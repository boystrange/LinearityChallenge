{-# OPTIONS --rewriting --guardedness #-}
open import Function using (id; _∘_)
open import Data.Unit using (tt)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Sum
open import Data.Product using (Σ; _,_)
open import Data.List.Base using (List; []; _∷_; [_]; map)
open import Data.Vec using (Vec)
open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂)

open import Type
open import Equivalence
open import Context
open import Permutations

record ProcType : Set where
  field
    {n} : ℕ
    context : Context n

open ProcType public

ProcContext : Set
ProcContext = List ProcType

data _∈_ (T : ProcType) : ProcContext → Set where
  here : ∀{Σ} → T ∈ (T ∷ Σ)
  next : ∀{S Σ} → T ∈ Σ → T ∈ (S ∷ Σ)

data Ch {n} (A : Type n) : Context n → Set where
  ch : Ch A [ A ]

data Proc {n} (Σ : ProcContext) : Context n → Set where
  call     : ∀{T} → T ∈ Σ → (σ : ∀{s} → Fin (T .ProcType.n) → PreType n s) →
             ∀[ substc σ (T .context) ↭_ ⇒ Proc Σ ]
  link     : ∀{A B} → dual A ≈ B → ∀[ Ch A ∗ Ch B ⇒ Proc Σ ]
  fail     : ∀[ Ch ⊤ ∗ U ⇒ Proc Σ ]
  wait     : ∀[ Ch ⊥ ∗ Proc Σ ⇒ Proc Σ ]
  close    : ∀[ Ch 𝟙 ⇒ Proc Σ ]
  case     : ∀{A B} → ∀[ Ch (A & B) ∗ ((A ∷_) ⊢ Proc Σ ∩ (B ∷_) ⊢ Proc Σ) ⇒ Proc Σ ]
  select   : ∀{A B} → ∀[ Ch (A ⊕ B) ∗ ((A ∷_) ⊢ Proc Σ ∪ (B ∷_) ⊢ Proc Σ) ⇒ Proc Σ ]
  join     : ∀{A B} → ∀[ Ch (A ⅋ B) ∗ ((B ∷_) ⊢ (A ∷_) ⊢ Proc Σ) ⇒ Proc Σ ]
  fork     : ∀{A B} → ∀[ Ch (A ⊗ B) ∗ ((A ∷_) ⊢ Proc Σ) ∗ ((B ∷_) ⊢ Proc Σ) ⇒ Proc Σ ]
  cut      : ∀{A B} → dual A ≈ B → ∀[ ((A ∷_) ⊢ Proc Σ) ∗ ((B ∷_) ⊢ Proc Σ) ⇒ Proc Σ ]

data PreDef (Σ : ProcContext) : ProcContext → Set where
  []  : PreDef Σ []
  _∷_ : ∀{T Σ'} → Proc Σ (T .context) → PreDef Σ Σ' → PreDef Σ (T ∷ Σ')

Def : ProcContext → Set
Def Σ = PreDef Σ Σ

lookup : ∀{Σ Σ' T} → PreDef Σ Σ' → T ∈ Σ' → Proc Σ (T .context)
lookup (P ∷ def) here = P
lookup (_ ∷ def) (next x) = lookup def x

↭proc : ∀{n} {Γ Δ : Context n} {Σ} → Γ ↭ Δ → Proc Σ Γ → Proc Σ Δ
↭proc π (call x σ π') = call x σ (trans π' π)
↭proc π (link eq (ch ⟨ p ⟩ ch)) with ↭solo π p
... | _ , q , π' rewrite ↭solo-inv π' = link eq (ch ⟨ q ⟩ ch)
↭proc π (fail (ch ⟨ p ⟩ tt)) with ↭solo π p
... | _ , q , π' = fail (ch ⟨ q ⟩ tt)
↭proc π (wait (ch ⟨ p ⟩ P)) with ↭solo π p
... | _ , q , π' = wait (ch ⟨ q ⟩ ↭proc π' P)
↭proc π (close ch) rewrite ↭solo-inv π = close ch
↭proc π (case (ch ⟨ p ⟩ (P , Q))) with ↭solo π p
... | _ , q , π' = case (ch ⟨ q ⟩ (↭proc (prep π') P , ↭proc (prep π') Q))
↭proc π (select (ch ⟨ p ⟩ inj₁ P)) with ↭solo π p
... | _ , q , π' = select (ch ⟨ q ⟩ inj₁ (↭proc (prep π') P))
↭proc π (select (ch ⟨ p ⟩ inj₂ P)) with ↭solo π p
... | _ , q , π' = select (ch ⟨ q ⟩ inj₂ (↭proc (prep π') P))
↭proc π (join (ch ⟨ p ⟩ P)) with ↭solo π p
... | _ , q , π' = join (ch ⟨ q ⟩ ↭proc (prep (prep π')) P)
↭proc π (fork (ch ⟨ p ⟩ (P ⟨ q ⟩ Q))) with ↭solo π p
... | _ , p' , π' with ↭split π' q
... | Δ₁ , Δ₂ , q' , π₁ , π₂ = fork (ch ⟨ p' ⟩ (↭proc (prep π₁) P ⟨ q' ⟩ ↭proc (prep π₂) Q))
↭proc π (cut eq (P ⟨ p ⟩ Q)) with ↭split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = cut eq (↭proc (prep π₁) P ⟨ q ⟩ ↭proc (prep π₂) Q)

substp : ∀{n m Σ} {Γ : Context n} (σ : ∀{s} → Fin n → PreType m s) → Proc Σ Γ → Proc Σ (substc σ Γ)
substp σ (call {T} x σ' π) with ↭subst σ π
... | π' rewrite substc-compose σ' σ (T .context) = call x (Type.subst σ ∘ σ') π'
substp σ (link {A} eq (ch ⟨ p ⟩ ch)) with ≈subst σ eq
... | eq' rewrite Eq.sym (dual-subst σ A) = link eq' (ch ⟨ +-subst σ p ⟩ ch)
substp σ (fail (ch ⟨ p ⟩ tt)) = fail (ch ⟨ +-subst σ p ⟩ tt)
substp σ (wait (ch ⟨ p ⟩ P)) = wait (ch ⟨ +-subst σ p ⟩ substp σ P)
substp σ (close ch) = close ch
substp σ (case (ch ⟨ p ⟩ (P , Q))) = case (ch ⟨ +-subst σ p ⟩ (substp σ P , substp σ Q))
substp σ (select (ch ⟨ p ⟩ inj₁ P)) = select (ch ⟨ +-subst σ p ⟩ inj₁ (substp σ P))
substp σ (select (ch ⟨ p ⟩ inj₂ Q)) = select (ch ⟨ +-subst σ p ⟩ inj₂ (substp σ Q))
substp σ (join (ch ⟨ p ⟩ P)) = join (ch ⟨ +-subst σ p ⟩ substp σ P)
substp σ (fork (ch ⟨ p ⟩ (P ⟨ q ⟩ Q))) = fork (ch ⟨ +-subst σ p ⟩ (substp σ P ⟨ +-subst σ q ⟩ substp σ Q))
substp σ (cut {A} eq (P ⟨ p ⟩ Q)) with ≈subst σ eq
... | eq' rewrite Eq.sym (dual-subst σ A) = cut eq' (substp σ P ⟨ +-subst σ p ⟩ substp σ Q)
