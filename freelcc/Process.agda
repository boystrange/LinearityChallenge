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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)

open import Type
open import Equivalence
open import Context
open import Permutations

record ProcType : Set where
  field
    {n} : ℕ
    context : Context

open ProcType public

ProcContext : Set
ProcContext = List ProcType

data _∈_ (T : ProcType) : ProcContext → Set where
  here : ∀{Σ} → T ∈ (T ∷ Σ)
  next : ∀{S Σ} → T ∈ Σ → T ∈ (S ∷ Σ)

data Ch (A : Type) : Context → Set where
  ch : Ch A [ A ]

data Proc (Σ : ProcContext) : Context → Set where
  call     : ∀{T} → T ∈ Σ → ∀[ T .context ↭_ ⇒ Proc Σ ]
  link     : ∀{A B} → dual A ≅ B → ∀[ Ch A ∗ Ch B ⇒ Proc Σ ]
  fail     : ∀[ Ch ⊤ ∗ U ⇒ Proc Σ ]
  wait     : ∀[ Ch ⊥ ∗ Proc Σ ⇒ Proc Σ ]
  close    : ∀[ Ch 𝟙 ⇒ Proc Σ ]
  case     : ∀{A B} → ∀[ Ch (A & B) ∗ ((A ∷_) ⊢ Proc Σ ∩ (B ∷_) ⊢ Proc Σ) ⇒ Proc Σ ]
  select   : ∀{A B} → ∀[ Ch (A ⊕ B) ∗ ((A ∷_) ⊢ Proc Σ ∪ (B ∷_) ⊢ Proc Σ) ⇒ Proc Σ ]
  join     : ∀{A B} → ∀[ Ch (A ⅋ B) ∗ ((B ∷_) ⊢ (A ∷_) ⊢ Proc Σ) ⇒ Proc Σ ]
  fork     : ∀{A B} → ∀[ Ch (A ⊗ B) ∗ ((A ∷_) ⊢ Proc Σ) ∗ ((B ∷_) ⊢ Proc Σ) ⇒ Proc Σ ]
  cut      : ∀{A B} → dual A ≅ B → ∀[ ((A ∷_) ⊢ Proc Σ) ∗ ((B ∷_) ⊢ Proc Σ) ⇒ Proc Σ ]

data PreDef (Σ : ProcContext) : ProcContext → Set where
  []  : PreDef Σ []
  _∷_ : ∀{T Σ'} → Proc Σ (T .context) → PreDef Σ Σ' → PreDef Σ (T ∷ Σ')

Def : ProcContext → Set
Def Σ = PreDef Σ Σ

lookup : ∀{Σ Σ' T} → PreDef Σ Σ' → T ∈ Σ' → Proc Σ (T .context)
lookup (P ∷ def) here = P
lookup (_ ∷ def) (next x) = lookup def x

↭proc : ∀{Γ Δ Σ} → Γ ↭ Δ → Proc Σ Γ → Proc Σ Δ
↭proc π (call σ π') = call σ (trans π' π)
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

-- Ext : ∀{Γ Σ Σ'} → (∀{Δ} → Δ ∈ Σ → Δ ∈ Σ') →
--       ∀{Δ} → Δ ∈ (Γ ∷ Σ) → Δ ∈ (Γ ∷ Σ')
-- Ext ρ here = here
-- Ext ρ (next x) = next (ρ x)

-- Rename : ∀{Γ Σ Σ'} → (∀{Δ} → Δ ∈ Σ → Δ ∈ Σ') → Proc Σ Γ → Proc Σ' Γ
-- Rename ρ (call σ x π) = call σ (ρ x) π
-- Rename ρ (rec σ P π) = rec σ (Rename (Ext ρ) P) π
-- Rename ρ (link eq x) = link eq x
-- Rename ρ (fail x) = fail x
-- Rename ρ (wait (ch ⟨ σ ⟩ P)) = wait (ch ⟨ σ ⟩ Rename ρ P)
-- Rename ρ (close ch) = close ch
-- Rename ρ (case (ch ⟨ p ⟩ (P , Q))) = case (ch ⟨ p ⟩ (Rename ρ P , Rename ρ Q))
-- Rename ρ (select (ch ⟨ p ⟩ inj₁ P)) = select (ch ⟨ p ⟩ inj₁ (Rename ρ P))
-- Rename ρ (select (ch ⟨ p ⟩ inj₂ P)) = select (ch ⟨ p ⟩ inj₂ (Rename ρ P))
-- Rename ρ (join (ch ⟨ p ⟩ P)) = join (ch ⟨ p ⟩ Rename ρ P)
-- Rename ρ (fork (ch ⟨ p ⟩ (P ⟨ q ⟩ Q))) = fork (ch ⟨ p ⟩ (Rename ρ P ⟨ q ⟩ Rename ρ Q))
-- Rename ρ (cut eq (P ⟨ σ ⟩ Q)) = cut eq (Rename ρ P ⟨ σ ⟩ Rename ρ Q)

-- Exts : ∀{Γ Σ Σ'} → (∀{Δ} → Δ ∈ Σ → Proc Σ' Δ) →
--        ∀{Δ} → Δ ∈ (Γ ∷ Σ) → Proc (Γ ∷ Σ') Δ
-- Exts {_} {Γ} σ here = call var here {!!}
-- Exts σ (next x) = Rename next (σ x)

-- Subst : ∀{Γ Σ Σ'} → (∀{Δ} → Δ ∈ Σ → Proc Σ' Δ) → Proc Σ Γ → Proc Σ' Γ
-- Subst σ (call τ x π) = ↭proc π (σ x)
-- Subst σ (rec τ P π) = rec τ (Subst (Exts σ) P) π
-- Subst σ (link eq x) = link eq x
-- Subst σ (fail x) = fail x
-- Subst σ (wait (ch ⟨ p ⟩ P)) = wait (ch ⟨ p ⟩ Subst σ P)
-- Subst σ (close ch) = close ch
-- Subst σ (case (ch ⟨ p ⟩ (P , Q))) = case (ch ⟨ p ⟩ (Subst σ P , Subst σ Q))
-- Subst σ (select (ch ⟨ p ⟩ inj₁ P)) = select (ch ⟨ p ⟩ inj₁ (Subst σ P))
-- Subst σ (select (ch ⟨ p ⟩ inj₂ P)) = select (ch ⟨ p ⟩ inj₂ (Subst σ P))
-- Subst σ (join (ch ⟨ p ⟩ P)) = join (ch ⟨ p ⟩ Subst σ P)
-- Subst σ (fork (ch ⟨ p ⟩ (P ⟨ q ⟩ Q))) = fork (ch ⟨ p ⟩ (Subst σ P ⟨ q ⟩ Subst σ Q))
-- Subst σ (cut eq (P ⟨ p ⟩ Q)) = cut eq (Subst σ P ⟨ p ⟩ Subst σ Q)

-- Sing : ∀{Γ Σ} → Proc Σ Γ → ∀{Δ} → Δ ∈ (Γ ∷ Σ) → Proc Σ Δ
-- Sing P here = P
-- Sing P (next x) = call x refl

-- Unfold : ∀{Δ Σ} → Proc (Δ ∷ Σ) Δ → Proc Σ Δ
-- Unfold P = Subst (Sing (rec P refl)) P

-- Proc : Context → Set
-- Proc = Proc []
