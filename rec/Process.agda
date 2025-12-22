{-# OPTIONS --rewriting #-}
open import Data.Unit using (tt)
open import Data.Sum
open import Data.Fin using (Fin)
open import Data.Nat
open import Data.Product using (_,_)
open import Data.List.Base using (List; []; _∷_; [_])
open import Relation.Unary hiding (_∈_)

open import Type
open import Context
open import Permutations

ProcContext : ℕ → Set
ProcContext n = Fin n → Context

data Ch (A : Type) : Context → Set where
  ch : Ch A [ A ]

data Proc {n} (Σ : ProcContext n) : Context → Set where
  call     : ∀{i} → ∀[ Σ i ↭_ ⇒ Proc Σ ]
  link     : ∀{A} → ∀[ Ch A ∗ Ch (dual A) ⇒ Proc Σ ]
  fail     : ∀[ Ch ⊤ ∗ U ⇒ Proc Σ ]
  wait     : ∀[ Ch ⊥ ∗ Proc Σ ⇒ Proc Σ ]
  close    : ∀[ Ch 𝟙 ⇒ Proc Σ ]
  case     : ∀{A B} → ∀[ Ch (A & B) ∗ ((A ∷_) ⊢ Proc Σ ∩ (B ∷_) ⊢ Proc Σ) ⇒ Proc Σ ]
  select   : ∀{A B} → ∀[ Ch (A ⊕ B) ∗ ((A ∷_) ⊢ Proc Σ ∪ (B ∷_) ⊢ Proc Σ) ⇒ Proc Σ ]
  join     : ∀{A B} → ∀[ Ch (A ⅋ B) ∗ ((A ∷_) ⊢ (B ∷_) ⊢ Proc Σ) ⇒ Proc Σ ]
  fork     : ∀{A B} → ∀[ Ch (A ⊗ B) ∗ ((A ∷_) ⊢ Proc Σ) ∗ ((B ∷_) ⊢ Proc Σ) ⇒ Proc Σ ]
  all      : ∀{A} → ∀[ Ch (`∀ A) ∗ ⋂[ X ∶ Type ] ((subst [ X /] A ∷_) ⊢ Proc Σ) ⇒ Proc Σ ]
  ex       : ∀{A B} → ∀[ Ch (`∃ A) ∗ ((subst [ B /] A ∷_) ⊢ Proc Σ) ⇒ Proc Σ ]
  server   : ∀{A} → ∀[ Ch (`! A) ∗ (Un ∩ ((A ∷_) ⊢ Proc Σ)) ⇒ Proc Σ ]
  client   : ∀{A} → ∀[ Ch (`? A) ∗ ((A ∷_) ⊢ Proc Σ) ⇒ Proc Σ ]
  weaken   : ∀{A} → ∀[ Ch (`? A) ∗ Proc Σ ⇒ Proc Σ ]
  contract : ∀{A} → ∀[ Ch (`? A) ∗ ((`? A ∷_) ⊢ (`? A ∷_) ⊢ Proc Σ) ⇒ Proc Σ ]
  cut      : ∀{A} → ∀[ ((A ∷_) ⊢ Proc Σ) ∗ ((dual A ∷_) ⊢ Proc Σ) ⇒ Proc Σ ]

ProcEnv : ∀{n} → ProcContext n → Set
ProcEnv {n} Σ = (i : Fin n) → Proc {n} Σ (Σ i)

↭proc : ∀{n Γ Δ} {Σ : ProcContext n} → Γ ↭ Δ → Proc Σ Γ → Proc Σ Δ
↭proc π (call π') = call (trans π' π)
↭proc π (link (ch ⟨ p ⟩ ch)) with ↭solo π p
... | _ , q , π' rewrite ↭solo-inv π' = link (ch ⟨ q ⟩ ch)
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
↭proc π (all (ch ⟨ p ⟩ F)) with ↭solo π p
... | _ , q , π' = all (ch ⟨ q ⟩ λ X → ↭proc (prep π') (F X))
↭proc π (ex (ch ⟨ p ⟩ P)) with ↭solo π p
... | _ , q , π' = ex (ch ⟨ q ⟩ ↭proc (prep π') P)
↭proc π (server (ch ⟨ p ⟩ (un , P))) with ↭solo π p
... | _ , q , π' = server (ch ⟨ q ⟩ (↭un π' un , ↭proc (prep π') P))
↭proc π (client (ch ⟨ p ⟩ P)) with ↭solo π p
... | _ , q , π' = client (ch ⟨ q ⟩ ↭proc (prep π') P)
↭proc π (weaken (ch ⟨ p ⟩ P)) with ↭solo π p
... | _ , q , π' = weaken (ch ⟨ q ⟩ ↭proc π' P)
↭proc π (contract (ch ⟨ p ⟩ P)) with ↭solo π p
... | _ , q , π' = contract (ch ⟨ q ⟩ ↭proc (prep (prep π')) P)
↭proc π (cut (P ⟨ p ⟩ Q)) with ↭split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = cut (↭proc (prep π₁) P ⟨ q ⟩ ↭proc (prep π₂) Q)
