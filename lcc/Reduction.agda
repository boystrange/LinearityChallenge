{-# OPTIONS --rewriting #-}
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.List.Base using ([]; _∷_; [_]; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (sym)

open import Type
open import Context
open import Permutations
open import Process
open import Congruence

weakening : ∀[ Un ∗ Proc ⇒ Proc ]
weakening (un ⟨ p ⟩ P) = ↭proc (↭concat p) (aux un P)
  where
    aux : ∀{Γ₁ Γ₂} (un : Un Γ₁) → Proc Γ₂ → Proc (Γ₁ ++ Γ₂)
    aux un-[] P = P
    aux (un-∷ un) P = weaken (ch ⟨ < ≫ ⟩ aux un P)

contraction : ∀{Γ Γ₁ Γ₂} (un : Un Γ₁) → Γ ≃ Γ₁ + Γ₂ → Proc (Γ₁ ++ Γ) → Proc Γ
contraction un p P = ↭proc (↭concat p) (aux un (↭proc (↭left (↭sym (↭concat p))) P))
  where
    aux : ∀{Γ₁ Γ₂} → Un Γ₁ → Proc (Γ₁ ++ Γ₁ ++ Γ₂) → Proc (Γ₁ ++ Γ₂)
    aux un-[] P = P
    aux {`? A ∷ Γ₁} {Γ₂} (un-∷ un) P with contract (ch ⟨ < ≫ ⟩ (↭proc (↭shift {`? A} {`? A ∷ Γ₁} {Γ₁ ++ Γ₂}) P))
    ... | P₁ rewrite sym (++-assoc (`? A ∷ Γ₁) Γ₁ Γ₂) with ↭proc (↭sym (↭shift {`? A} {Γ₁ ++ Γ₁})) P₁
    ... | P₂ rewrite ++-assoc Γ₁ Γ₁ (`? A ∷ Γ₂) with aux un P₂
    ... | P₃ = ↭proc ↭shift P₃

data _↝_ {Γ} : Proc Γ → Proc Γ → Set where
  r-link      : ∀{Δ A P} (p : Γ ≃ [ dual A ] + Δ) →
                cut {A} (link (ch ⟨ < > • ⟩ ch) ⟨ p ⟩ P) ↝ ↭proc (↭concat p) P
  r-close     : ∀{P} (p₀ q₀ : Γ ≃ [] + Γ) →
                cut (close ch ⟨ p₀ ⟩ wait (ch ⟨ < q₀ ⟩ P)) ↝ P
  r-select-l  : ∀{Γ₁ Γ₂ A B P Q R}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                cut {A ⊕ B} (select (ch ⟨ < p₀ ⟩ inj₁ P) ⟨ p ⟩
                             case (ch ⟨ < q₀ ⟩ (Q , R))) ↝ cut (P ⟨ p ⟩ Q)
  r-select-r  : ∀{Γ₁ Γ₂ A B P Q R}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                cut {A ⊕ B} (select (ch ⟨ < p₀ ⟩ inj₂ P) ⟨ p ⟩
                             case (ch ⟨ < q₀ ⟩ (Q , R))) ↝ cut (P ⟨ p ⟩ R)
  r-fork      : ∀{Γ₁ Γ₂ Γ₃ Δ A B P Q R}
                (p : Γ ≃ Δ + Γ₃) (p₀ : Γ₃ ≃ [] + Γ₃) (q : Δ ≃ Γ₁ + Γ₂) (q₀ : Δ ≃ [] + Δ) →
                let _ , p′ , q′ = +-assoc-l p q in
                cut {A ⊗ B} (fork (ch ⟨ < q₀ ⟩ (P ⟨ q ⟩ Q)) ⟨ p ⟩
                             join (ch ⟨ < p₀ ⟩ R)) ↝ cut (P ⟨ q′ ⟩ cut (Q ⟨ > p′ ⟩ R))
  r-client    : ∀{Γ₁ Γ₂ A P Q}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) (un : Un Γ₂) →
                cut {`? A} (client (ch ⟨ < p₀ ⟩ P) ⟨ p ⟩ server (ch ⟨ < q₀ ⟩ (un , Q))) ↝
                cut (P ⟨ p ⟩ Q)
  r-weaken    : ∀{Γ₁ Γ₂ A P Q}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) (un : Un Γ₂) →
                cut {`? A} (weaken (ch ⟨ < p₀ ⟩ P) ⟨ p ⟩ server (ch ⟨ < q₀ ⟩ (un , Q))) ↝
                weakening (un ⟨ +-comm p ⟩ P)
  r-contract  : ∀{Γ₁ Γ₂ A P Q}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) (un : Un Γ₂) →
                cut {`? A} (contract (ch ⟨ < p₀ ⟩ P) ⟨ p ⟩ server (ch ⟨ < q₀ ⟩ (un , Q))) ↝
                contraction un (+-comm p) (cut (server (ch ⟨ < q₀ ⟩ (un , Q)) ⟨ ++≃+ ⟩
                                           cut (server (ch ⟨ < q₀ ⟩ (un , Q)) ⟨ > +-comm p ⟩ P)))
  r-exists     : ∀{A B Γ₁ Γ₂ P F} (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                 cut {`∃ A} (ex {A} {B} (ch ⟨ < p₀ ⟩ P) ⟨ p ⟩ all (ch ⟨ < q₀ ⟩ F)) ↝
                 cut (P ⟨ p ⟩ F B)
  r-cut        : ∀{Γ₁ Γ₂ A P Q R} (q : Γ ≃ Γ₁ + Γ₂) →
                 P ↝ Q → cut {A} (P ⟨ q ⟩ R) ↝ cut (Q ⟨ q ⟩ R)
  r-cong       : ∀{P R Q} → P ⊒ R → R ↝ Q → P ↝ Q
