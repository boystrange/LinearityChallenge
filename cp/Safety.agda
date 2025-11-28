{-# OPTIONS --rewriting #-}
open import Data.List.Base using ([]; _∷_; [_])

open import Type
open import Context
open import Process
open import Congruence
open import DeadlockFreedom

data ReductionContext (Δ : Context) : Context → Set where
  hole   : ReductionContext Δ Δ
  cut-l  : ∀{Γ Γ₁ Γ₂ A} (p : Γ ≃ Γ₁ + Γ₂) →
           ReductionContext Δ (A ∷ Γ₁) → Process (dual A ∷ Γ₂) →
           ReductionContext Δ Γ
  cut-r  : ∀{Γ Γ₁ Γ₂ A} (p : Γ ≃ Γ₁ + Γ₂) →
           Process (A ∷ Γ₁) → ReductionContext Δ (dual A ∷ Γ₂) →
           ReductionContext Δ Γ

_⟦_⟧ : ∀{Γ Δ} → ReductionContext Δ Γ → Process Δ → Process Γ
hole ⟦ P ⟧           = P
cut-l p 𝒞 Q ⟦ P ⟧  = cut p (𝒞 ⟦ P ⟧) Q
cut-r p Q 𝒞 ⟦ P ⟧  = cut p Q (𝒞 ⟦ P ⟧)

WellFormed       : ∀{Γ} → Process Γ → Set
WellFormed {Γ} P = ∀{Δ} {𝒞 : ReductionContext Δ Γ} {Q : Process Δ} →
                   P ⊒ (𝒞 ⟦ Q ⟧) → Alive Q

type-safety : ∀{Γ} (P : Process Γ) → WellFormed P
type-safety P {_} {_} {Q} _ = deadlock-freedom Q
