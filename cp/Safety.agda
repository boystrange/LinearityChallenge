{-# OPTIONS --rewriting #-}
open import Data.List.Base using ([]; _∷_; [_])

open import Type
open import Context
open import Process
open import Congruence
open import DeadlockFreedom

data ReductionContext (Δ : Context) : Context → Set where
    hole  : ReductionContext Δ Δ
    cut-l : ∀{Γ Γ₁ Γ₂ A} (σ : Γ ≃ Γ₁ + Γ₂) → ReductionContext Δ (A ∷ Γ₁) → Proc (dual A ∷ Γ₂) → ReductionContext Δ Γ
    cut-r : ∀{Γ Γ₁ Γ₂ A} (σ : Γ ≃ Γ₁ + Γ₂) → Proc (A ∷ Γ₁) → ReductionContext Δ (dual A ∷ Γ₂) → ReductionContext Δ Γ

_⟦_⟧ : ∀{Γ Δ} → ReductionContext Δ Γ → Proc Δ → Proc Γ
hole        ⟦ P ⟧ = P
cut-l σ ∁ Q ⟦ P ⟧ = cut σ (∁ ⟦ P ⟧) Q
cut-r σ Q ∁ ⟦ P ⟧ = cut σ Q (∁ ⟦ P ⟧)

WellFormed : ∀{Γ} → Proc Γ → Set
WellFormed {Γ} P = ∀{Δ} {∁ : ReductionContext Δ Γ} {Q : Proc Δ} → 
    P ⊒ ((∁ ⟦ Q ⟧)) → Alive Q

type-safety : ∀{Γ} (P : Proc Γ) → WellFormed P
type-safety P {_} {_} {Q} _ = deadlock-freedom Q