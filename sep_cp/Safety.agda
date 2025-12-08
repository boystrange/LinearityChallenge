{-# OPTIONS --rewriting #-}
open import Data.List.Base using ([]; _∷_; [_])
open import Relation.Unary

open import Type
open import Context
open import Process
open import Congruence
open import DeadlockFreedom

data ReductionContext (Δ : Context) : Context → Set where
  hole   : ReductionContext Δ Δ
  cut-l  : ∀{A} → ∀[ ((A ∷_) ⊢ ReductionContext Δ) ∗ ((dual A ∷_) ⊢ Proc) ⇒ ReductionContext Δ ]
  cut-r  : ∀{A} → ∀[ ((A ∷_) ⊢ Proc) ∗ ((dual A ∷_) ⊢ ReductionContext Δ) ⇒ ReductionContext Δ ]

_⟦_⟧ : ∀{Γ Δ} → ReductionContext Δ Γ → Proc Δ → Proc Γ
hole               ⟦ P ⟧ = P
cut-l (𝒞 ⟨ p ⟩ Q)  ⟦ P ⟧ = cut ((𝒞 ⟦ P ⟧) ⟨ p ⟩ Q)
cut-r (Q ⟨ p ⟩ 𝒞)  ⟦ P ⟧ = cut (Q ⟨ p ⟩ (𝒞 ⟦ P ⟧))

WellFormed : ∀{Γ} → Proc Γ → Set
WellFormed {Γ} P = ∀{Δ} {𝒞 : ReductionContext Δ Γ} {Q : Proc Δ} →
                   P ⊒ (𝒞 ⟦ Q ⟧) → Alive Q

type-safety : ∀{Γ} (P : Proc Γ) → WellFormed P
type-safety P {_} {_} {Q} _ = deadlock-freedom Q
