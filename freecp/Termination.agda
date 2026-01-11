{-# OPTIONS --rewriting --guardedness #-}
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat using (ℕ; z≤n; s≤s; _≤_; _<_)
import Data.Nat.Properties as Nat
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ-syntax)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded

open import Process
open import Reduction
open import DeadlockFreedom

strong-termination : ∀{n Σ μ ν Γ Δ} (ℙ : Def Σ) {P : Proc {n} Σ μ Γ} {Q : Proc Σ ν Δ} →
                     ∃[ k ] ((reds : ℙ ⊢ P ↝* Q) → run-length ℙ reds ≤ k)
strong-termination {n} {Σ} {μ} ℙ = μ , aux
  where
    aux : ∀{μ ν Γ Δ} {P : Proc {n} Σ μ Γ} {Q : Proc Σ ν Δ} (reds : ℙ ⊢ P ↝* Q) -> run-length ℙ reds ≤ μ
    aux refl = z≤n
    aux (trans red reds) = Nat.≤-trans (s≤s (aux reds)) (↝size red)

measure : ∀{n Σ μ Γ} (P : Proc {n} Σ μ Γ) → ℕ
measure {μ = μ} _ = μ

normalize : ∀{n Σ μ Γ} (ℙ : Def Σ) (P : Proc {n} Σ μ Γ) ->
            ∃[ ν ] ∃[ Δ ] Σ[ Q ∈ Proc Σ ν Δ ] (ℙ ⊢ P ↝* Q × Observable Q)
normalize {n} {Σ} ℙ P = aux P (<-wellFounded (measure P))
  where
    aux : ∀{μ Γ} (P : Proc {n} Σ μ Γ) -> Acc _<_ (measure P) ->
          ∃[ ν ] ∃[ Δ ] Σ[ Q ∈ Proc Σ ν Δ ] ℙ ⊢ P ↝* Q × Observable Q
    aux P (acc rs) with deadlock-freedom ℙ P
    ... | inj₁ (Δ , obs) = _ , _ , _ , refl , Δ , obs
    ... | inj₂ (_ , _ , R , red) with aux R (rs (↝size red))
    ... | _ , _ , Q , reds , obs = _ , _ , Q , trans red reds , obs
