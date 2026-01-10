{-# OPTIONS --rewriting --guardedness #-}
open import Data.Nat using (ℕ; z≤n; s≤s; _≤_)
import Data.Nat.Properties as Nat
open import Data.Product using (_,_; ∃; ∃-syntax)

open import Process
open import Reduction

strong-termination : ∀{n Σ μ ν Γ Δ} (ℙ : Def Σ) {P : Proc {n} Σ μ Γ} {Q : Proc Σ ν Δ} →
                     ∃[ k ] ((reds : ℙ ⊢ P ↝* Q) → run-length ℙ reds ≤ k)
strong-termination {n} {Σ} {μ} ℙ = μ , aux
  where
    aux : ∀{μ ν Γ Δ} {P : Proc {n} Σ μ Γ} {Q : Proc Σ ν Δ} (reds : ℙ ⊢ P ↝* Q) -> run-length ℙ reds ≤ μ
    aux refl = z≤n
    aux (trans red reds) = Nat.≤-trans (s≤s (aux reds)) (↝size red)
