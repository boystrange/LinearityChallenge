{-# OPTIONS --rewriting --guardedness #-}
open import Function using (id; _∘_)
open import Data.Unit using (tt)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; z≤n; s≤s; _+_; _≤_)
import Data.Nat.Properties as Nat
open import Data.Sum
open import Data.Product using (Σ; _,_; ∃; ∃-syntax)
open import Data.List.Base using (List; []; _∷_; [_]; map)
open import Data.Vec using (Vec)
open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂)

open import Process
open import Reduction

strong-termination : ∀{n Σ μ ν Γ Δ} (ℙ : Def Σ) {P : Proc {n} Σ μ Γ} {Q : Proc Σ ν Δ} →
                     ∃[ k ] ((reds : ℙ ⊢ P ↝* Q) → run-length ℙ reds ≤ k)
strong-termination {n} {Σ} {μ} ℙ = μ , aux
  where
    aux : ∀{μ ν Γ Δ} {P : Proc {n} Σ μ Γ} {Q : Proc Σ ν Δ} (reds : ℙ ⊢ P ↝* Q) -> run-length ℙ reds ≤ μ
    aux refl = z≤n
    aux (trans red reds) = Nat.≤-trans (s≤s (aux reds)) (↝size red)
