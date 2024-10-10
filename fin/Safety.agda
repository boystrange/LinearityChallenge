open import Data.Sum
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Nullary using (contradiction)

open import Type
open import Context
open import Process
open import Kind
open import Congruence

data ActionCut {Γ} : Process Γ -> Set where
  is-action-cut :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)} ->
    Action P -> Action Q -> ActionCut (Cut d p P Q)

data SafeCut {Γ} : Process Γ -> Set where
  is-action-cut :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)} ->
    Output P -> Input Q -> SafeCut (Cut d p P Q)

safety : ∀{Γ} {P : Process Γ} -> ActionCut P -> ∃[ Q ] P ⊒ Q × SafeCut Q
safety (is-action-cut d p (inj₁ x) (inj₁ y)) = contradiction (x , y) (input-input d)
safety (is-action-cut d p (inj₁ x) (inj₂ y)) = _ , s-comm d (dual-symm d) p (+-comm p) , is-action-cut (dual-symm d) (+-comm p) y x
safety (is-action-cut d p (inj₂ x) (inj₁ y)) = _ , s-refl , is-action-cut d p x y
safety (is-action-cut d p (inj₂ x) (inj₂ y)) = contradiction (x , y) (output-output d)
