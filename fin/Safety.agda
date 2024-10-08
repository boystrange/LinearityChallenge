-- MIT License

-- Copyright (c) 2024 Luca Padovani & Claudia Raffaelli

-- Permission is hereby granted, free of charge, to any person
-- obtaining a copy of this software and associated documentation
-- files (the "Software"), to deal in the Software without
-- restriction, including without limitation the rights to use,
-- copy, modify, merge, publish, distribute, sublicense, and/or sell
-- copies of the Software, and to permit persons to whom the
-- Software is furnished to do so, subject to the following
-- conditions:

-- The above copyright notice and this permission notice shall be
-- included in all copies or substantial portions of the Software.

-- THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
-- EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
-- OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
-- NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
-- HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
-- WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
-- FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
-- OTHER DEALINGS IN THE SOFTWARE.

module Safety where

open import Data.Sum
open import Data.Product using (_×_; Σ; _,_; ∃; Σ-syntax; ∃-syntax)

open import Relation.Nullary using (¬_; contradiction)

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
