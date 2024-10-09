```agda
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

module Reduction where

open import Data.Bool using (Bool; if_then_else_)
open Bool using (true; false)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

open import Type
open import Context
open import Process
open import Congruence

data _~>_ {Γ} : Process Γ -> Process Γ -> Set where
  r-link :
    ∀{Δ A B}
    {P : Process (B :: Δ)}
    (d : Dual A B) (e : Dual A B)
    (p : Γ ≃ B , Δ) ->
    Cut d p (Link e (split-l (split-r split-e))) P ~> #process (#cons p) P

  r-close :
    ∀{P : Process Γ}
    (p₀ : Γ ≃ [] + Γ) (q₀ : Γ ≃ [] + Γ) ->
    Cut dual-one-bot p₀ (Close (split-l split-e)) (Wait (split-l q₀) P) ~> P

  r-select-l :
    ∀{Γ₁ Γ₂ A A' B B'}
    {P : Process (A :: Γ₁)}
    {Q : Process (A' :: Γ₂)}
    {R : Process (B' :: Γ₂)}
    (d : Dual A A') (e : Dual B B')
    (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) ->
    Cut (dual-plus-with d e) p (Select true (split-l p₀) P)
                               (Case (split-l q₀) Q R) ~>
    Cut d p P Q

  r-select-r :
    ∀{Γ₁ Γ₂ A A' B B'}
    {P : Process (B :: Γ₁)}
    {Q : Process (A' :: Γ₂)}
    {R : Process (B' :: Γ₂)}
    (d : Dual A A') (e : Dual B B')
    (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) ->
    Cut (dual-plus-with d e) p (Select false (split-l p₀) P)
                               (Case (split-l q₀) Q R) ~>
    Cut e p P R

  r-fork :
    ∀{Γ₁ Γ₂ Γ₃ Δ A B A' B'}
    {P : Process (A :: Γ₁)}
    {Q : Process (B :: Γ₂)}
    {R : Process (B' :: A' :: Γ₃)}
    (d : Dual A A') (e : Dual B B')
    (p : Γ ≃ Δ + Γ₃) (p₀ : Γ₃ ≃ [] + Γ₃)
    (q : Δ ≃ Γ₁ + Γ₂) (q₀ : Δ ≃ [] + Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    Cut (dual-fork-join d e) p (Fork (split-l q₀) q P Q) (Join (split-l p₀) R) ~>
    Cut d q' P (Cut e (split-r p') Q R)

  r-cut :
    ∀{Γ₁ Γ₂ A B}
    {P Q : Process (A :: Γ₁)}
    {R : Process (B :: Γ₂)}
    (d : Dual A B)
    (q : Γ ≃ Γ₁ + Γ₂)
    (r : P ~> Q) ->
    Cut d q P R ~> Cut d q Q R

  r-cong :
    {P R Q : Process Γ}
    (p : P ⊒ R) (q : R ~> Q) -> P ~> Q

data _~>*_ {Γ} : Process Γ -> Process Γ -> Set where
  refl : ∀{P : Process Γ} -> P ~>* P
  tran : ∀{P Q R : Process Γ} -> P ~> Q -> Q ~>* R -> P ~>* R
```