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

module Congruence where

open import Data.Bool using (Bool; if_then_else_)
open Bool using (true; false)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

open import Type
open import Context
open import Process

data _⊒_ : ∀{Γ} -> Process Γ -> Process Γ -> Set where
  s-comm :
    ∀{Γ Γ₁ Γ₂ A B P Q} (d : Dual A B) (d' : Dual B A)
    (p : Γ ≃ Γ₁ + Γ₂) (p' : Γ ≃ Γ₂ + Γ₁) ->
    Cut d p P Q ⊒ Cut d' p' Q P

  s-assoc-r :
    ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A A' B B'}
    {P : Process (A :: Γ₁)}
    {Q : Process (B :: A' :: Δ₁)}
    {R : Process (B' :: Δ₂)}
    (d : Dual A A') (e : Dual B B')
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₂ ≃ Δ₁ + Δ₂)
    (p' : Δ ≃ Γ₁ + Δ₁) (q' : Γ ≃ Δ + Δ₂) ->
    Cut d p P (Cut e (split-l q) Q R) ⊒
    Cut e q' (Cut d (split-r p') P (#process #here Q)) R

  s-link :
    ∀{Γ A B}
    (d : Dual A B) (p : Γ ≃ [ A ] + [ B ]) ->
    Link d p ⊒ Link (dual-symm d) (+-comm p)

  s-fail :
    ∀{Γ Γ₁ Γ₂ Δ A B P} (d : Dual A B)
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ Top ] + Δ) ->
    let _ , _ , q' = +-assoc-l p q in
    Cut d p (Fail (split-r q)) P ⊒ Fail q'

  s-wait :
    ∀{Γ Γ₁ Γ₂ Δ A B}
    {P : Process (A :: Δ)} {Q : Process (B :: Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ Bot ] + Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    Cut d p (Wait (split-r q) P) Q ⊒ Wait q' (Cut d p' P Q)

  s-select-l :
    ∀{Γ Γ₁ Γ₂ Δ A B C D}
    {P : Process (C :: A :: Δ)}
    {Q : Process (B :: Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ C ⊕ D ] + Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    Cut d p (Select true (split-r q) P) Q ⊒ Select true q' (Cut d (split-l p') (#process #here P) Q)

  s-select-r :
    ∀{Γ Γ₁ Γ₂ Δ A B C D}
    {P : Process (D :: A :: Δ)}
    {Q : Process (B :: Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ C ⊕ D ] + Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    Cut d p (Select false (split-r q) P) Q ⊒ Select false q' (Cut d (split-l p') (#process #here P) Q)

  s-case :
    ∀{Γ A B A₁ A₂ Γ₁ Γ₂ Δ}
    {P : Process (A₁ :: A :: Δ)}
    {Q : Process (A₂ :: A :: Δ)}
    {R : Process (B :: Γ₂)}
    (d : Dual A B)
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ A₁ & A₂ ] + Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    Cut d p (Case (split-r q) P Q) R ⊒
    Case q' (Cut d (split-l p') (#process #here P) R)
            (Cut d (split-l p') (#process #here Q) R)

  s-fork-l :
    ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A B C D}
    {P : Process (C :: A :: Δ₁)}
    {Q : Process (D :: Δ₂)}
    {R : Process (B :: Γ₂)}
    (d : Dual A B)
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ C ⊗ D ] + Δ) (r : Δ ≃ Δ₁ + Δ₂) ->
    let _ , p' , q' = +-assoc-l p q in
    let _ , p'' , r' = +-assoc-l p' r in
    let _ , q'' , r'' = +-assoc-r r' (+-comm p'') in
    Cut d p (Fork (split-r q) (split-l r) P Q) R ⊒
    Fork q' r'' (Cut d (split-l q'') (#process #here P) R) Q

  s-fork-r :
    ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A B C D}
    {P : Process (C :: Δ₁)}
    {Q : Process (D :: A :: Δ₂)}
    {R : Process (B :: Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ C ⊗ D ] + Δ)
    (r : Δ ≃ Δ₁ + Δ₂) ->
    let _ , p' , q' = +-assoc-l p q in
    let _ , p'' , r' = +-assoc-l p' r in
    Cut d p (Fork (split-r q) (split-r r) P Q) R ⊒
    Fork q' r' P (Cut d (split-l p'') (#process #here Q) R)

  s-join :
    ∀{Γ Γ₁ Γ₂ Δ A B C D}
    {P : Process (D :: C :: A :: Δ)}
    {Q : Process (B :: Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ C ⅋ D ] + Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    Cut d p (Join (split-r q) P) Q ⊒
    Join q' (Cut d (split-l (split-l p')) (#process #rot P) Q)

  s-refl : ∀{Γ} {P : Process Γ} -> P ⊒ P
  s-tran : ∀{Γ} {P Q R : Process Γ} -> P ⊒ Q -> Q ⊒ R -> P ⊒ R
  s-cong :
    ∀{Γ Γ₁ Γ₂ A A'}
    {P Q : Process (A :: Γ₁)}
    {R : Process (A' :: Γ₂)}
    (d : Dual A A')
    (p : Γ ≃ Γ₁ + Γ₂) -> P ⊒ Q -> Cut d p P R ⊒ Cut d p Q R

infix  1 ⊒begin_
infixr 2 _⊒⟨⟩_ _⊒⟨_⟩_
infix  3 _⊒end

⊒begin_ : {Γ : Context} {P Q : Process Γ} -> P ⊒ Q -> P ⊒ Q
⊒begin_ p = p

_⊒end : {Γ : Context} (P : Process Γ) -> P ⊒ P
_⊒end _ = s-refl

_⊒⟨_⟩_ : {Γ : Context} (P : Process Γ) {Q R : Process Γ} -> P ⊒ Q -> Q ⊒ R -> P ⊒ R
_⊒⟨_⟩_ _ = s-tran

_⊒⟨⟩_ : {Γ : Context} (P : Process Γ) {Q : Process Γ} -> P ⊒ Q -> P ⊒ Q
_ ⊒⟨⟩ p = p

s-assoc-l : ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A A' B B'}
            {P : Process (B :: Δ₁)}
            {Q : Process (B' :: A :: Δ₂)}
            {R : Process (A' :: Γ₂)}
            (d : Dual A A') (e : Dual B B')
            (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ Δ₁ + Δ₂)
            (p' : Δ ≃ Δ₂ + Γ₂) (q' : Γ ≃ Δ₁ + Δ) ->
            Cut d p (Cut e (split-r q) P Q) R ⊒ Cut e q' P (Cut d (split-l p') (#process #here Q) R)
s-assoc-l {P = P} {Q = Q} {R = R} d e p q p' q' =
  ⊒begin
    Cut d p (Cut e (split-r q) P Q) R ⊒⟨ s-cong d p
                                          (s-comm e (dual-symm e) (split-r q) (split-l (+-comm q))) ⟩
    Cut d p (Cut (dual-symm e) (split-l (+-comm q)) Q P) R ⊒⟨ s-comm d (dual-symm d) p (+-comm p) ⟩
    Cut (dual-symm d) (+-comm p) R (Cut (dual-symm e) (split-l (+-comm q)) Q P) ⊒⟨ s-assoc-r (dual-symm d) (dual-symm e) (+-comm p) (+-comm q)
                                                                                    (+-comm p') (+-comm q') ⟩
    Cut (dual-symm e) (+-comm q') (Cut (dual-symm d) (split-r (+-comm p')) R (#process #here Q)) P ⊒⟨ s-cong (dual-symm e) (+-comm q')
                                                                                                       (s-comm (dual-symm d) d (split-r (+-comm p')) (split-l p')) ⟩
    Cut (dual-symm e) (+-comm q') (Cut d (split-l p') (#process #here Q) R) P ⊒⟨ s-comm (dual-symm e) e (+-comm q') q' ⟩
    Cut e q' P (Cut d (split-l p') (#process #here Q) R)
  ⊒end

s-cong-r :
  ∀{Γ Γ₁ Γ₂ A B}
  {P : Process (A :: Γ₁)}
  {Q Q' : Process (B :: Γ₂)}
  (d : Dual A B)
  (p : Γ ≃ Γ₁ + Γ₂) ->
  Q ⊒ Q' -> Cut d p P Q ⊒ Cut d p P Q'
s-cong-r {P = P} {Q} {Q'} d p pcong =
  ⊒begin
    Cut d p P Q                       ⊒⟨ s-comm d (dual-symm d) p (+-comm p) ⟩
    Cut (dual-symm d) (+-comm p) Q P  ⊒⟨ s-cong (dual-symm d) (+-comm p) pcong ⟩
    Cut (dual-symm d) (+-comm p) Q' P ⊒⟨ s-comm (dual-symm d) d (+-comm p) p ⟩
    Cut d p P Q'
  ⊒end

s-cong-2 :
  ∀{Γ Γ₁ Γ₂ A B}
  {P P' : Process (A :: Γ₁)}
  {Q Q' : Process (B :: Γ₂)}
  (d : Dual A B)
  (p : Γ ≃ Γ₁ + Γ₂) ->
  P ⊒ P' -> Q ⊒ Q' -> Cut d p P Q ⊒ Cut d p P' Q'
s-cong-2 {P = P} {P'} {Q} {Q'} d p Pc Qc =
  ⊒begin
    Cut d p P Q   ⊒⟨ s-cong d p Pc ⟩
    Cut d p P' Q  ⊒⟨ s-cong-r d p Qc ⟩
    Cut d p P' Q'
  ⊒end
