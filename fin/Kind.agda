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

module Kind where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Bool using (Bool; if_then_else_)
open Bool using (true; false)

open import Relation.Nullary using (¬_; contradiction)

open import Type
open import Context
open import Process
open import Congruence

data IsLink {Γ} : Process Γ -> Set where
  link :
    ∀{A B} (d : Dual A B) (p : Γ ≃ [ A ] + [ B ]) -> IsLink (Link d p)

data Input : ∀{Γ} -> Process Γ -> Set where
  fail :
    ∀{Γ Δ}
    (p : Γ ≃ [] + Δ) -> Input (Fail (split-l p))
  wait :
    ∀{Γ Δ} (p : Γ ≃ [] + Δ) {P : Process Δ} -> Input (Wait (split-l p) P)
  case :
    ∀{Γ Δ A B} (p : Γ ≃ [] + Δ) {P : Process (A :: Δ)} {Q : Process (B :: Δ)} ->
    Input (Case (split-l p) P Q)
  join :
    ∀{Γ Δ A B} (p : Γ ≃ [] + Δ) {P : Process (B :: A :: Δ)} ->
    Input (Join (split-l p) P)

data Output : ∀{Γ} -> Process Γ -> Set where
  close :
    ∀{Γ} (p : Γ ≃ [ One ] + []) -> Output (Close p)
  select :
    ∀{Γ Δ A B} (x : Bool) (p : Γ ≃ [] + Δ) {P : Process ((if x then A else B) :: Δ)} ->
    Output (Select x (split-l p) P)
  fork :
    ∀{Γ Δ Δ₁ Δ₂ A B} (p : Γ ≃ [] + Δ) (q : Δ ≃ Δ₁ + Δ₂)
    {P : Process (A :: Δ₁)} {Q : Process (B :: Δ₂)} ->
    Output (Fork (split-l p) q P Q)

Action : ∀{Γ} -> Process Γ -> Set
Action P = Input P ⊎ Output P

data ThreadNext : ∀{Γ} -> Process Γ -> Set where
  fail :
    ∀{A Γ Δ}
    (p : Γ ≃ [ Top ] + Δ) -> ThreadNext (Fail (split-r {A} p))
  wait :
    ∀{C Γ Δ} (p : Γ ≃ [ Bot ] + Δ) {P : Process (C :: Δ)} -> ThreadNext (Wait (split-r p) P)
  case :
    ∀{Γ Δ C A B} (p : Γ ≃ [ A & B ] + Δ) {P : Process (A :: C :: Δ)} {Q : Process (B :: C :: Δ)} ->
    ThreadNext (Case (split-r p) P Q)
  join :
    ∀{Γ Δ C A B} (p : Γ ≃ [ A ⅋ B ] + Δ) {P : Process (B :: A :: C :: Δ)} ->
    ThreadNext (Join (split-r p) P)
  select :
    ∀{Γ Δ C A B} (x : Bool) (p : Γ ≃ [ A ⊕ B ] + Δ) {P : Process ((if x then A else B) :: C :: Δ)} ->
    ThreadNext (Select x (split-r p) P)
  fork-l :
    ∀{Γ Δ Δ₁ Δ₂ C A B} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂)
    {P : Process (A :: C :: Δ₁)} {Q : Process (B :: Δ₂)} ->
    ThreadNext (Fork (split-r p) (split-l q) P Q)
  fork-r :
    ∀{Γ Δ Δ₁ Δ₂ C A B} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂)
    {P : Process (A :: Δ₁)} {Q : Process (B :: C :: Δ₂)} ->
    ThreadNext (Fork (split-r p) (split-r q) P Q)

data Thread {Γ} : Process Γ -> Set where
  link :
    ∀{A B}
    (d : Dual A B) (p : Γ ≃ [ A ] + [ B ]) -> Thread (Link d p)
  fail :
    ∀{Δ}
    (p : Γ ≃ [ Top ] + Δ) -> Thread (Fail p)
  wait :
    ∀{Δ} (p : Γ ≃ [ Bot ] + Δ) {P : Process Δ} -> Thread (Wait p P)
  case :
    ∀{Δ A B} (p : Γ ≃ [ A & B ] + Δ) {P : Process (A :: Δ)} {Q : Process (B :: Δ)} ->
    Thread (Case p P Q)
  join :
    ∀{Δ A B} (p : Γ ≃ [ A ⅋ B ] + Δ) {P : Process (B :: A :: Δ)} ->
    Thread (Join p P)
  close :
    ∀(p : Γ ≃ [ One ] + []) -> Thread (Close p)
  select :
    ∀{Δ A B} (x : Bool) (p : Γ ≃ [ A ⊕ B ] + Δ) {P : Process ((if x then A else B) :: Δ)} ->
    Thread (Select x p P)
  fork :
    ∀{Δ Δ₁ Δ₂ A B} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂)
    {P : Process (A :: Δ₁)} {Q : Process (B :: Δ₂)} ->
    Thread (Fork p q P Q)

data CutFree {Γ} : Process Γ -> Set where
  link :
    ∀{A B}
    (d : Dual A B) (p : Γ ≃ [ A ] + [ B ]) -> CutFree (Link d p)
  fail :
    ∀{Δ} (p : Γ ≃ [ Top ] + Δ) -> CutFree (Fail p)
  wait :
    ∀{Δ} (p : Γ ≃ [ Bot ] + Δ) {P : Process Δ} -> CutFree P -> CutFree (Wait p P)
  case :
    ∀{Δ A B} (p : Γ ≃ [ A & B ] + Δ) {P : Process (A :: Δ)} {Q : Process (B :: Δ)} ->
    CutFree P -> CutFree Q -> CutFree (Case p P Q)
  join :
    ∀{Δ A B} (p : Γ ≃ [ A ⅋ B ] + Δ) {P : Process (B :: A :: Δ)} ->
    CutFree P -> CutFree (Join p P)
  close :
    ∀(p : Γ ≃ [ One ] + []) -> CutFree (Close p)
  select :
    ∀{Δ A B} (x : Bool) (p : Γ ≃ [ A ⊕ B ] + Δ) {P : Process ((if x then A else B) :: Δ)} ->
    CutFree P -> CutFree (Select x p P)
  fork :
    ∀{Δ Δ₁ Δ₂ A B} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂)
    {P : Process (A :: Δ₁)} {Q : Process (B :: Δ₂)} ->
    CutFree P -> CutFree Q -> CutFree (Fork p q P Q)

thread-is : ∀{Γ} {P : Process Γ} -> Thread P ->
  IsLink P ⊎ ThreadNext P ⊎ Input P ⊎ Output P
thread-is (link d p) = inj₁ (link d p)
thread-is (fail (split-l p)) = inj₂ (inj₂ (inj₁ (fail p)))
thread-is (fail (split-r p)) = inj₂ (inj₁ (fail p))
thread-is (wait (split-l p)) = inj₂ (inj₂ (inj₁ (wait p)))
thread-is (wait (split-r p)) = inj₂ (inj₁ (wait p))
thread-is (case (split-l p)) = inj₂ (inj₂ (inj₁ (case p)))
thread-is (case (split-r p)) = inj₂ (inj₁ (case p))
thread-is (join (split-l p)) = inj₂ (inj₂ (inj₁ (join p)))
thread-is (join (split-r p)) = inj₂ (inj₁ (join p))
thread-is (close p) = inj₂ (inj₂ (inj₂ (close p)))
thread-is (select x (split-l p)) = inj₂ (inj₂ (inj₂ (select x p)))
thread-is (select x (split-r p)) = inj₂ (inj₁ (select x p))
thread-is (fork (split-l p) q) = inj₂ (inj₂ (inj₂ (fork p q)))
thread-is (fork (split-r p) (split-l q)) = inj₂ (inj₁ (fork-l p q))
thread-is (fork (split-r p) (split-r q)) = inj₂ (inj₁ (fork-r p q))

-- CLASSIFICATION OF CUTS

data IsCut {Γ} : Process Γ -> Set where
  cut :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)} ->
    IsCut (Cut d p P Q)

data CanonicalCut {Γ} : Process Γ -> Set where
  cc-link :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)} ->
    IsLink P -> CanonicalCut (Cut d p P Q)
  cc-next :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)} ->
    ThreadNext P -> CanonicalCut (Cut d p P Q)
  cc-redex :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)} ->
    Output P -> Input Q -> CanonicalCut (Cut d p P Q)

input-input :
  ∀{Γ Δ A B} {P : Process (A :: Γ)} {Q : Process (B :: Δ)} ->
  Dual A B -> ¬ (Input P × Input Q)
input-input dual-top-zero (fail p , ())
input-input dual-bot-one (wait p , ())
input-input (dual-with-plus d d₁) (case p , ())
input-input (dual-join-fork d d₁) (join p , ())

output-output :
  ∀{Γ Δ A B} {P : Process (A :: Γ)} {Q : Process (B :: Δ)} ->
  Dual A B -> ¬ (Output P × Output Q)
output-output dual-one-bot (close _ , close ())
output-output (dual-plus-with d d₁) (select _ p , close ())
output-output (dual-fork-join d d₁) (fork p q , close ())

canonical-cut :
  ∀{Γ Γ₁ Γ₂ A B}
  {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)}
  (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) ->
  Thread P -> Thread Q ->
  ∃[ R ] CanonicalCut R × Cut d p P Q ⊒ R
canonical-cut dc pc Pt Qt with thread-is Pt | thread-is Qt
... | inj₁ x | y = _ , cc-link dc pc x , s-refl
... | inj₂ (inj₁ x) | y = _ , cc-next dc pc x , s-refl
... | inj₂ (inj₂ x) | inj₁ y = _ , cc-link (dual-symm dc) (+-comm pc) y , s-comm dc (dual-symm dc) pc (+-comm pc)
... | inj₂ (inj₂ x) | inj₂ (inj₁ y) = _ , cc-next (dual-symm dc) (+-comm pc) y , s-comm dc (dual-symm dc) pc (+-comm pc)
... | inj₂ (inj₂ (inj₁ x)) | inj₂ (inj₂ (inj₁ y)) = contradiction (x , y) (input-input dc)
... | inj₂ (inj₂ (inj₁ x)) | inj₂ (inj₂ (inj₂ y)) = _ , cc-redex (dual-symm dc) (+-comm pc) y x , s-comm dc (dual-symm dc) pc (+-comm pc)
... | inj₂ (inj₂ (inj₂ x)) | inj₂ (inj₂ (inj₁ y)) = _ , cc-redex dc pc x y , s-refl
... | inj₂ (inj₂ (inj₂ x)) | inj₂ (inj₂ (inj₂ y)) = contradiction (x , y) (output-output dc)

process-is : ∀{Γ} (P : Process Γ) -> Thread P ⊎ IsCut P
process-is (Close p) = inj₁ (close p)
process-is (Link d p) = inj₁ (link d p)
process-is (Fail p) = inj₁ (fail p)
process-is (Wait p P) = inj₁ (wait p)
process-is (Select x p P) = inj₁ (select x p)
process-is (Case p P Q) = inj₁ (case p)
process-is (Fork p q P Q) = inj₁ (fork p q)
process-is (Join p P) = inj₁ (join p)
process-is (Cut d p P Q) = inj₂ (cut d p)
