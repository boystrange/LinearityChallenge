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

module Soundness where

open import Data.Product using (Σ; _×_; _,_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Nullary using (¬_; contradiction)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Type
open import Context
open import Process
open import Kind

postulate
  cut-elimination : ∀{Γ} (P : Process Γ) -> Σ[ Q ∈ Process Γ ] CutFree Q

weak-soundness : ∀{P : Process [ Zero ]} -> ¬ CutFree P
weak-soundness (link d (split-l ()))
weak-soundness (link d (split-r ()))
weak-soundness (fail (split-r ()))
weak-soundness (wait (split-r ()) cf)
weak-soundness (case (split-r ()) cf cf₁)
weak-soundness (join (split-r ()) cf)
weak-soundness (select x (split-r ()) cf)
weak-soundness (fork (split-r ()) q cf cf₁)

strong-soundness : ¬ (Process [ Zero ])
strong-soundness P with cut-elimination P
... | _ , cf = weak-soundness cf

-- lemma : ∀{Γ Δ}(P : Process Γ) -> Γ ≃ [ Zero ] + Δ ->
--         ∃[ Θ ] Δ ≃ [ Top ] + Θ
