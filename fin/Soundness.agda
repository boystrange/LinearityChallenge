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
