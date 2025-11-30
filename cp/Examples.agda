{-# OPTIONS --rewriting #-}
open import Data.Sum hiding (reduce; swap)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (zero; suc; #_)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)
open import Function using (_$_)
open import Data.Maybe

open import Type
open import Context
open import Permutations
open import Process
import DeadlockFreedom as DF

reduce : ∀{Γ} -> ℕ -> Process Γ -> Process Γ
reduce zero P = P
reduce (suc n) P with DF.deadlock-freedom P
... | inj₁ (Q , _ , _) = Q
... | inj₂ (Q , _) = reduce n Q

poly0 : Process [ `∀ (var (# 0) ⅋ rav (# 0)) ]
poly0 = all (< ≫) λ X ->
        join (< ≫) $
        link (> < ≫)

poly1 : Process [ `∀ (`∀ (var (# 1) ⅋ (var (# 0) ⅋ (rav (# 0) ⊗ rav (# 1))))) ]
poly1 = all (< ≫) λ X ->
        all (< ≫) λ Y ->
        join (< ≫) $
        join (< ≫) $
        fork (< ≫) (< ≫)
             (link (> < ≫))
             (link (> < ≫))

𝔹 : Type
𝔹 = 𝟙 ⊕ 𝟙

True : Process [ 𝔹 ]
True = select true (< ≫) close

False : Process [ 𝔹 ]
False = select false (< ≫) close

Not : Process (dual 𝔹 ∷ 𝔹 ∷ [])
Not = case (< ≫)
           (wait (< ≫) False)
           (wait (< ≫) True)

Copy : Process (dual 𝔹 ∷ 𝔹 ∷ [])
Copy = cut (< ≫) (↭process swap Not) Not

Drop : Process (dual 𝔹 ∷ 𝟙 ∷ [])
Drop = case (< ≫)
            (wait (< ≫) close)
            (wait (< ≫) close)

And : Process (dual 𝔹 ∷ dual 𝔹 ∷ 𝔹 ∷ [])
And = case (< ≫)
           (wait (< ≫) Copy)
           (wait (< ≫)
                 (cut (< ≫)
                      (↭process swap Drop)
                      (wait (< ≫) False)))

Or : Process (dual 𝔹 ∷ dual 𝔹 ∷ 𝔹 ∷ [])
Or = cut (< < ≫)
         (cut (> < ≫)
              (↭process swap Not)
              (cut (> > < ≫)
                   (↭process swap Not)
                   And))
         Not

ex1 : Process [ 𝔹 ]
ex1 = cut ≫ False (cut ≫ False Or)
