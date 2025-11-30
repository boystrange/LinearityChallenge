{-# OPTIONS --rewriting #-}
open import Data.Sum hiding (reduce; swap)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
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

_⊸_ : ∀{n} -> PreType n -> PreType n -> PreType n
A ⊸ B = dual A ⅋ B

reduce : ∀{Γ} -> ℕ -> Process Γ -> Process Γ
reduce zero P = P
reduce (suc n) P with DF.deadlock-freedom P
... | inj₁ (Q , _ , _) = Q
... | inj₂ (Q , _) = reduce n Q

identity : Process [ `∀ (var (# 0) ⊸ var (# 0)) ]
identity = all (< ≫) λ X -> join (< ≫) $
                            link (> < ≫)

⊗-comm : Process [ `∀ (`∀ ((var (# 0) ⊗ var (# 1)) ⊸ (var (# 1) ⊗ var (# 0)))) ]
⊗-comm = all (< ≫) λ X ->
         all (< ≫) λ Y ->
         join (< ≫) $
         join (> < ≫) $
         fork (> > < ≫) (< ≫)
              (link (< ≫))
              (link (< ≫))

𝔹 : Type
𝔹 = 𝟙 ⊕ 𝟙

True : Process [ 𝔹 ]
True = left (< ≫) close

False : Process [ 𝔹 ]
False = right (< ≫) close

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
