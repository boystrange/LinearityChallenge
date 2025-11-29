{-# OPTIONS --rewriting #-}
open import Data.Sum
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Unit.Base using (⊤; tt)
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (zero; suc)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)
open import Function using (_$_)
open import Data.Maybe

open import Type
open import Context
open import Permutations
open import Process
import DeadlockFreedom as DF

normalize : ∀{Γ} -> ℕ -> Process Γ -> Data.Unit.Base.⊤ ⊎ Process Γ
normalize zero P = inj₁ tt
normalize (suc n) P with DF.deadlock-freedom P
... | inj₁ (Q , _ , _) = inj₂ Q
... | inj₂ (Q , _) = normalize n Q

poly0 : Process [ `∀ (var zero ⅋ rav zero) ]
poly0 = all (⊲ []) λ X ->
      join (⊲ [])
      (link (⊳ ⊲ []))

poly1 : Process [ `∀ (`∀ (var (suc zero) ⅋ (var zero ⅋ (rav zero ⊗ rav (suc zero))))) ]
poly1 = all (⊲ []) λ X ->
        all (⊲ []) λ Y ->
        join (⊲ []) $
        join (⊲ ⊳ []) $
        fork (⊲ ⊳ ⊳ []) (⊲ ⊳ [])
             (link (⊳ ⊲ []))
             (link (⊳ ⊲ []))

𝔹 : Type
𝔹 = 𝟙 ⊕ 𝟙

True : Process [ 𝔹 ]
True = select true (⊲ []) close

False : Process [ 𝔹 ]
False = select false (⊲ []) close

Not : Process (dual 𝔹 ∷ 𝔹 ∷ [])
Not = case (⊲ ⊳ [])
           (wait (⊲ ⊳ []) False)
           (wait (⊲ ⊳ []) True)

Copy : Process (dual 𝔹 ∷ 𝔹 ∷ [])
Copy = cut {𝔹} (⊲ ⊳ []) (#process #here Not) Not

Drop : Process (dual 𝔹 ∷ 𝟙 ∷ [])
Drop = case (⊲ ⊳ [])
            (wait (⊲ ⊳ []) close)
            (wait (⊲ ⊳ []) close)

And : Process (dual 𝔹 ∷ dual 𝔹 ∷ 𝔹 ∷ [])
And = case (⊲ ⊳ ⊳ [])
           (wait (⊲ ⊳ ⊳ []) Copy)
           (wait (⊲ ⊳ ⊳ [])
                 (cut (⊲ ⊳ [])
                      (#process #here Drop)
                      (wait (⊲ ⊳ []) False)))

Or : Process (dual 𝔹 ∷ dual 𝔹 ∷ 𝔹 ∷ [])
Or = cut (⊲ ⊲ ⊳ [])
         (cut (⊳ ⊲ ⊳ [])
              (#process #here Not)
              (cut (⊳ ⊳ ⊲ [])
                   (#process #here Not)
                   And))
         Not

ex1 : Process [ 𝔹 ]
ex1 = cut (⊳ []) True (cut (⊳ ⊳ []) True Or)
