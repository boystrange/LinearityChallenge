{-# OPTIONS --rewriting #-}
open import Data.Nat using (zero; suc)
open import Data.Fin using (zero; suc)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)
open import Function using (_$_)

open import Type
open import Context
open import Process

poly0 : Process [ `∀ (var zero ⅋ rav zero) ]
poly0 = all (split-l split-e) λ X ->
      join (split-l split-e)
      (link (split-r (split-l split-e)))

poly1 : Process [ `∀ (`∀ (var (suc zero) ⅋ (var zero ⅋ (rav zero ⊗ rav (suc zero))))) ]
poly1 = all (split-l split-e) λ X ->
        all (split-l split-e) λ Y ->
        join (split-l split-e) $
        join (split-l (split-r split-e)) $
        fork (split-l (split-r (split-r split-e))) (split-l (split-r split-e))
             (link (split-r (split-l split-e)))
             (link (split-r (split-l split-e)))
