{-# OPTIONS --rewriting #-}
open import Function using (_$_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Fin using (zero; suc; #_)
open import Data.List.Base using ([]; _∷_; [_])
open import Relation.Unary

open import Type
open import Context
open import Permutations
open import Process
open import DeadlockFreedom using (deadlock-freedom)

𝔹 : Type
𝔹 = 𝟙 ⊕ 𝟙

True : Proc [ 𝔹 ]
True = select (ch ⟨ < ≫ ⟩ inj₁ (close ch))

False : Proc [ 𝔹 ]
False = select (ch ⟨ < ≫ ⟩ inj₂ (close ch))

If_Else : ∀[ Proc ⇒ Proc ⇒ (dual 𝔹 ∷_) ⊢ Proc ]
If P Else Q = curry∗ case ch (< ≫) ( wait (ch ⟨ < ≫ ⟩ P)
                                   , wait (ch ⟨ < ≫ ⟩ Q))

Drop : ∀[ Proc ⇒ (dual 𝔹 ∷_) ⊢ Proc ]
Drop P = If P Else P

!!_ : Proc [ 𝔹 ] → Proc [ 𝔹 ]
!!_ B = curry∗ cut B ≫ (If False Else True)

_&&_ _||_  : Proc [ 𝔹 ] → Proc [ 𝔹 ] → Proc [ 𝔹 ]
A && B   = curry∗ cut A ≫ $
           curry∗ cut B ≫ $
           If (curry∗ link ch (< ≫) ch) Else (Drop False)
A || B   = !! ((!! A) && (!! B))

{-# TERMINATING #-}
eval : ∀[ Proc ⇒ Proc ]
eval P with deadlock-freedom P
... | inj₁ (Q , _ , _)  = Q
... | inj₂ (Q , _)      = eval Q

_⊸_ : ∀{n} → PreType n → PreType n → PreType n
A ⊸ B = dual A ⅋ B

Echo : let X = var (# 0) in
       Proc [ `! (`∀ (X ⊸ X)) ]
Echo = curry∗ server ch (< ≫)
             ( un-[]
             , curry∗ all ch (< ≫) λ X →
               curry∗ join ch (< ≫) $
               curry∗ link ch (< ≫) ch)

Echo-True : Proc [ 𝔹 ]
Echo-True = curry∗ cut Echo ≫ $
            curry∗ client ch (< ≫) $
            curry∗ ex ch (< ≫) $
            curry∗ fork ch (< ≫) $ True ⟨ ≫ ⟩ curry∗ link ch (< ≫) ch
