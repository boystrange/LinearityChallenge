{-# OPTIONS --rewriting #-}
open import Function using (_$_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Fin using (zero; suc; #_)
open import Data.List.Base using ([]; _∷_; [_])
open import Relation.Unary

open import Type
open import Context
open import Separation
open import Permutations
open import Process
open import DeadlockFreedom using (deadlock-freedom)

𝔹 : Type
𝔹 = 𝟙 ⊕ 𝟙

true : Proc [ 𝔹 ]
true = select (ch ⟨ < ≫ ⟩ inj₁ (close ch))

false : Proc [ 𝔹 ]
false = select (ch ⟨ < ≫ ⟩ inj₂ (close ch))

if_else : ∀{Γ} → Proc Γ → Proc Γ → Proc (dual 𝔹 ∷ Γ)
if P else Q = curry∗ case ch (< ≫) ( wait (ch ⟨ < ≫ ⟩ P)
                                   , wait (ch ⟨ < ≫ ⟩ Q))

drop : ∀{Γ} → Proc Γ → Proc (dual 𝔹 ∷ Γ)
drop P = if P else P

!!_ : Proc [ 𝔹 ] → Proc [ 𝔹 ]
!!_ B = curry∗ cut B ≫ (if false else true)

_&&_ _||_  : Proc [ 𝔹 ] → Proc [ 𝔹 ] → Proc [ 𝔹 ]
A && B   = curry∗ cut A ≫ $
           curry∗ cut B ≫ $
           if (curry∗ link ch (< ≫) ch) else (drop false)
A || B   = !! ((!! A) && (!! B))

{-# TERMINATING #-}
eval : ∀{Γ} → Proc Γ → Proc Γ
eval P with deadlock-freedom P
... | inj₁ (Q , _ , _)  = Q
... | inj₂ (Q , _)      = eval Q

_⊸_ : ∀{n} → PreType n → PreType n → PreType n
A ⊸ B = dual A ⅋ B

echo : let X = var (# 0) in
       Proc [ `! (`∀ (X ⊸ X)) ]
echo = curry∗ server ch (< ≫)
             ( un-[]
             , curry∗ all ch (< ≫) λ X →
               curry∗ join ch (< ≫) $
               curry∗ link ch (< ≫) ch)

echo-true : Proc [ 𝔹 ]
echo-true = curry∗ cut echo ≫ $
            curry∗ client ch (< ≫) $
            curry∗ ex ch (< ≫) $
            curry∗ fork ch (< ≫) $ true ⟨ ≫ ⟩ curry∗ link ch (< ≫) ch
