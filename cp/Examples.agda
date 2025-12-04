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
open import DeadlockFreedom using (deadlock-freedom)

𝔹 : Type
𝔹 = 𝟙 ⊕ 𝟙

true : Process [ 𝔹 ]
true = left (< ≫) close

false : Process [ 𝔹 ]
false = right (< ≫) close

if_else : ∀{Γ} → Process Γ → Process Γ → Process (dual 𝔹 ∷ Γ)
if P else Q = case (< ≫) (wait (< ≫) P) (wait (< ≫) Q)

drop : ∀{Γ} → Process Γ → Process (dual 𝔹 ∷ Γ)
drop P = if P else P

!!_ : Process [ 𝔹 ] → Process [ 𝔹 ]
!!_ B = cut ≫ B (if false else true)

_&&_ _||_  : Process [ 𝔹 ] → Process [ 𝔹 ] → Process [ 𝔹 ]
A && B   = cut ≫ A (cut ≫ B (if (link (< ≫)) else (drop false)))
A || B   = !! ((!! A) && (!! B))

{-# TERMINATING #-}
eval : ∀{Γ} → Process Γ → Process Γ
eval P with deadlock-freedom P
... | inj₁ (Q , _ , _)  = Q
... | inj₂ (Q , _)      = eval Q

_⊸_ : ∀{n} → PreType n → PreType n → PreType n
A ⊸ B = dual A ⅋ B

echo : let X = var (# 0) in
       Process [ `! (`∀ (X ⊸ X)) ]
echo = server (< ≫) un-[] $
       all (< ≫) λ X →
       join (< ≫) $
       link (< ≫)

echo-true : Process [ 𝔹 ]
echo-true = cut ≫ echo (client (< ≫) $
                       ex (< ≫) $
                       fork (< ≫) ≫ true (link (< ≫)))

⊗-comm : let X = var (# 1) in
         let Y = var (# 0) in
         Process [ `∀ (`∀ ((X ⊗ Y) ⊸ (Y ⊗ X))) ]
⊗-comm = all (< ≫) λ X →
         all (< ≫) λ Y →
         join (< ≫) $
         join (> < ≫) $
         fork (> > < ≫) (< ≫)
              (link (< ≫))
              (link (< ≫))
