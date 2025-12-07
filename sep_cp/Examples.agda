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
true = select (ch ⟨ < ≫ ⟩ inj₁ (close ch))

false : Process [ 𝔹 ]
false = select (ch ⟨ < ≫ ⟩ inj₂ (close ch))

if_else : ∀{Γ} → Process Γ → Process Γ → Process (dual 𝔹 ∷ Γ)
if P else Q = case (ch ⟨ < ≫ ⟩ (wait (ch ⟨ < ≫ ⟩ P) ,
                                wait (ch ⟨ < ≫ ⟩ Q)))

drop : ∀{Γ} → Process Γ → Process (dual 𝔹 ∷ Γ)
drop P = if P else P

!!_ : Process [ 𝔹 ] → Process [ 𝔹 ]
!!_ B = cut (B ⟨ ≫ ⟩ if false else true)

_&&_ _||_  : Process [ 𝔹 ] → Process [ 𝔹 ] → Process [ 𝔹 ]
A && B   = cut (A ⟨ ≫ ⟩
               (cut (B ⟨ ≫ ⟩
                    (if (link (ch ⟨ < ≫ ⟩ ch)) else (drop false)))
               )
           )
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
echo = server $ ch ⟨ < ≫ ⟩ (un-[] , (
       all $ ch ⟨ < ≫ ⟩ λ X →
       join $ ch ⟨ < ≫ ⟩
       link (ch ⟨ < ≫ ⟩ ch)))

echo-true : Process [ 𝔹 ]
echo-true = cut (echo ⟨ ≫ ⟩
                 client (ch ⟨ < ≫ ⟩
                 ex (ch ⟨ < ≫ ⟩
                 fork (ch ⟨ < ≫ ⟩ (
                   true ⟨ ≫ ⟩
                   link (ch ⟨ < ≫ ⟩ ch))))))
