{-# OPTIONS --rewriting #-}
open import Function using (_$_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; curry)
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

!! : Proc [ 𝔹 ] → Proc [ 𝔹 ]
!! B = curry∗ cut B ≫ (If False Else True)

_&&_ _||_  : Proc [ 𝔹 ] → Proc [ 𝔹 ] → Proc [ 𝔹 ]
A && B   = curry∗ cut A ≫ $
           curry∗ cut B ≫ $
           If curry∗ link ch (< ≫) ch Else (Drop False)
A || B   = !! (!! A && !! B)

{-# TERMINATING #-}
eval : ∀[ Proc ⇒ Proc ]
eval P with deadlock-freedom P
... | inj₁ (Q , _ , _)  = Q
... | inj₂ (Q , _)      = eval Q

send : ∀{A B Γ} → Proc (B ∷ Γ) → Proc (A ⊗ B ∷ dual A ∷ Γ)
send P = curry∗ (curry∗ fork ch (< ≫)) (curry∗ link ch (< > •) ch) (< ≫) P

ServerT : Type
ServerT = `! (`∀ (rav (# 0) ⅋ (var (# 0) ⊗ 𝟙)))

Server : Proc [ ServerT ]
Server = curry (curry∗ server ch (< ≫)) un-[] $
         curry∗ all ch (< ≫) λ X →
         curry∗ join ch (< ≫) $
         send $
         close ch

Client : Proc (dual ServerT ∷ 𝔹 ∷ [])
Client = curry∗ client ch (< ≫) $
         curry∗ (ex {_} {𝔹}) ch (< ≫) $
         curry∗ (curry∗ fork ch (< ≫)) True ≫ $
         curry∗ join ch (< ≫) $
         curry∗ wait ch (< ≫) $
         curry∗ link ch (< > •) ch

Main : Proc [ 𝔹 ]
Main = curry∗ cut Client (< •) Server
