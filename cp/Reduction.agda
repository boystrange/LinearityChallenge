{-# OPTIONS --rewriting #-}
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; ∃; Σ; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)
open import Data.List.Properties using (++-assoc)

open import Type
open import Context
open import Permutations
open import Process
open import Congruence

weakening : ∀{Γ Γ₁ Γ₂} (un : Un Γ₁) → Γ ≃ Γ₁ + Γ₂ → Process Γ₂ → Process Γ
weakening un p P = ↭process (↭concat p) (aux un P)
  where
    aux : ∀{Γ₁ Γ₂} (un : Un Γ₁) → Process Γ₂ → Process (Γ₁ ++ Γ₂)
    aux un-[] P = P
    aux (un-∷ un) P = weaken (< ≫) (aux un P)

contraction : ∀{Γ Γ₁ Γ₂} (un : Un Γ₁) → Γ ≃ Γ₁ + Γ₂ → Process (Γ₁ ++ Γ) → Process Γ
contraction un p P = ↭process (↭concat p) (aux un (↭process (↭left (↭sym (↭concat p))) P))
  where
    aux : ∀{Γ₁ Γ₂} → Un Γ₁ → Process (Γ₁ ++ Γ₁ ++ Γ₂) → Process (Γ₁ ++ Γ₂)
    aux un-[] P = P
    aux {`? A ∷ Γ₁} {Γ₂} (un-∷ un) P with contract (< ≫) (↭process (↭shift {`? A} {`? A ∷ Γ₁} {Γ₁ ++ Γ₂}) P)
    ... | P₁ rewrite sym (++-assoc (`? A ∷ Γ₁) Γ₁ Γ₂) with ↭process (↭sym (↭shift {`? A} {Γ₁ ++ Γ₁})) P₁
    ... | P₂ rewrite ++-assoc Γ₁ Γ₁ (`? A ∷ Γ₂) with aux un P₂
    ... | P₃ = ↭process ↭shift P₃

data _↝_ {Γ} : Process Γ → Process Γ → Set where
  r-link      : ∀{Δ A P} (p : Γ ∋ dual A ⊳ Δ) →
                cut {A} p (link (< > •)) P ↝ ↭process (↭concat p) P
  r-close     : ∀{P} (p₀ q₀ : Γ ≃ [] + Γ) →
                cut p₀ close (wait (< q₀) P) ↝ P
  r-left      : ∀{Γ₁ Γ₂ A B P Q R}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                cut {A ⊕ B} p (left (< p₀) P)
                              (case (< q₀) Q R) ↝ cut p P Q
  r-right     : ∀{Γ₁ Γ₂ A B P Q R}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                cut {A ⊕ B} p (right (< p₀) P)
                              (case (< q₀) Q R) ↝ cut p P R
  r-fork      : ∀{Γ₁ Γ₂ Γ₃ Δ A B P Q R}
                (p : Γ ≃ Δ + Γ₃) (p₀ : Γ₃ ≃ [] + Γ₃) (q : Δ ≃ Γ₁ + Γ₂) (q₀ : Δ ≃ [] + Δ) →
                let _ , p′ , q′ = +-assoc-l p q in
                cut {A ⊗ B} p (fork (< q₀) q P Q)
                              (join (< p₀) R) ↝ cut q′ P (cut (> p′) Q R)
  r-client    : ∀{Γ₁ Γ₂ A P Q}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) (un : Un Γ₁) →
                cut {`! A} p (server (< p₀) un P) (client (< q₀) Q) ↝ cut p P Q
  r-weaken    : ∀{Γ₁ Γ₂ A P Q}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) (un : Un Γ₁) →
                cut {`! A} p (server (< p₀) un P)
                             (weaken (< q₀) Q) ↝ weakening un p Q
  r-contract  : ∀{Γ₁ Γ₂ A P Q}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) (un : Un Γ₁) →
                cut {`! A} p (server (< p₀) un P)
                             (contract (< q₀) Q) ↝
                    contraction un p
                      (cut ++≃+ (server (< p₀) un P)
                      (cut (> p) (server (< p₀) un P) Q))
  r-poly       : ∀{A B Γ₁ Γ₂ P F} (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) ->
                 cut {`∃ A} p (ex {_} {B} (< p₀) P) (all (< q₀) F) ↝ cut p P (F B)
  r-cut        : ∀{Γ₁ Γ₂ A P Q R} (q : Γ ≃ Γ₁ + Γ₂) →
                 P ↝ Q → cut {A} q P R ↝ cut q Q R
  r-cong       : ∀{P R Q} → P ⊒ R → R ↝ Q → P ↝ Q
