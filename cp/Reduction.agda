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
weakening un p P = #process (+++# p) (aux un P)
  where
    aux : ∀{Γ₁ Γ₂} (un : Un Γ₁) → Process Γ₂ → Process (Γ₁ ++ Γ₂)
    aux un-[] P = P
    aux (un-∷ un) P = weaken (split-l +-unit-l) (aux un P)

contraction : ∀{Γ Γ₁ Γ₂} (un : Un Γ₁) → Γ ≃ Γ₁ + Γ₂ → Process (Γ₁ ++ Γ) → Process Γ
contraction un p P = #process (+++# p) (aux un (#process (#left (#sym (+++# p))) P))
  where
    aux : ∀{Γ₁ Γ₂} → Un Γ₁ → Process (Γ₁ ++ Γ₁ ++ Γ₂) → Process (Γ₁ ++ Γ₂)
    aux un-[] P = P
    aux {`? A ∷ Γ₁} {Γ₂} (un-∷ un) P with contract (split-l +-unit-l) (#process (#shift {`? A} {`? A ∷ Γ₁} {Γ₁ ++ Γ₂}) P)
    ... | P₁ rewrite sym (++-assoc (`? A ∷ Γ₁) Γ₁ Γ₂) with #process (#sym (#shift {`? A} {Γ₁ ++ Γ₁})) P₁
    ... | P₂ rewrite ++-assoc Γ₁ Γ₁ (`? A ∷ Γ₂) with aux un P₂
    ... | P₃ = #process #shift P₃

data _↝_ {Γ} : Process Γ → Process Γ → Set where
  r-link      : ∀{Δ A} {P : Process (dual A ∷ Δ)}
                (p : Γ ≃ dual A , Δ) →
                cut {A = A} p (link (split-l (split-r split-e))) P ↝ #process (#cons p) P
  r-close     : ∀{P : Process Γ} (p₀ : Γ ≃ [] + Γ) (q₀ : Γ ≃ [] + Γ) →
                cut p₀ close (wait (split-l q₀) P) ↝ P
  r-select-l  : ∀{Γ₁ Γ₂ A B}
                {P : Process (A ∷ Γ₁)} {Q : Process (dual A ∷ Γ₂)} {R : Process (dual B ∷ Γ₂)}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                cut {A = A ⊕ B} p (select true (split-l p₀) P)
                                  (case (split-l q₀) Q R) ↝ cut p P Q
  r-select-r  : ∀{Γ₁ Γ₂ A B}
                {P : Process (B ∷ Γ₁)} {Q : Process (dual A ∷ Γ₂)} {R : Process (dual B ∷ Γ₂)}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                cut {A = A ⊕ B} p (select false (split-l p₀) P)
                                  (case (split-l q₀) Q R) ↝ cut p P R
  r-fork      : ∀{Γ₁ Γ₂ Γ₃ Δ A B}
                {P : Process (A ∷ Γ₁)} {Q : Process (B ∷ Γ₂)} {R : Process (dual B ∷ dual A ∷ Γ₃)}
                (p : Γ ≃ Δ + Γ₃) (p₀ : Γ₃ ≃ [] + Γ₃) (q : Δ ≃ Γ₁ + Γ₂) (q₀ : Δ ≃ [] + Δ) →
                let _ , p′ , q′ = +-assoc-l p q in
                cut p (fork (split-l q₀) q P Q)
                      (join (split-l p₀) R) ↝ cut q′ P (cut (split-r p′) Q R)
  r-client    : ∀{Γ₁ Γ₂ A} {P : Process (A ∷ Γ₁)} {Q : Process (dual A ∷ Γ₂)}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) (un : Un Γ₁) →
                cut p (server (split-l p₀) un P) (client (split-l q₀) Q) ↝ cut p P Q
  r-weaken    : ∀{Γ₁ Γ₂ A} {P : Process (A ∷ Γ₁)} {Q : Process Γ₂}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) (un : Un Γ₁) →
                cut p (server (split-l p₀) un P)
                      (weaken (split-l q₀) Q) ↝ weakening un p Q
  r-contract  : ∀{Γ₁ Γ₂ A}
                {P : Process (A ∷ Γ₁)} {Q : Process (`? (dual A) ∷ `? (dual A) ∷ Γ₂)}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) (un : Un Γ₁) →
                cut p (server (split-l p₀) un P)
                      (contract (split-l q₀) Q) ↝
                    contraction un p
                      (cut ++≃+ (server (split-l p₀) un P)
                      (cut (split-r p) (server (split-l p₀) un P) Q))
  r-poly       : ∀{A B Γ₁ Γ₂} {P : Process (subst (make-subst B) A ∷ Γ₁)}
                 {F : (C : Type) -> Process (subst (make-subst C) (dual A) ∷ Γ₂)}
                 (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) ->
                 cut p (ex {A = A} (split-l p₀) P) (all (split-l q₀) F) ↝ cut p P (F B)
  r-cut        : ∀{Γ₁ Γ₂ A} {P Q : Process (A ∷ Γ₁)} {R : Process (dual A ∷ Γ₂)}
                 (q : Γ ≃ Γ₁ + Γ₂) → P ↝ Q → cut q P R ↝ cut q Q R
  r-cong       : ∀{P R Q : Process Γ} → P ⊒ R → R ↝ Q → P ↝ Q
