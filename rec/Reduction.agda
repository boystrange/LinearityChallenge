{-# OPTIONS --rewriting --guardedness #-}
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.List.Base using ([]; _∷_; [_]; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality using (sym)

open import Type
open import Context
open import Permutations
open import Process
open import Congruence

weakening : ∀[ Un ∗ Proc ⇒ Proc ]
weakening (un ⟨ p ⟩ P) = ↭proc (↭concat p) (aux un P)
  where
    aux : ∀{Γ₁ Γ₂} (un : Un Γ₁) → Proc Γ₂ → Proc (Γ₁ ++ Γ₂)
    aux un-[] P = P
    aux (un-∷ un) P = weaken (ch ⟨ < ≫ ⟩ aux un P)

contraction : ∀{Γ Γ₁ Γ₂} (un : Un Γ₁) → Γ ≃ Γ₁ + Γ₂ → Proc (Γ₁ ++ Γ) → Proc Γ
contraction un p P = ↭proc (↭concat p) (aux un (↭proc (↭left (↭sym (↭concat p))) P))
  where
    aux : ∀{Γ₁ Γ₂} → Un Γ₁ → Proc (Γ₁ ++ Γ₁ ++ Γ₂) → Proc (Γ₁ ++ Γ₂)
    aux un-[] P = P
    aux {`? A ∷ Γ₁} {Γ₂} (un-∷ un) P with contract (ch ⟨ < ≫ ⟩ (↭proc (↭shift {`? A} {`? A ∷ Γ₁} {Γ₁ ++ Γ₂}) P))
    ... | P₁ rewrite sym (++-assoc (`? A ∷ Γ₁) Γ₁ Γ₂) with ↭proc (↭sym (↭shift {`? A} {Γ₁ ++ Γ₁})) P₁
    ... | P₂ rewrite ++-assoc Γ₁ Γ₁ (`? A ∷ Γ₂) with aux un P₂
    ... | P₃ = ↭proc ↭shift P₃

data _↝_ {Γ} : Proc Γ → Proc Γ → Set where
  r-rec       : ∀{Δ P} {π : Δ ↭ Γ} → rec P π ↝ ↭proc π (Unfold P)
  r-link      : ∀{Δ A P} (p : Γ ≃ [ dual A .force ] + Δ) →
                cut {A = A} (link (ch ⟨ < > • ⟩ ch) ⟨ p ⟩ P) ↝ ↭proc (↭concat p) P
  r-close     : ∀{P} (p : Γ ≃ Γ + []) (p₀ : Γ ≃ [] + Γ) →
                cut (wait (ch ⟨ < p₀ ⟩ P) ⟨ p ⟩ close ch) ↝ P
  r-select-l  : ∀{Γ₁ Γ₂ A B P Q R}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                cut {A = A & B} (case (ch ⟨ < p₀ ⟩ (P , Q)) ⟨ p ⟩
                                select (ch ⟨ < q₀ ⟩ inj₁ R)) ↝ cut (P ⟨ p ⟩ R)
  r-select-r  : ∀{Γ₁ Γ₂ A B P Q R}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                cut {A = A & B} (case (ch ⟨ < p₀ ⟩ (P , Q)) ⟨ p ⟩
                                select (ch ⟨ < q₀ ⟩ inj₂ R)) ↝ cut (Q ⟨ p ⟩ R)
  r-fork      : ∀{Γ₁ Γ₂ Γ₃ Δ A B P Q R}
                (p : Γ ≃ Γ₁ + Δ) (p₀ : Γ₁ ≃ [] + Γ₁) (q : Δ ≃ Γ₂ + Γ₃) (q₀ : Δ ≃ [] + Δ) →
                let _ , p' , q' = +-assoc-r p q in
                cut {A = A ⅋ B} (join (ch ⟨ < p₀ ⟩ P) ⟨ p ⟩
                                fork (ch ⟨ < q₀ ⟩ (Q ⟨ q ⟩ R))) ↝ cut (cut (P ⟨ < p' ⟩ Q) ⟨ q' ⟩ R)
  r-client    : ∀{Γ₁ Γ₂ A P Q}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) (un : Un Γ₁) →
                cut {A = `! A} (server (ch ⟨ < p₀ ⟩ (un , P)) ⟨ p ⟩ client (ch ⟨ < q₀ ⟩ Q)) ↝
                cut (P ⟨ p ⟩ Q)
  r-weaken    : ∀{Γ₁ Γ₂ A P Q}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) (un : Un Γ₁) →
                cut {A = `! A} (server (ch ⟨ < p₀ ⟩ (un , P)) ⟨ p ⟩ weaken (ch ⟨ < q₀ ⟩ Q)) ↝
                weakening (un ⟨ p ⟩ Q)
  r-contract  : ∀{Γ₁ Γ₂ A P Q}
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) (un : Un Γ₁) →
                cut (server {A} (ch ⟨ < p₀ ⟩ (un , P)) ⟨ p ⟩ contract (ch ⟨ < q₀ ⟩ Q)) ↝
                  contraction un p (cut (server {A} (ch ⟨ < p₀ ⟩ (un , P)) ⟨ ++≃+ ⟩
                                        cut (server {A} (ch ⟨ < p₀ ⟩ (un , P)) ⟨ > p ⟩ Q)))
  r-exists     : ∀{A B Γ₁ Γ₂ P F} (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                 cut {A = `∀ A} (all (ch ⟨ < p₀ ⟩ F) ⟨ p ⟩ ex {B = B} (ch ⟨ < q₀ ⟩ P)) ↝
                 cut (F B ⟨ p ⟩ P)
  r-cut        : ∀{Γ₁ Γ₂ A P Q R} (q : Γ ≃ Γ₁ + Γ₂) →
                 P ↝ Q → cut {A = A} (P ⟨ q ⟩ R) ↝ cut (Q ⟨ q ⟩ R)
  r-cong       : ∀{P R Q} → P ⊒ R → R ↝ Q → P ↝ Q
