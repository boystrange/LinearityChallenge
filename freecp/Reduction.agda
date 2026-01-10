{-# OPTIONS --rewriting --guardedness #-}
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Fin using (Fin)
open import Data.List.Base using ([]; _∷_; [_]; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality using (sym)

open import Type
open import Equivalence
open import Context
open import Permutations
open import Process
open import Congruence

data _⊢_↝_ {n Σ Γ} (ℙ : Def Σ) : ∀{Δ} → Proc {n} Σ Γ → Proc Σ Δ → Set where
  r-call      : ∀{T} (x : T ∈ Σ) (σ : ∀{u} → Fin (T .ProcType.n) → PreType n u)
                (π : substc σ (T .context) ↭ Γ) →
                ℙ ⊢ call x σ π ↝ ↭proc π (substp σ (lookup ℙ x))
  r-link      : ∀{Δ A B C P} (eq : dual A ≈ B) (eq' : dual A ≈ C) (p : Γ ≃ [ C ] + Δ) →
                let _ , p' , eq'' = +≈ p (≈trans (≈sym eq') eq ∷ []) in
                ℙ ⊢ cut {A = A} {B} eq (link eq' (ch ⟨ < > • ⟩ ch) ⟨ p ⟩ P) ↝
                ↭proc (↭concat p') P
  r-close     : ∀{P} (eq : 𝟙 ≈ 𝟙) (p : Γ ≃ Γ + []) (p₀ : Γ ≃ [] + Γ) →
                ℙ ⊢ cut eq (wait (ch ⟨ < p₀ ⟩ P) ⟨ p ⟩ close ch) ↝ P
  r-select-l  : ∀{Γ₁ Γ₂ A B A' B' P Q R} (eq : (dual A ⊕ dual B) ≈ (A' ⊕ B'))
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                ℙ ⊢ cut {A = A & B} eq (case (ch ⟨ < p₀ ⟩ (P , Q)) ⟨ p ⟩
                                       select (ch ⟨ < q₀ ⟩ inj₁ R)) ↝
                    cut (≈after⊕L eq) (P ⟨ p ⟩ R)
  r-select-r  : ∀{Γ₁ Γ₂ A B A' B' P Q R} (eq : (dual A ⊕ dual B) ≈ (A' ⊕ B'))
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                ℙ ⊢ cut {A = A & B} eq (case (ch ⟨ < p₀ ⟩ (P , Q)) ⟨ p ⟩
                                       select (ch ⟨ < q₀ ⟩ inj₂ R)) ↝
                    cut (≈after⊕R eq) (Q ⟨ p ⟩ R)
  r-fork      : ∀{Γ₁ Γ₂ Γ₃ Δ A B A' B' P Q R} (eq : (dual A ⊗ dual B) ≈ (A' ⊗ B'))
                (p : Γ ≃ Γ₁ + Δ) (p₀ : Γ₁ ≃ [] + Γ₁) (q : Δ ≃ Γ₂ + Γ₃) (q₀ : Δ ≃ [] + Δ) →
                let _ , p' , q' = +-assoc-r p q in
                ℙ ⊢ cut {A = A ⅋ B} eq (join (ch ⟨ < p₀ ⟩ P) ⟨ p ⟩ fork (ch ⟨ < q₀ ⟩ (Q ⟨ q ⟩ R))) ↝
                    cut (≈after⊗R eq) (cut (≈after⊗L eq) (P ⟨ < p' ⟩ Q) ⟨ q' ⟩ R)
  r-cut        : ∀{Γ₁ Γ₂ A B A' Γ₁' P R Q} (eq : dual A ≈ B) (eqA : A ≈ A') (eqC : Γ₁ ≈c Γ₁')
                 (p : Γ ≃ Γ₁ + Γ₂) →
                 ℙ ⊢ P ↝ Q →
                 let _ , p' , eq'' = +≈ p eqC in
                 ℙ ⊢ cut {A = A} eq (P ⟨ p ⟩ R) ↝ cut {A = A'} (≈trans (≈dual (≈sym eqA)) eq) (Q ⟨ p' ⟩ R)
  r-cong       : ∀{Δ} {P R : Proc {n} Σ Γ} {Q : Proc Σ Δ} → P ⊒ R → ℙ ⊢ R ↝ Q → ℙ ⊢ P ↝ Q

↝≈ : ∀{n Σ Γ Δ}{P : Proc {n} Σ Γ} {Q : Proc Σ Δ} {ℙ} → ℙ ⊢ P ↝ Q → Γ ≈c Δ
↝≈ (r-call x σ π) = ≈c-refl
↝≈ (r-link eq eq' p) with +≈ p (≈trans (≈sym eq') eq ∷ [])
... | _ , _ , eq'' = eq''
↝≈ (r-close eq p p₀) = ≈c-refl
↝≈ (r-select-l eq p p₀ q₀) = ≈c-refl
↝≈ (r-select-r eq p p₀ q₀) = ≈c-refl
↝≈ (r-fork eq p p₀ q q₀) = ≈c-refl
↝≈ (r-cut eq eqA eqC p red ) with +≈ p eqC
... | _ , _ , eq' = eq'
↝≈ (r-cong _ red) = ↝≈ red
