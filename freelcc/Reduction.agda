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

data _⊢_↝_⊣_ {n Σ Γ} (ℙ : Def Σ) : ∀{Δ} → Proc {n} Σ Γ → Proc Σ Δ → Γ ≈c Δ → Set where
  r-call      : ∀{T} (x : T ∈ Σ) (σ : ∀{u} → Fin (T .ProcType.n) → PreType n u)
                (π : substc σ (T .context) ↭ Γ) →
                ℙ ⊢ call x σ π ↝ ↭proc π (substp σ (lookup ℙ x)) ⊣ ≈c-refl
  r-link      : ∀{Δ A B C P} (eq : dual A ≈ B) (eq' : dual A ≈ C) (p : Γ ≃ [ C ] + Δ) →
                let _ , p' , eq'' = +≈ p (≈trans (≈sym eq') eq ∷ []) in
                ℙ ⊢ cut {A = A} {B} eq (link eq' (ch ⟨ < > • ⟩ ch) ⟨ p ⟩ P) ↝
                ↭proc (↭concat p') P ⊣ eq''
  r-close     : ∀{P} (eq : 𝟙 ≈ 𝟙) (p : Γ ≃ Γ + []) (p₀ : Γ ≃ [] + Γ) →
                ℙ ⊢ cut eq (wait (ch ⟨ < p₀ ⟩ P) ⟨ p ⟩ close ch) ↝ P ⊣ ≈c-refl
  r-select-l  : ∀{Γ₁ Γ₂ A B P Q R} (eq : (dual A ⊕ dual B) ≈ (dual A ⊕ dual B))
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                ℙ ⊢ cut {A = A & B} eq (case (ch ⟨ < p₀ ⟩ (P , Q)) ⟨ p ⟩
                                       select (ch ⟨ < q₀ ⟩ inj₁ R)) ↝
                    cut (≈after⊕L eq) (P ⟨ p ⟩ R) ⊣ ≈c-refl
  r-select-r  : ∀{Γ₁ Γ₂ A B P Q R} (eq : (dual A ⊕ dual B) ≈ (dual A ⊕ dual B))
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                ℙ ⊢ cut {A = A & B} eq (case (ch ⟨ < p₀ ⟩ (P , Q)) ⟨ p ⟩
                                       select (ch ⟨ < q₀ ⟩ inj₂ R)) ↝
                    cut (≈after⊕R eq) (Q ⟨ p ⟩ R) ⊣ ≈c-refl
  r-fork      : ∀{Γ₁ Γ₂ Γ₃ Δ A B P Q R} (eq : (dual A ⊗ dual B) ≈ (dual A ⊗ dual B))
                (p : Γ ≃ Γ₁ + Δ) (p₀ : Γ₁ ≃ [] + Γ₁) (q : Δ ≃ Γ₂ + Γ₃) (q₀ : Δ ≃ [] + Δ) →
                let _ , p' , q' = +-assoc-r p q in
                ℙ ⊢ cut {A = A ⅋ B} eq (join (ch ⟨ < p₀ ⟩ P) ⟨ p ⟩ fork (ch ⟨ < q₀ ⟩ (Q ⟨ q ⟩ R))) ↝
                    cut (≈after⊗R eq) (cut (≈after⊗L eq) (P ⟨ < p' ⟩ Q) ⟨ q' ⟩ R) ⊣ ≈c-refl
  r-cut        : ∀{Γ₁ Γ₂ A B A' Γ₁' P R Q} (eq : dual A ≈ B) (eqA : A ≈ A') (eqC : Γ₁ ≈c Γ₁')
                 (p : Γ ≃ Γ₁ + Γ₂) →
                 let _ , p' , eq'' = +≈ p eqC in
                 ℙ ⊢ P ↝ Q ⊣ (eqA ∷ eqC) →
                 ℙ ⊢ cut {A = A} eq (P ⟨ p ⟩ R) ↝ cut (≈trans (≈sym (≈dual eqA)) eq) (Q ⟨ p' ⟩ R) ⊣ eq''
  r-cong       : ∀{Δ P R Q} (eq : Γ ≈c Δ) → P ⊒ R → ℙ ⊢ R ↝ Q ⊣ eq → ℙ ⊢ P ↝ Q ⊣ eq
