{-# OPTIONS --rewriting --guardedness #-}
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
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

data _⊢_↝_ {Σ} {Γ} (ℙ : Def Σ) : Proc Σ Γ → Proc Σ Γ → Set where
  r-call      : ∀{T} (x : T ∈ Σ) (π : T .context ↭ Γ) → ℙ ⊢ call x π ↝ ↭proc π (lookup ℙ x)
  r-link      : ∀{Δ A A' P} (eq eq' : dual A' ≅ A) (p : Γ ≃ [ A ] + Δ) →
                ℙ ⊢ cut {A = A'} {A} eq (link eq' (ch ⟨ < > • ⟩ ch) ⟨ p ⟩ P) ↝ ↭proc (↭concat p) P
  r-close     : ∀{P} (eq : 𝟙 ≅ 𝟙) (p : Γ ≃ Γ + []) (p₀ : Γ ≃ [] + Γ) →
                ℙ ⊢ cut eq (wait (ch ⟨ < p₀ ⟩ P) ⟨ p ⟩ close ch) ↝ P
  r-select-l  : ∀{Γ₁ Γ₂ A B P Q R} (eq : (dual A ⊕ dual B) ≅ (dual A ⊕ dual B))
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                ℙ ⊢ cut {A = A & B} eq (case (ch ⟨ < p₀ ⟩ (P , Q)) ⟨ p ⟩
                                       select (ch ⟨ < q₀ ⟩ inj₁ R)) ↝ cut (≅after eq ⊕L ⊕L) (P ⟨ p ⟩ R)
  r-select-r  : ∀{Γ₁ Γ₂ A B P Q R} (eq : (dual A ⊕ dual B) ≅ (dual A ⊕ dual B))
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                ℙ ⊢ cut {A = A & B} eq (case (ch ⟨ < p₀ ⟩ (P , Q)) ⟨ p ⟩
                                       select (ch ⟨ < q₀ ⟩ inj₂ R)) ↝ cut (≅after eq ⊕R ⊕R) (Q ⟨ p ⟩ R)
  r-fork      : ∀{Γ₁ Γ₂ Γ₃ Δ A B P Q R} (eq : (dual A ⊗ dual B) ≅ (dual A ⊗ dual B))
                (p : Γ ≃ Γ₁ + Δ) (p₀ : Γ₁ ≃ [] + Γ₁) (q : Δ ≃ Γ₂ + Γ₃) (q₀ : Δ ≃ [] + Δ) →
                let _ , p' , q' = +-assoc-r p q in
                ℙ ⊢ cut {A = A ⅋ B} eq (join (ch ⟨ < p₀ ⟩ P) ⟨ p ⟩ fork (ch ⟨ < q₀ ⟩ (Q ⟨ q ⟩ R))) ↝
                    cut (≅after eq ⊗R ⊗R) (cut (≅after eq ⊗L ⊗L) (P ⟨ < p' ⟩ Q) ⟨ q' ⟩ R)
  r-cong       : ∀{P R Q} → P ⊒ R → ℙ ⊢ R ↝ Q → ℙ ⊢ P ↝ Q
