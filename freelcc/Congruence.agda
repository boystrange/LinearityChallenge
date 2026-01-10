{-# OPTIONS --rewriting --guardedness #-}
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.List.Base using ([]; _∷_; [_])

open import Type
open import Equivalence
open import Context
open import Permutations
open import Process

data _⊒_ {n Σ Γ} : Proc {n} Σ Γ → Proc Σ Γ → Set where
  s-comm :
    ∀{A B Γ₁ Γ₂ P Q} (eq : dual A ≈ B) (p : Γ ≃ Γ₁ + Γ₂) →
    cut eq (P ⟨ p ⟩ Q) ⊒ cut (≈sym (≈dual eq)) (Q ⟨ +-comm p ⟩ P)
  s-link :
    ∀{A B} (eq : dual A ≈ B) (p : Γ ≃ [ A ] + [ B ]) →
    link eq (ch ⟨ p ⟩ ch) ⊒ link (≈sym (≈dual eq)) (ch ⟨ +-comm p ⟩ ch)
  s-fail :
    ∀{A B Γ₁ Γ₂ Δ P} (eq : dual A ≈ B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ ⊤ ] + Δ) →
    let _ , _ , q′ = +-assoc-l p q in
    cut {_} {_} {A} {B} eq (fail (ch ⟨ > q ⟩ tt) ⟨ p ⟩ P) ⊒ fail (ch ⟨ q′ ⟩ tt)
  s-wait :
    ∀{Γ₁ Γ₂ Δ A B P Q} (eq : dual A ≈ B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ ⊥ ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A = A} {B} eq (wait (ch ⟨ > q ⟩ P) ⟨ p ⟩ Q) ⊒ wait (ch ⟨ q′ ⟩ cut eq (P ⟨ p′ ⟩ Q))
  s-case :
    ∀{A A' B C Γ₁ Γ₂ Δ P Q R} (eq : dual A ≈ A') (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ B & C ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A = A} {A'} eq (case (ch ⟨ > q ⟩ (P , Q)) ⟨ p ⟩ R) ⊒
    case (ch ⟨ q′ ⟩ (cut eq (↭proc swap P ⟨ < p′ ⟩ R) ,
                     cut eq (↭proc swap Q ⟨ < p′ ⟩ R)))
  s-select-l :
    ∀{Γ₁ Γ₂ Δ A A' B C P Q} (eq : dual A ≈ A') (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ B ⊕ C ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A = A} {A'} eq (select (ch ⟨ > q ⟩ inj₁ P) ⟨ p ⟩ Q) ⊒
    select (ch ⟨ q′ ⟩ inj₁ (cut eq (↭proc swap P ⟨ < p′ ⟩ Q)))
  s-select-r :
    ∀{Γ₁ Γ₂ Δ A A' B C P Q} (eq : dual A ≈ A') (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ B ⊕ C ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A = A} {A'} eq (select (ch ⟨ > q ⟩ inj₂ P) ⟨ p ⟩ Q) ⊒
    select (ch ⟨ q′ ⟩ inj₂ (cut eq (↭proc swap P ⟨ < p′ ⟩ Q)))
  s-join :
    ∀{Γ₁ Γ₂ Δ A A' B C P Q} (eq : dual A ≈ A') (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ B ⅋ C ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A = A} {A'} eq (join (ch ⟨ > q ⟩ P) ⟨ p ⟩ Q) ⊒
    join (ch ⟨ q′ ⟩ cut eq (↭proc (↭shift {_} {A} {B ∷ C ∷ []}) P ⟨ < < p′ ⟩ Q))
  s-fork-l :
    ∀{Γ₁ Γ₂ Δ Δ₁ Δ₂ A A' B C P Q R}
    (eq : dual A ≈ A') (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ B ⊗ C ] + Δ) (r : Δ ≃ Δ₁ + Δ₂) →
    let _ , p′ , q′ = +-assoc-l p q in
    let _ , p′′ , r′ = +-assoc-l p′ r in
    let _ , q′′ , r′′ = +-assoc-r r′ (+-comm p′′) in
    cut {A = A} {A'} eq (fork (ch ⟨ > q ⟩ (P ⟨ < r ⟩ Q)) ⟨ p ⟩ R) ⊒
    fork (ch ⟨ q′ ⟩ (cut eq (↭proc swap P ⟨ < q′′ ⟩ R) ⟨ r′′ ⟩ Q))
  s-fork-r :
    ∀{Γ₁ Γ₂ Δ Δ₁ Δ₂ A A' B C P Q R} (eq : dual A ≈ A')
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ B ⊗ C ] + Δ) (r : Δ ≃ Δ₁ + Δ₂) →
    let _ , p′ , q′ = +-assoc-l p q in
    let _ , p′′ , r′ = +-assoc-l p′ r in
    cut {A = A} {A'} eq (fork (ch ⟨ > q ⟩ (P ⟨ > r ⟩ Q)) ⟨ p ⟩ R) ⊒
    fork (ch ⟨ q′ ⟩ (P ⟨ r′ ⟩ cut eq (↭proc swap Q ⟨ < p′′ ⟩ R)))
  s-refl  : ∀{P} → P ⊒ P
  s-tran  : ∀{P Q R} → P ⊒ Q → Q ⊒ R → P ⊒ R
  s-cong  : ∀{Γ₁ Γ₂ A A' P Q P′ Q′} (eq : dual A ≈ A') (p : Γ ≃ Γ₁ + Γ₂) →
            P ⊒ Q → P′ ⊒ Q′ → cut {A = A} {A'} eq (P ⟨ p ⟩ P′) ⊒ cut eq (Q ⟨ p ⟩ Q′)
