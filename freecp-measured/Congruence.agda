{-# OPTIONS --rewriting --guardedness #-}
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Nat using (ℕ; suc; _+_)
import Data.Nat.Properties as Nat using (+-comm; +-assoc)
open import Data.List.Base using ([]; _∷_; [_])
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong₂)

open import Type
open import Equivalence
open import Context
open import Permutations
open import Process

ugly-assoc : (a b c d : ℕ) → a ≡ c + d → a + b ≡ (c + b) + d
ugly-assoc a b c d refl
  rewrite Nat.+-assoc c d b | Nat.+-comm d b | Eq.sym (Nat.+-assoc c b d) = refl

data _⊒_ {n Σ Γ} : ∀{μ ν} → Proc {n} Σ μ Γ → Proc Σ ν Γ → Set where
  s-comm :
    ∀{A B μ ν Γ₁ Γ₂}{P : Proc Σ μ (A ∷ Γ₁)} {Q : Proc Σ ν (B ∷ Γ₂)}
    (eq : dual A ≈ B) (p : Γ ≃ Γ₁ + Γ₂) →
    cut eq (P ⟨ p ⟩ Q) ⊒ cut (≈sym (≈dual eq)) (Q ⟨ +-comm p ⟩ P)
  s-link :
    ∀{A B μ} (eq : dual A ≈ B) (p : Γ ≃ [ A ] + [ B ]) →
    link {μ = μ} eq (ch ⟨ p ⟩ ch) ⊒ link {μ = μ} (≈sym (≈dual eq)) (ch ⟨ +-comm p ⟩ ch)
  s-fail :
    ∀{A B μ ν Γ₁ Γ₂ Δ} {P : Proc Σ ν (B ∷ Γ₂)}
    (eq : dual A ≈ B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ ⊤ ] + Δ) →
    let _ , _ , q′ = +-assoc-l p q in
    cut {_} {_} {A} eq (fail {μ = μ} (ch ⟨ > q ⟩ tt) ⟨ p ⟩ P) ⊒ fail {μ = μ + ν} (ch ⟨ q′ ⟩ tt)
  s-wait :
    ∀{Γ₁ Γ₂ Δ A B μ ν}{P : Proc Σ μ (A ∷ Δ)} {Q : Proc Σ ν (B ∷ Γ₂)}
    (eq : dual A ≈ B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ ⊥ ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut eq (wait (ch ⟨ > q ⟩ P) ⟨ p ⟩ Q) ⊒ wait (ch ⟨ q′ ⟩ cut eq (P ⟨ p′ ⟩ Q))
  s-case :
    ∀{A A' B C Γ₁ Γ₂ Δ μ ν} {P : Proc Σ μ (B ∷ A ∷ Δ)} {Q : Proc Σ μ (C ∷ A ∷ Δ)} {R : Proc Σ ν (A' ∷ Γ₂)}
    (eq : dual A ≈ A') (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ B & C ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut eq (case (ch ⟨ > q ⟩ (P , Q)) ⟨ p ⟩ R) ⊒
    case (ch ⟨ q′ ⟩ (cut eq (↭proc swap P ⟨ < p′ ⟩ R) ,
                     cut eq (↭proc swap Q ⟨ < p′ ⟩ R)))
  s-select-l :
    ∀{Γ₁ Γ₂ Δ A A' B C μ ν} {P : Proc Σ μ (B ∷ A ∷ Δ)} {Q : Proc Σ ν (A' ∷ Γ₂)}
    (eq : dual A ≈ A') (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ B ⊕ C ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut eq (select (ch ⟨ > q ⟩ inj₁ P) ⟨ p ⟩ Q) ⊒
    select (ch ⟨ q′ ⟩ inj₁ (cut eq (↭proc swap P ⟨ < p′ ⟩ Q)))
  s-select-r :
    ∀{Γ₁ Γ₂ Δ A A' B C μ ν} {P : Proc Σ μ (C ∷ A ∷ Δ)} {Q : Proc Σ ν (A' ∷ Γ₂)}
    (eq : dual A ≈ A') (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ B ⊕ C ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut eq (select (ch ⟨ > q ⟩ inj₂ P) ⟨ p ⟩ Q) ⊒
    select (ch ⟨ q′ ⟩ inj₂ (cut eq (↭proc swap P ⟨ < p′ ⟩ Q)))
  s-join :
    ∀{Γ₁ Γ₂ Δ A A' B C μ ν} {P : Proc Σ μ (B ∷ C ∷ A ∷ Δ)} {Q : Proc Σ ν (A' ∷ Γ₂)}
    (eq : dual A ≈ A') (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ B ⅋ C ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut eq (join (ch ⟨ > q ⟩ P) ⟨ p ⟩ Q) ⊒
    join (ch ⟨ q′ ⟩ cut eq (↭proc (↭shift {_} {A} {B ∷ C ∷ []}) P ⟨ < < p′ ⟩ Q))
  s-fork-l :
    ∀{Γ₁ Γ₂ Δ Δ₁ Δ₂ A A' B C μ ν ω} {P : Proc Σ μ (B ∷ A ∷ Δ₁)} {Q : Proc Σ ν (C ∷ Δ₂)} {R : Proc Σ ω (A' ∷ Γ₂)}
    (eq : dual A ≈ A') (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ B ⊗ C ] + Δ) (r : Δ ≃ Δ₁ + Δ₂) →
    let _ , p′ , q′ = +-assoc-l p q in
    let _ , p′′ , r′ = +-assoc-l p′ r in
    let _ , q′′ , r′′ = +-assoc-r r′ (+-comm p′′) in
    cut eq (fork (ch ⟨ > q ⟩ (P ⟨ < r ⟩ Q)) ⟨ p ⟩ R) ⊒
    fork (ch ⟨ q′ ⟩ (cut eq (↭proc swap P ⟨ < q′′ ⟩ R) ⟨ r′′ ⟩ Q))
  s-fork-r :
    ∀{Γ₁ Γ₂ Δ Δ₁ Δ₂ A A' B C μ ν ω} {P : Proc Σ μ (B ∷ Δ₁)} {Q : Proc Σ ν (C ∷ A ∷ Δ₂)} {R : Proc Σ ω (A' ∷ Γ₂)}
    (eq : dual A ≈ A') (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ B ⊗ C ] + Δ) (r : Δ ≃ Δ₁ + Δ₂) →
    let _ , p′ , q′ = +-assoc-l p q in
    let _ , p′′ , r′ = +-assoc-l p′ r in
    cut {A = A} {A'} eq (fork (ch ⟨ > q ⟩ (P ⟨ > r ⟩ Q)) ⟨ p ⟩ R) ⊒
    fork (ch ⟨ q′ ⟩ (P ⟨ r′ ⟩ cut eq (↭proc swap Q ⟨ < p′′ ⟩ R)))
  s-put :
    ∀{Γ₁ Γ₂ Δ A A' B μ ν ω} {P : Proc Σ μ (B ∷ A ∷ Δ)} {Q : Proc Σ ν (A' ∷ Γ₂)}
    (eq : dual A ≈ A') (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ ω ⊲ B ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut eq (put (ch ⟨ > q ⟩ P) ⟨ p ⟩ Q) ⊒
    put (ch ⟨ q′ ⟩ (cut eq (↭proc swap P ⟨ < p′ ⟩ Q)))
  s-get :
    ∀{Γ₁ Γ₂ Δ A A' B μ₁ μ₂ ν ω} {P : Proc Σ μ₁ (B ∷ A ∷ Δ)} {Q : Proc Σ μ₂ (A' ∷ Γ₂)}
    (eq : dual A ≈ A') (eq' : μ₁ ≡ ν + ω) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ ω ⊳ B ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {μ = ν} eq (get eq' (ch ⟨ > q ⟩ P) ⟨ p ⟩ Q) ⊒
    get (ugly-assoc μ₁ μ₂ ν ω eq') (ch ⟨ q′ ⟩ cut eq (↭proc swap P ⟨ < p′ ⟩ Q))
  s-refl  : ∀{μ} {P : Proc Σ μ Γ} → P ⊒ P
  s-tran  : ∀{μ ν ω} {P : Proc Σ μ Γ} {Q : Proc Σ ν Γ} {R : Proc Σ ω Γ} → P ⊒ Q → Q ⊒ R → P ⊒ R
  s-cong  : ∀{Γ₁ Γ₂ A A' μ μ' ν ν'} {P : Proc Σ μ (A ∷ Γ₁)} {Q : Proc Σ ν (A ∷ Γ₁)} {P′ : Proc Σ μ' (A' ∷ Γ₂)} {Q′ : Proc Σ ν' (A' ∷ Γ₂)}
            (eq : dual A ≈ A') (p : Γ ≃ Γ₁ + Γ₂) →
            P ⊒ Q → P′ ⊒ Q′ → cut eq (P ⟨ p ⟩ P′) ⊒ cut eq (Q ⟨ p ⟩ Q′)

⊒size : ∀{n Σ μ ν Γ} {P : Proc {n} Σ μ Γ} {Q : Proc Σ ν Γ} → P ⊒ Q → ν ≡ μ
⊒size (s-comm {μ = μ} {ν} eq p) = Nat.+-comm ν μ
⊒size (s-link eq p) = refl
⊒size (s-fail eq p q) = refl
⊒size (s-wait eq p q) = refl
⊒size (s-case eq p q) = refl
⊒size (s-select-l eq p q) = refl
⊒size (s-select-r eq p q) = refl
⊒size (s-join eq p q) = refl
⊒size (s-fork-l {μ = μ} {ν} {ω} eq p q r)
  rewrite Nat.+-assoc μ ν ω | Nat.+-comm ν ω | Eq.sym (Nat.+-assoc μ ω ν) = refl
⊒size (s-fork-r {μ = μ} {ν} {ω} eq p q r) rewrite Nat.+-assoc μ ν ω = refl
⊒size (s-put {μ = μ} {ν} {ω} eq p q)
  rewrite Nat.+-assoc μ ν ω | Nat.+-comm ν ω | Eq.sym (Nat.+-assoc μ ω ν) = refl
⊒size (s-get eq eq' p q) = refl
⊒size s-refl = refl
⊒size (s-tran pc pc') rewrite ⊒size pc' = ⊒size pc
⊒size (s-cong eq p pc pc') = cong₂ _+_ (⊒size pc) (⊒size pc')
