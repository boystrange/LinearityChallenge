{-# OPTIONS --rewriting #-}
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.List.Base using ([]; _∷_; [_])

open import Type
open import Context
open import Permutations
open import Process

data _⊒_ {Γ} : Proc Γ → Proc Γ → Set where
  s-comm :
    ∀{A Γ₁ Γ₂ P Q} (p : Γ ≃ Γ₁ + Γ₂) →
    cut {A} (P ⟨ p ⟩ Q) ⊒ cut (Q ⟨ +-comm p ⟩ P)
  s-link :
    ∀{A} (p : Γ ≃ [ A ] + [ dual A ]) →
    link (ch ⟨ p ⟩ ch) ⊒ link (ch ⟨ +-comm p ⟩ ch)
  s-fail :
    ∀{A Γ₁ Γ₂ Δ P} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ ⊤ ] + Δ) →
    let _ , _ , q′ = +-assoc-l p q in
    cut {A} (fail (ch ⟨ > q ⟩ tt) ⟨ p ⟩ P) ⊒ fail (ch ⟨ q′ ⟩ tt)
  s-wait :
    ∀{Γ₁ Γ₂ Δ A P Q} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ ⊥ ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A} (wait (ch ⟨ > q ⟩ P) ⟨ p ⟩ Q) ⊒ wait (ch ⟨ q′ ⟩ cut (P ⟨ p′ ⟩ Q))
  s-case :
    ∀{A B C Γ₁ Γ₂ Δ P Q R} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ B & C ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A} (case (ch ⟨ > q ⟩ (P , Q)) ⟨ p ⟩ R) ⊒
    case (ch ⟨ q′ ⟩ (cut (↭proc swap P ⟨ < p′ ⟩ R) ,
                     cut (↭proc swap Q ⟨ < p′ ⟩ R)))
  s-select-l :
    ∀{Γ₁ Γ₂ Δ A B C P Q} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ B ⊕ C ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A} (select (ch ⟨ > q ⟩ inj₁ P) ⟨ p ⟩ Q) ⊒
    select (ch ⟨ q′ ⟩ inj₁ (cut (↭proc swap P ⟨ < p′ ⟩ Q)))
  s-select-r :
    ∀{Γ₁ Γ₂ Δ A B C P Q} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ B ⊕ C ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A} (select (ch ⟨ > q ⟩ inj₂ P) ⟨ p ⟩ Q) ⊒
    select (ch ⟨ q′ ⟩ inj₂ (cut (↭proc swap P ⟨ < p′ ⟩ Q)))
  s-join :
    ∀{Γ₁ Γ₂ Δ A B C P Q} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ B ⅋ C ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A} (join (ch ⟨ > q ⟩ P) ⟨ p ⟩ Q) ⊒
    join (ch ⟨ q′ ⟩ cut (↭proc (↭shift {A} {C ∷ B ∷ []}) P ⟨ < < p′ ⟩ Q))
  s-fork-l :
    ∀{Γ₁ Γ₂ Δ Δ₁ Δ₂ A B C P Q R}
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ B ⊗ C ] + Δ) (r : Δ ≃ Δ₁ + Δ₂) →
    let _ , p′ , q′ = +-assoc-l p q in
    let _ , p′′ , r′ = +-assoc-l p′ r in
    let _ , q′′ , r′′ = +-assoc-r r′ (+-comm p′′) in
    cut {A} (fork (ch ⟨ > q ⟩ (P ⟨ < r ⟩ Q)) ⟨ p ⟩ R) ⊒
    fork (ch ⟨ q′ ⟩ (cut (↭proc swap P ⟨ < q′′ ⟩ R) ⟨ r′′ ⟩ Q))
  s-fork-r :
    ∀{Γ₁ Γ₂ Δ Δ₁ Δ₂ A B C P Q R}
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ B ⊗ C ] + Δ) (r : Δ ≃ Δ₁ + Δ₂) →
    let _ , p′ , q′ = +-assoc-l p q in
    let _ , p′′ , r′ = +-assoc-l p′ r in
    cut {A} (fork (ch ⟨ > q ⟩ (P ⟨ > r ⟩ Q)) ⟨ p ⟩ R) ⊒
    fork (ch ⟨ q′ ⟩ (P ⟨ r′ ⟩ cut (↭proc swap Q ⟨ < p′′ ⟩ R)))
  s-all :
    ∀{A B Γ₁ Γ₂ Δ F Q} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ `∀ B ] + Δ) ->
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A} (all (ch ⟨ > q ⟩ F) ⟨ p ⟩ Q) ⊒
    all (ch ⟨ q′ ⟩ λ X → cut (↭proc swap (F X) ⟨ (< p′) ⟩ Q))
  s-ex :
    ∀{A B C Γ₁ Γ₂ Δ P Q} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ `∃ B ] + Δ) ->
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A} (ex {_} {C} (ch ⟨ > q ⟩ P) ⟨ p ⟩ Q) ⊒
    ex (ch ⟨ q′ ⟩ cut (↭proc swap P ⟨ < p′ ⟩ Q))
  s-server :
    ∀{A B Γ₁ Γ₂ Δ₁ P Q}
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ `! B ] + Δ₁) (r : Γ₂ ≃ [] + Γ₂)
    (un₁ : Un Δ₁) (un₂ : Un Γ₂) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {`? A} (server (ch ⟨ > q ⟩ (un-∷ un₁ , P)) ⟨ p ⟩ server (ch ⟨ < r ⟩ (un₂ , Q))) ⊒
    server (ch ⟨ q′ ⟩ (∗-un (un₁ ⟨ p′ ⟩ un₂) , cut (↭proc swap P ⟨ (< p′) ⟩ server (ch ⟨ < r ⟩ (un₂ , Q)))))
  s-client :
    ∀{A B Γ₁ Γ₂ Δ P Q} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ `? B ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A} (client (ch ⟨ > q ⟩ P) ⟨ p ⟩ Q) ⊒
    client (ch ⟨ q′ ⟩ cut (↭proc swap P ⟨ < p′ ⟩ Q))
  s-weaken :
    ∀{A B Γ₁ Γ₂ Δ P Q} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ `? B ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A} (weaken (ch ⟨ (> q) ⟩ P) ⟨ p ⟩ Q) ⊒ weaken (ch ⟨ q′ ⟩ cut (P ⟨ p′ ⟩ Q))
  s-contract :
    ∀{A B Γ₁ Γ₂ Δ P Q} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ `? B ] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A} (contract (ch ⟨ > q ⟩ P) ⟨ p ⟩ Q) ⊒
    contract (ch ⟨ q′ ⟩ cut (↭proc (↭shift {A} {`? B ∷ `? B ∷ []}) P ⟨ < < p′ ⟩ Q))
  s-refl  : ∀{P} → P ⊒ P
  s-tran  : ∀{P Q R} → P ⊒ Q → Q ⊒ R → P ⊒ R
  s-cong  : ∀{Γ₁ Γ₂ A P Q P′ Q′} (p : Γ ≃ Γ₁ + Γ₂) →
            P ⊒ Q → P′ ⊒ Q′ → cut {A} (P ⟨ p ⟩ P′) ⊒ cut (Q ⟨ p ⟩ Q′)
