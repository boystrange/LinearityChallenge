{-# OPTIONS --rewriting #-}
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)

open import Type
open import Context
open import Permutations
open import Process

data _⊒_ {Γ} : Process Γ → Process Γ → Set where
  s-comm :
    ∀{A Γ₁ Γ₂ P Q} (p : Γ ≃ Γ₁ + Γ₂) → cut {A} p P Q ⊒ cut (+-comm p) Q P
  s-link :
    ∀{A} (p : Γ ≃ [ A ] + [ dual A ]) →
    link p ⊒ link (+-comm p)
  s-fail :
    ∀{A Γ₁ Γ₂ Δ P} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ∋ ⊤ ⊳ Δ) →
    let _ , _ , q′ = +-assoc-l p q in
    cut {A} p (fail (> q)) P ⊒ fail q′
  s-wait :
    ∀{Γ₁ Γ₂ Δ A P Q} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ∋ ⊥ ⊳ Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A} p (wait (> q) P) Q ⊒ wait q′ (cut p′ P Q)
  s-case :
    ∀{A B C Γ₁ Γ₂ Δ P Q R} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ∋ B & C ⊳ Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A} p (case (> q) P Q) R ⊒ case q′ (cut (< p′) (↭process swap P) R)
                                           (cut (< p′) (↭process swap Q) R)
  s-left :
    ∀{Γ₁ Γ₂ Δ A B C P Q} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ∋ B ⊕ C ⊳ Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A} p (left (> q) P) Q ⊒ left q′ (cut (< p′) (↭process swap P) Q)
  s-right :
    ∀{Γ₁ Γ₂ Δ A B C P Q} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ∋ B ⊕ C ⊳ Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A} p (right (> q) P) Q ⊒ right q′ (cut (< p′) (↭process swap P) Q)
  s-join :
    ∀{Γ₁ Γ₂ Δ A B C P Q} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ∋ B ⅋ C ⊳ Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A} p (join (> q) P) Q ⊒
    join q′ (cut (< < p′) (↭process (↭shift {A} {C ∷ B ∷ []}) P) Q)
  s-fork-l :
    ∀{Γ₁ Γ₂ Δ Δ₁ Δ₂ A B C P Q R}
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ∋ B ⊗ C ⊳ Δ) (r : Δ ≃ Δ₁ + Δ₂) →
    let _ , p′ , q′ = +-assoc-l p q in
    let _ , p′′ , r′ = +-assoc-l p′ r in
    let _ , q′′ , r′′ = +-assoc-r r′ (+-comm p′′) in
    cut {A} p (fork (> q) (< r) P Q) R ⊒
    fork q′ r′′ (cut (< q′′) (↭process swap P) R) Q
  s-fork-r :
    ∀{Γ₁ Γ₂ Δ Δ₁ Δ₂ A B C P Q R}
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ∋ B ⊗ C ⊳ Δ) (r : Δ ≃ Δ₁ + Δ₂) →
    let _ , p′ , q′ = +-assoc-l p q in
    let _ , p′′ , r′ = +-assoc-l p′ r in
    cut {A} p (fork (> q) (> r) P Q) R ⊒
    fork q′ r′ P (cut (< p′′) (↭process swap Q) R)
  s-all :
    ∀{A B Γ₁ Γ₂ Δ F Q} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ∋ `∀ B ⊳ Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    cut {A} p (all (> q) F) Q ⊒ all q' λ σ → cut (< p') (↭process swap (F σ)) Q
  s-ex :
    ∀{A B C Γ₁ Γ₂ Δ P Q} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ∋ `∃ B ⊳ Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    cut {A} p (ex {_} {C} (> q) P) Q ⊒ ex q' (cut (< p') (↭process swap P) Q)
  s-server :
    ∀{A B Γ₁ Γ₂ Δ₁ P Q}
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ∋ `! B ⊳ Δ₁) (r : Γ₂ ≃ [] + Γ₂)
    (un₁ : Un Δ₁) (un₂ : Un Γ₂) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {`? A} p (server (> q) (un-∷ un₁) P) (server (< r) un₂ Q) ⊒
    server q′ (+-un p′ un₁ un₂) (cut (< p′) (↭process swap P) (server (< r) un₂ Q))
  s-client :
    ∀{A B Γ₁ Γ₂ Δ P Q} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ∋ `? B ⊳ Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A} p (client (> q) P) Q ⊒ client q′ (cut (< p′) (↭process swap P) Q)
  s-weaken :
    ∀{A B Γ₁ Γ₂ Δ P Q} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ∋ `? B ⊳ Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A} p (weaken (> q) P) Q ⊒ weaken q′ (cut p′ P Q)
  s-contract :
    ∀{A B Γ₁ Γ₂ Δ P Q} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ∋ `? B ⊳ Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut {A} p (contract (> q) P) Q ⊒
    contract q′ (cut (< < p′) (↭process (↭shift {A} {`? B ∷ `? B ∷ []}) P) Q)
  s-refl  : ∀{P} → P ⊒ P
  s-tran  : ∀{P Q R} → P ⊒ Q → Q ⊒ R → P ⊒ R
  s-cong  : ∀{Γ₁ Γ₂ A P Q P′ Q′} (p : Γ ≃ Γ₁ + Γ₂) →
            P ⊒ Q → P′ ⊒ Q′ → cut {A} p P P′ ⊒ cut p Q Q′
