{-# OPTIONS --rewriting #-}
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)

open import Type
open import Context
open import Permutations
open import Process

data _⊒_ : ∀{Γ} → Process Γ → Process Γ → Set where
  s-comm :
    ∀{A Γ Γ₁ Γ₂ P Q} (p : Γ ≃ Γ₁ + Γ₂) →
    cut {A = A} p P Q ⊒ cut (+-comm p) Q P
  s-link :
    ∀{Γ A} (p : Γ ≃ [ A ] + [ dual A ]) →
    link p ⊒ link (+-comm p)
  s-fail :
    ∀{A Γ Γ₁ Γ₂ Δ P} (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ ⊤ , Δ) →
    let _ , _ , q′ = +-assoc-l p q in
    cut {A = A} p (fail (⊳ q)) P ⊒ fail q′
  s-wait :
    ∀{Γ Γ₁ Γ₂ Δ A} {P : Process (A ∷ Δ)} {Q : Process (dual A ∷ Γ₂)}
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ ⊥ , Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut p (wait (⊳ q) P) Q ⊒ wait q′ (cut p′ P Q)
  s-select-l :
    ∀{Γ Γ₁ Γ₂ Δ A B C} {P : Process (B ∷ A ∷ Δ)} {Q : Process (dual A ∷ Γ₂)}
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ B ⊕ C , Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut p (select true (⊳ q) P) Q ⊒
    select true q′ (cut (⊲ p′) (#process #here P) Q)
  s-select-r :
    ∀{Γ Γ₁ Γ₂ Δ A B C} {P : Process (C ∷ A ∷ Δ)} {Q : Process (dual A ∷ Γ₂)}
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ B ⊕ C , Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut p (select false (⊳ q) P) Q ⊒
    select false q′ (cut (⊲ p′) (#process #here P) Q)
  s-case :
    ∀{Γ A B C Γ₁ Γ₂ Δ}
    {P : Process (B ∷ A ∷ Δ)}
    {Q : Process (C ∷ A ∷ Δ)}
    {R : Process (dual A ∷ Γ₂)}
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ B & C , Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut p (case (⊳ q) P Q) R ⊒
    case q′ (cut (⊲ p′) (#process #here P) R)
            (cut (⊲ p′) (#process #here Q) R)
  s-fork-l :
    ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A B C}
    {P : Process (B ∷ A ∷ Δ₁)} {Q : Process (C ∷ Δ₂)} {R : Process (dual A ∷ Γ₂)}
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ B ⊗ C , Δ) (r : Δ ≃ Δ₁ + Δ₂) →
    let _ , p′ , q′ = +-assoc-l p q in
    let _ , p′′ , r′ = +-assoc-l p′ r in
    let _ , q′′ , r′′ = +-assoc-r r′ (+-comm p′′) in
    cut p (fork (⊳ q) (⊲ r) P Q) R ⊒
    fork q′ r′′ (cut (⊲ q′′) (#process #here P) R) Q
  s-fork-r :
    ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A B C}
    {P : Process (B ∷ Δ₁)} {Q : Process (C ∷ A ∷ Δ₂)} {R : Process (dual A ∷ Γ₂)}
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ B ⊗ C , Δ) (r : Δ ≃ Δ₁ + Δ₂) →
    let _ , p′ , q′ = +-assoc-l p q in
    let _ , p′′ , r′ = +-assoc-l p′ r in
    cut p (fork (⊳ q) (⊳ r) P Q) R ⊒
    fork q′ r′ P (cut (⊲ p′′) (#process #here Q) R)
  s-join :
    ∀{Γ Γ₁ Γ₂ Δ A B C}
    {P : Process (C ∷ B ∷ A ∷ Δ)} {Q : Process (dual A ∷ Γ₂)}
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ B ⅋ C , Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut p (join (⊳ q) P) Q ⊒
    join q′ (cut (⊲ ⊲ p′) (#process #rot P) Q)
  s-server :
    ∀{Γ A B Γ₁ Γ₂ Δ₁}
    {P : Process (B ∷ `? A ∷ Δ₁)} {Q : Process (dual A ∷ Γ₂)}
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ `! B , Δ₁) (r : Γ₂ ≃ [] + Γ₂)
    (un₁ : Un Δ₁) (un₂ : Un Γ₂) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut p (server (⊳ q) (un-∷ un₁) P) (server (⊲ r) un₂ Q) ⊒
    server q′ (#un+ p′ un₁ un₂) (cut (⊲ p′) (#process #here P) (server (⊲ r) un₂ Q))
  s-client :
    ∀{Γ A B Γ₁ Γ₂ Δ}
    {P : Process (B ∷ A ∷ Δ)} {Q : Process (dual A ∷ Γ₂)}
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ `? B , Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut p (client (⊳ q) P) Q ⊒ client q′ (cut (⊲ p′) (#process #here P) Q)
  s-weaken :
    ∀{Γ A B Γ₁ Γ₂ Δ}
    {P : Process (A ∷ Δ)} {Q : Process (dual A ∷ Γ₂)}
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ `? B , Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut p (weaken (⊳ q) P) Q ⊒ weaken q′ (cut p′ P Q)
  s-contract :
    ∀{Γ A B Γ₁ Γ₂ Δ}
    {P : Process (`? B ∷ `? B ∷ A ∷ Δ)} {Q : Process (dual A ∷ Γ₂)}
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ `? B , Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut p (contract (⊳ q) P) Q ⊒
    contract q′ (cut (⊲ ⊲ p′) (#process #rot P) Q)
  s-ex :
    ∀{Γ A B C Γ₁ Γ₂ Δ}
    {P : Process (subst [ C /_] B ∷ A ∷ Δ)}
    {Q : Process (dual A ∷ Γ₂)}
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ `∃ B , Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    cut p (ex (⊳ q) P) Q ⊒ ex q' (cut (⊲ p') (#process #here P) Q)
  s-all :
    ∀{Γ A B Γ₁ Γ₂ Δ}
    {F : (C : Type) -> Process (subst [ C /_] B ∷ A ∷ Δ)}
    {Q : Process (dual A ∷ Γ₂)}
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ `∀ B , Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    cut p (all (⊳ q) F) Q ⊒ all q' λ σ → cut (⊲ p') (#process #here (F σ)) Q
  s-refl  : ∀{Γ} {P : Process Γ} → P ⊒ P
  s-tran  : ∀{Γ} {P Q R : Process Γ} → P ⊒ Q → Q ⊒ R → P ⊒ R
  s-cong  : ∀{Γ Γ₁ Γ₂ A} {P Q : Process (A ∷ Γ₁)} {P′ Q′ : Process (dual A ∷ Γ₂)}
            (p : Γ ≃ Γ₁ + Γ₂) → P ⊒ Q → P′ ⊒ Q′ →
            cut p P P′ ⊒ cut p Q Q′
