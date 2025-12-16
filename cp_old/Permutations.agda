{-# OPTIONS --rewriting #-}
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)

open import Type
open import Context

data _↭_ : Context → Context → Set where
  refl   : ∀{Γ} → Γ ↭ Γ
  swap   : ∀{A B Γ} → (A ∷ B ∷ Γ) ↭ (B ∷ A ∷ Γ)
  prep   : ∀{A Γ Δ} → Γ ↭ Δ → (A ∷ Γ) ↭ (A ∷ Δ)
  trans  : ∀{Γ Δ Θ} → Γ ↭ Δ → Δ ↭ Θ → Γ ↭ Θ

↭sym : ∀{Γ Δ} → Γ ↭ Δ → Δ ↭ Γ
↭sym refl = refl
↭sym swap = swap
↭sym (prep π) = prep (↭sym π)
↭sym (trans π π′) = trans (↭sym π′) (↭sym π)

↭empty-inv : ∀{Γ} → [] ↭ Γ → Γ ≡ []
↭empty-inv refl = refl
↭empty-inv (trans π π′) rewrite ↭empty-inv π | ↭empty-inv π′ = refl

↭solo-inv : ∀{A Γ} → [ A ] ↭ Γ → Γ ≡ [ A ]
↭solo-inv refl = refl
↭solo-inv (prep π) rewrite ↭empty-inv π = refl
↭solo-inv (trans π π′) rewrite ↭solo-inv π | ↭solo-inv π′ = refl

↭split : ∀{Γ Γ₁ Γ₂ Δ} → Γ ↭ Δ → Γ ≃ Γ₁ + Γ₂ → ∃[ Δ₁ ] ∃[ Δ₂ ] (Δ ≃ Δ₁ + Δ₂ × Γ₁ ↭ Δ₁ × Γ₂ ↭ Δ₂)
↭split refl p = _ , _ , p , refl , refl
↭split (prep π) (< p) with ↭split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = _ ∷ Δ₁ , Δ₂ , < q , prep π₁ , π₂
↭split (prep π) (> p) with ↭split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = Δ₁ , _ ∷ Δ₂ , > q , π₁ , prep π₂
↭split swap (< < p) = _ , _ , < < p , swap , refl
↭split swap (< > p) = _ , _ , > < p , refl , refl
↭split swap (> < p) = _ , _ , < > p , refl , refl
↭split swap (> > p) = _ , _ , > > p , refl , swap
↭split (trans π π′) p with ↭split π p
... | Θ₁ , Θ₂ , p′ , π₁ , π₂ with ↭split π′ p′
... | Δ₁ , Δ₂ , q , π₁′ , π₂′ = Δ₁ , Δ₂ , q , trans π₁ π₁′ , trans π₂ π₂′

↭solo : ∀{A Γ Γ′ Δ} → Γ ↭ Δ → Γ ∋ A ⊳ Γ′ → ∃[ Δ′ ] (Δ ∋ A ⊳ Δ′ × Γ′ ↭ Δ′)
↭solo π p with ↭split π p
... | _ , _ , q , π₁ , π₂ rewrite ↭solo-inv π₁ = _ , q , π₂

↭shift : ∀{A Γ Δ} → (Γ ++ A ∷ Δ) ↭ (A ∷ Γ ++ Δ)
↭shift {_} {[]} = refl
↭shift {_} {_ ∷ _} = trans (prep ↭shift) swap

↭concat : ∀{Γ Γ₁ Γ₂} → Γ ≃ Γ₁ + Γ₂ → (Γ₁ ++ Γ₂) ↭ Γ
↭concat • = refl
↭concat (< p) = prep (↭concat p)
↭concat (> p) = trans ↭shift (prep (↭concat p))

↭left : ∀{Γ Δ Θ} → Γ ↭ Δ → (Θ ++ Γ) ↭ (Θ ++ Δ)
↭left {Θ = []} π = π
↭left {Θ = _ ∷ _} π = prep (↭left π)

↭un : ∀{Γ Δ} → Γ ↭ Δ → Un Γ → Un Δ
↭un refl un = un
↭un (prep π) (un-∷ un) = un-∷ (↭un π un)
↭un swap (un-∷ (un-∷ un)) = un-∷ (un-∷ un)
↭un (trans π π′) un = ↭un π′ (↭un π un)
