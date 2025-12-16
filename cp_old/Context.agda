{-# OPTIONS --rewriting #-}
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)

open import Type

Context : Set
Context = List Type

infix 4 _≃_+_ _∋_⊳_

data _≃_+_ : Context → Context → Context → Set where
  •   : [] ≃ [] + []
  <_  : ∀{A Γ Δ Θ} → Γ ≃ Δ + Θ → A ∷ Γ ≃ A ∷ Δ + Θ
  >_  : ∀{A Γ Δ Θ} → Γ ≃ Δ + Θ → A ∷ Γ ≃ Δ + A ∷ Θ

_∋_⊳_ : Context → Type → Context → Set
Γ ∋ A ⊳ Δ = Γ ≃ [ A ] + Δ

+-comm : ∀{Γ Δ Θ} → Γ ≃ Δ + Θ → Γ ≃ Θ + Δ
+-comm • = •
+-comm (< p) = > (+-comm p)
+-comm (> p) = < (+-comm p)

++≃+ : ∀{Γ Δ} → Γ ++ Δ ≃ Γ + Δ
++≃+ {[]}    {[]}    = •
++≃+ {[]}    {_ ∷ _} = > ++≃+
++≃+ {_ ∷ _} {_}     = < ++≃+

≫ : ∀{Γ} → Γ ≃ [] + Γ
≫ = ++≃+ {[]}

≪ : ∀{Γ} → Γ ≃ Γ + []
≪ = +-comm ≫

+-assoc-r  : ∀{Γ Δ Θ Δ′ Θ′} → Γ ≃ Δ + Θ → Θ ≃ Δ′ + Θ′ →
             ∃[ Γ′ ] Γ′ ≃ Δ + Δ′ × Γ ≃ Γ′ + Θ′
+-assoc-r • • = [] , • , •
+-assoc-r (< p) q with +-assoc-r p q
... | _ , p′ , q′ = _ , < p′ , < q′
+-assoc-r (> p) (< q) with +-assoc-r p q
... | _ , p′ , q′ = _ , > p′ , < q′
+-assoc-r (> p) (> q) with +-assoc-r p q
... | _ , p′ , q′ = _ , p′ , > q′

+-assoc-l  : ∀{Γ Δ Θ Δ′ Θ′} → Γ ≃ Δ + Θ → Δ ≃ Δ′ + Θ′ →
             ∃[ Γ′ ] Γ′ ≃ Θ′ + Θ × Γ ≃ Δ′ + Γ′
+-assoc-l p q with +-assoc-r (+-comm p) (+-comm q)
... | Δ , r , p′ = Δ , +-comm r , +-comm p′

+-empty-l : ∀{Γ Δ} → Γ ≃ [] + Δ → Γ ≡ Δ
+-empty-l • = refl
+-empty-l (> p) = cong (_ ∷_) (+-empty-l p)

data Un : Context → Set where
  un-[]  : Un []
  un-∷   : ∀{A Γ} → Un Γ → Un (`? A ∷ Γ)

+-un : ∀{Γ Γ₁ Γ₂} → Γ ≃ Γ₁ + Γ₂ → Un Γ₁ → Un Γ₂ → Un Γ
+-un • un-[] un-[] = un-[]
+-un (< p) (un-∷ un₁) un₂ = un-∷ (+-un p un₁ un₂)
+-un (> p) un₁ (un-∷ un₂) = un-∷ (+-un p un₁ un₂)
