{-# OPTIONS --rewriting #-}
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.List.Base using (List; []; _∷_; [_]; _++_; map)

open import Type

Context : Set
Context = List Type

infix 4 _≃_+_ _≃_,_

data _≃_+_ : Context → Context → Context → Set where
  •   : [] ≃ [] + []
  <_  : ∀{A Γ Δ Θ} → Γ ≃ Δ + Θ → A ∷ Γ ≃ A ∷ Δ + Θ
  >_  : ∀{A Γ Δ Θ} → Γ ≃ Δ + Θ → A ∷ Γ ≃ Δ + A ∷ Θ

_≃_,_ : Context → Type → Context → Set
Γ ≃ A , Δ = Γ ≃ [ A ] + Δ

+-comm : ∀{Γ Δ Θ} → Γ ≃ Δ + Θ → Γ ≃ Θ + Δ
+-comm • = •
+-comm (< p) = > (+-comm p)
+-comm (> p) = < (+-comm p)

≫ : ∀{Γ} → Γ ≃ [] + Γ
≫ {[]}    = •
≫ {_ ∷ _} = > ≫

≪ : ∀{Γ} → Γ ≃ Γ + []
≪ = +-comm ≫

++≃+ : ∀{Γ Δ} → Γ ++ Δ ≃ Γ + Δ
++≃+ {[]}    = ≫
++≃+ {_ ∷ _} = < ++≃+

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

+-sing-l : ∀{A B Γ} → [ A ] ≃ B , Γ → A ≡ B × Γ ≡ []
+-sing-l (< •) = refl , refl

data Un : Context → Set where
  un-[]  : Un []
  un-∷   : ∀{A Γ} → Un Γ → Un (`? A ∷ Γ)
