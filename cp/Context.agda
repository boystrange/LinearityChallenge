{-# OPTIONS --rewriting #-}
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.List.Base using (List; []; _∷_; [_]; _++_; map)

open import Type

Context : Set
Context = List Type

infix 4 _≃_+_ _≃_,_

data _≃_+_ : Context → Context → Context → Set where
  split-e  : [] ≃ [] + []
  split-l  : ∀{A Γ Δ Θ} → Γ ≃ Δ + Θ → A ∷ Γ ≃ A ∷ Δ + Θ
  split-r  : ∀{A Γ Δ Θ} → Γ ≃ Δ + Θ → A ∷ Γ ≃ Δ + A ∷ Θ

_≃_,_ : Context → Type → Context → Set
Γ ≃ A , Δ = Γ ≃ [ A ] + Δ

+-comm : ∀{Γ Δ Θ} → Γ ≃ Δ + Θ → Γ ≃ Θ + Δ
+-comm split-e = split-e
+-comm (split-l p) = split-r (+-comm p)
+-comm (split-r p) = split-l (+-comm p)

+-unit-l : ∀{Γ} → Γ ≃ [] + Γ
+-unit-l {[]} = split-e
+-unit-l {_ ∷ _} = split-r +-unit-l

+-unit-r  : ∀{Γ} → Γ ≃ Γ + []
+-unit-r = +-comm +-unit-l

++≃+ : ∀{Γ Δ} → Γ ++ Δ ≃ Γ + Δ
++≃+ {[]} = +-unit-l
++≃+ {_ ∷ _} = split-l ++≃+

+-assoc-r  : ∀{Γ Δ Θ Δ′ Θ′} → Γ ≃ Δ + Θ → Θ ≃ Δ′ + Θ′ →
             ∃[ Γ′ ] Γ′ ≃ Δ + Δ′ × Γ ≃ Γ′ + Θ′
+-assoc-r split-e split-e = [] , split-e , split-e
+-assoc-r (split-l p) q with +-assoc-r p q
... | _ , p′ , q′ = _ , split-l p′ , split-l q′
+-assoc-r (split-r p) (split-l q) with +-assoc-r p q
... | _ , p′ , q′ = _ , split-r p′ , split-l q′
+-assoc-r (split-r p) (split-r q) with +-assoc-r p q
... | _ , p′ , q′ = _ , p′ , split-r q′

+-assoc-l  : ∀{Γ Δ Θ Δ′ Θ′} → Γ ≃ Δ + Θ → Δ ≃ Δ′ + Θ′ →
             ∃[ Γ′ ] Γ′ ≃ Θ′ + Θ × Γ ≃ Δ′ + Γ′
+-assoc-l p q with +-assoc-r (+-comm p) (+-comm q)
... | Δ , r , p′ = Δ , +-comm r , +-comm p′

+-empty-l : ∀{Γ Δ} → Γ ≃ [] + Δ → Γ ≡ Δ
+-empty-l split-e = refl
+-empty-l (split-r p) = cong (_ ∷_) (+-empty-l p)

+-sing-l : ∀{A B Γ} → [ A ] ≃ B , Γ → A ≡ B × Γ ≡ []
+-sing-l (split-l split-e) = refl , refl

data Un : Context → Set where
  un-[]  : Un []
  un-∷   : ∀{A Γ} → Un Γ → Un (`? A ∷ Γ)
