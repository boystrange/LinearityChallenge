{-# OPTIONS --rewriting #-}
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Type

Context : Set
Context = List Type

infix  4 _≃_+_
infixr 8 _─∗_
infixr 9 _∗_

data _≃_+_ : Context → Context → Context → Set where
  •   : [] ≃ [] + []
  <_  : ∀{A Γ Δ Θ} → Γ ≃ Δ + Θ → A ∷ Γ ≃ A ∷ Δ + Θ
  >_  : ∀{A Γ Δ Θ} → Γ ≃ Δ + Θ → A ∷ Γ ≃ Δ + A ∷ Θ

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

data _∗_ (P Q : Pred Context _) (Γ : Context) : Set where
  _⟨_⟩_ : ∀{Δ Θ} → P Δ → Γ ≃ Δ + Θ → Q Θ → (P ∗ Q) Γ

∗-comm : ∀{P Q} → ∀[ P ∗ Q ⇒ Q ∗ P ]
∗-comm (p ⟨ σ ⟩ q) = q ⟨ +-comm σ ⟩ p

∗-assoc-l : ∀{P Q R} → ∀[ (P ∗ Q) ∗ R ⇒ P ∗ (Q ∗ R) ]
∗-assoc-l ((p ⟨ σ ⟩ q) ⟨ ρ ⟩ r) with +-assoc-l ρ σ
... | _ , σ' , ρ' = p ⟨ ρ' ⟩ (q ⟨ σ' ⟩ r)

_─∗_ : Pred Context _ → Pred Context _ → Context → Set
(P ─∗ Q) Δ = ∀{Θ Γ} → Γ ≃ Δ + Θ → P Θ → Q Γ

curry∗ : ∀{P Q R} → ∀[ P ∗ Q ⇒ R ] → ∀[ P ⇒ Q ─∗ R ]
curry∗ F px σ qx = F (px ⟨ σ ⟩ qx)

data Un : Context → Set where
  un-[]  : Un []
  un-∷   : ∀{A} → ∀[ Un ⇒ (`? A ∷_) ⊢ Un ]

∗-un : ∀[ Un ∗ Un ⇒ Un ]
∗-un (un-[] ⟨ • ⟩ un-[]) = un-[]
∗-un (un-∷ un ⟨ < σ ⟩ un′) = un-∷ (∗-un (un ⟨ σ ⟩ un′))
∗-un (un ⟨ > σ ⟩ un-∷ un′) = un-∷ (∗-un (un ⟨ σ ⟩ un′))
