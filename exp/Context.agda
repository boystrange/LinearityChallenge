open import Data.Product using (_×_; Σ; _,_; ∃; Σ-syntax; ∃-syntax)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; prep; refl; trans; swap; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (shift; ↭-singleton-inv; All-resp-↭)

open import Type

Context : Set
Context = List Type

infix 4 _≃_+_

data _≃_+_ : Context -> Context -> Context -> Set where
  split-e : [] ≃ [] + []
  split-l : ∀{A Γ Δ Θ} -> Γ ≃ Δ + Θ -> A ∷ Γ ≃ A ∷ Δ + Θ
  split-r : ∀{A Γ Δ Θ} -> Γ ≃ Δ + Θ -> A ∷ Γ ≃ Δ + A ∷ Θ

infix 4 _≃_,_

_≃_,_ : Context -> Type -> Context -> Set
Γ ≃ A , Δ = Γ ≃ [ A ] + Δ

+-comm : ∀{Γ Δ Θ} -> Γ ≃ Δ + Θ -> Γ ≃ Θ + Δ
+-comm split-e = split-e
+-comm (split-l p) = split-r (+-comm p)
+-comm (split-r p) = split-l (+-comm p)

+-unit-l : ∀{Γ} -> Γ ≃ [] + Γ
+-unit-l {[]} = split-e
+-unit-l {_ ∷ _} = split-r +-unit-l

+-unit-r : ∀{Γ} -> Γ ≃ Γ + []
+-unit-r = +-comm +-unit-l

++≃+ : ∀{Γ Δ} -> Γ ++ Δ ≃ Γ + Δ
++≃+ {[]} = +-unit-l
++≃+ {_ ∷ _} = split-l ++≃+

+-assoc-r :
  ∀{Γ Δ Θ Δ' Θ'} -> Γ ≃ Δ + Θ -> Θ ≃ Δ' + Θ' -> ∃[ Γ' ] Γ' ≃ Δ + Δ' × Γ ≃ Γ' + Θ'
+-assoc-r split-e split-e = [] , split-e , split-e
+-assoc-r (split-l p) q with +-assoc-r p q
... | _ , p' , q' = _ , split-l p' , split-l q'
+-assoc-r (split-r p) (split-l q) with +-assoc-r p q
... | _ , p' , q' = _ , split-r p' , split-l q'
+-assoc-r (split-r p) (split-r q) with +-assoc-r p q
... | _ , p' , q' = _ , p' , split-r q'

+-assoc-l :
  ∀{Γ Δ Θ Δ' Θ'} -> Γ ≃ Δ + Θ -> Δ ≃ Δ' + Θ' -> ∃[ Γ' ] Γ' ≃ Θ' + Θ × Γ ≃ Δ' + Γ'
+-assoc-l p q with +-assoc-r (+-comm p) (+-comm q)
... | Δ , r , p' = Δ , +-comm r , +-comm p'

+-empty-l : ∀{Γ Δ} -> Γ ≃ [] + Δ -> Γ ≡ Δ
+-empty-l split-e = refl
+-empty-l (split-r p) = Eq.cong (_ ∷_) (+-empty-l p)

+-sing-l : ∀{A B Γ} -> [ A ] ≃ B , Γ -> A ≡ B × Γ ≡ []
+-sing-l (split-l split-e) = refl , refl

_#_ : Context -> Context -> Set
_#_ = _↭_

#here : ∀{A B Γ} -> (A ∷ B ∷ Γ) # (B ∷ A ∷ Γ)
#here = swap _ _ refl

#next : ∀{A Γ Δ} -> Γ # Δ -> (A ∷ Γ) # (A ∷ Δ)
#next = prep _

#rot : ∀{A B C Γ} -> (A ∷ B ∷ C ∷ Γ) # (C ∷ A ∷ B ∷ Γ)
#rot = trans (#next (swap _ _ refl)) (swap _ _ refl)

#cons : ∀{A Γ Δ} -> Γ ≃ A , Δ -> (A ∷ Δ) ↭ Γ
#cons (split-l p) with +-empty-l p
... | refl = refl
#cons (split-r p) = trans (swap _ _ refl) (prep _ (#cons p))

#split : ∀{Γ Γ₁ Γ₂ Δ} -> Γ # Δ -> Γ ≃ Γ₁ + Γ₂ -> ∃[ Δ₁ ] ∃[ Δ₂ ] (Δ ≃ Δ₁ + Δ₂ × Γ₁ # Δ₁ × Γ₂ # Δ₂)
#split refl p = _ , _ , p , refl , refl
#split (prep x π) (split-l p) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = x ∷ Δ₁ , Δ₂ , split-l q , prep x π₁ , π₂
#split (prep x π) (split-r p) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = Δ₁ , x ∷ Δ₂ , split-r q , π₁ , prep x π₂
#split (swap x y π) (split-l (split-l p)) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = y ∷ x ∷ Δ₁ , Δ₂ , split-l (split-l q) , swap x y π₁ , π₂
#split (swap x y π) (split-l (split-r p)) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = x ∷ Δ₁ , y ∷ Δ₂ , split-r (split-l q) , prep x π₁ , prep y π₂
#split (swap x y π) (split-r (split-l p)) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = y ∷ Δ₁ , x ∷ Δ₂ , split-l (split-r q) , prep y π₁ , prep x π₂
#split (swap x y π) (split-r (split-r p)) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = Δ₁ , y ∷ x ∷ Δ₂ , split-r (split-r q) , π₁ , swap x y π₂
#split (trans π π') p with #split π p
... | Θ₁ , Θ₂ , p' , π₁ , π₂ with #split π' p'
... | Δ₁ , Δ₂ , q , π₁' , π₂' = Δ₁ , Δ₂ , q , trans π₁ π₁' , trans π₂ π₂'

#one+ : ∀{A Γ Γ' Δ} -> Γ ↭ Δ -> Γ ≃ A , Γ' -> ∃[ Δ' ] (Δ ≃ A , Δ' × Γ' ↭ Δ')
#one+ π p with #split π p
... | Θ , Δ' , q , π₁ , π₂ rewrite ↭-singleton-inv (↭-sym π₁) = Δ' , q , π₂

+++# : ∀{Γ Γ₁ Γ₂} -> Γ ≃ Γ₁ + Γ₂ -> (Γ₁ ++ Γ₂) ↭ Γ
+++# split-e = refl
+++# (split-l p) = prep _ (+++# p)
+++# (split-r p) = trans (shift _ _ _) (prep _ (+++# p))

Un : Context -> Set
Un = All UnT

#un+ : ∀{Γ Γ₁ Γ₂} -> Γ ≃ Γ₁ + Γ₂ -> Un Γ₁ -> Un Γ₂ -> Un Γ
#un+ pc un₁ un₂ = All-resp-↭ (+++# pc) (++⁺ un₁ un₂)
