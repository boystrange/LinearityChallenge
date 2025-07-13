import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂)

data Type : Set where
  𝟘 𝟙 ⊥ ⊤ : Type
  ¡ ¿ : Type -> Type
  _&_ _⊕_ _⊗_ _⅋_ : Type -> Type -> Type

data Dual : Type -> Type -> Set where
  d-𝟘-⊤ : Dual 𝟘 ⊤
  d-⊤-𝟘 : Dual ⊤ 𝟘
  d-𝟙-⊥ : Dual 𝟙 ⊥
  d-⊥-𝟙 : Dual ⊥ 𝟙
  d-!-? : ∀{A B} -> Dual A B -> Dual (¡ A) (¿ B)
  d-?-! : ∀{A B} -> Dual A B -> Dual (¿ A) (¡ B)
  d-&-⊕ : ∀{A B A' B'} -> Dual A A' -> Dual B B' -> Dual (A & B) (A' ⊕ B')
  d-⊕-& : ∀{A B A' B'} -> Dual A A' -> Dual B B' -> Dual (A ⊕ B) (A' & B')
  d-⊗-⅋ : ∀{A B A' B'} -> Dual A A' -> Dual B B' -> Dual (A ⊗ B) (A' ⅋ B')
  d-⅋-⊗ : ∀{A B A' B'} -> Dual A A' -> Dual B B' -> Dual (A ⅋ B) (A' ⊗ B')

dual-symm : ∀{A B} -> Dual A B -> Dual B A
dual-symm d-𝟘-⊤ = d-⊤-𝟘
dual-symm d-⊤-𝟘 = d-𝟘-⊤
dual-symm d-𝟙-⊥ = d-⊥-𝟙
dual-symm d-⊥-𝟙 = d-𝟙-⊥
dual-symm (d-!-? p) = d-?-! (dual-symm p)
dual-symm (d-?-! p) = d-!-? (dual-symm p)
dual-symm (d-&-⊕ p q) = d-⊕-& (dual-symm p) (dual-symm q)
dual-symm (d-⊕-& p q) = d-&-⊕ (dual-symm p) (dual-symm q)
dual-symm (d-⊗-⅋ p q) = d-⅋-⊗ (dual-symm p) (dual-symm q)
dual-symm (d-⅋-⊗ p q) = d-⊗-⅋ (dual-symm p) (dual-symm q)

dual-inv : ∀{A B C} -> Dual A B -> Dual B C -> A ≡ C
dual-inv d-𝟘-⊤ d-⊤-𝟘 = refl
dual-inv d-⊤-𝟘 d-𝟘-⊤ = refl
dual-inv d-𝟙-⊥ d-⊥-𝟙 = refl
dual-inv d-⊥-𝟙 d-𝟙-⊥ = refl
dual-inv (d-!-? p) (d-?-! q) = cong ¡ (dual-inv p q)
dual-inv (d-?-! p) (d-!-? q) = cong ¿ (dual-inv p q)
dual-inv (d-&-⊕ p q) (d-⊕-& r s) = cong₂ _&_ (dual-inv p r) (dual-inv q s)
dual-inv (d-⊕-& p q) (d-&-⊕ r s) = cong₂ _⊕_ (dual-inv p r) (dual-inv q s)
dual-inv (d-⊗-⅋ p q) (d-⅋-⊗ r s) = cong₂ _⊗_ (dual-inv p r) (dual-inv q s)
dual-inv (d-⅋-⊗ p q) (d-⊗-⅋ r s) = cong₂ _⅋_ (dual-inv p r) (dual-inv q s)

dual-fun-r : ∀{A B C} -> Dual A B -> Dual A C -> B ≡ C
dual-fun-r d e = dual-inv (dual-symm d) e

dual-fun-l : ∀{A B C} -> Dual B A -> Dual C A -> B ≡ C
dual-fun-l d e = dual-inv d (dual-symm e)
