# Types

This module defines types and proves their main properties.

## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong₂)
```

Types are propositions of multiplicative additive linear logic.

## Definition

```agda
data Type : Set where
  𝟘 𝟙 ⊥ ⊤ : Type
  _&_ _⊕_ _⊗_ _⅋_ : Type -> Type -> Type
```

## Duality

Duality is the standard relation between a type and its dual, which represents
the complementary protocol. A relation `Dual A B` means that $A = B^⊥$.

```agda
data Dual : Type -> Type -> Set where
  d-𝟘-⊤ : Dual 𝟘 ⊤
  d-⊤-𝟘 : Dual ⊤ 𝟘
  d-𝟙-⊥ : Dual 𝟙 ⊥
  d-⊥-𝟙 : Dual ⊥ 𝟙
  d-&-⊕ : ∀{A B A' B'} -> Dual A A' -> Dual B B' -> Dual (A & B) (A' ⊕ B')
  d-⊕-& : ∀{A B A' B'} -> Dual A A' -> Dual B B' -> Dual (A ⊕ B) (A' & B')
  d-⊗-⅋ : ∀{A B A' B'} -> Dual A A' -> Dual B B' -> Dual (A ⊗ B) (A' ⅋ B')
  d-⅋-⊗ : ∀{A B A' B'} -> Dual A A' -> Dual B B' -> Dual (A ⅋ B) (A' ⊗ B')
```

It is straightforward to prove that duality is a symmetric relation.

```agda
dual-symm : ∀{A B} -> Dual A B -> Dual B A
dual-symm d-𝟘-⊤ = d-⊤-𝟘
dual-symm d-⊤-𝟘 = d-𝟘-⊤
dual-symm d-𝟙-⊥ = d-⊥-𝟙
dual-symm d-⊥-𝟙 = d-𝟙-⊥
dual-symm (d-&-⊕ p q) = d-⊕-& (dual-symm p) (dual-symm q)
dual-symm (d-⊕-& p q) = d-&-⊕ (dual-symm p) (dual-symm q)
dual-symm (d-⊗-⅋ p q) = d-⅋-⊗ (dual-symm p) (dual-symm q)
dual-symm (d-⅋-⊗ p q) = d-⊗-⅋ (dual-symm p) (dual-symm q)
```

It is also easy to prove that duality is an **involution**.

```agda
dual-inv : ∀{A B C} -> Dual A B -> Dual B C -> A ≡ C
dual-inv d-𝟘-⊤ d-⊤-𝟘 = refl
dual-inv d-⊤-𝟘 d-𝟘-⊤ = refl
dual-inv d-𝟙-⊥ d-⊥-𝟙 = refl
dual-inv d-⊥-𝟙 d-𝟙-⊥ = refl
dual-inv (d-&-⊕ p q) (d-⊕-& r s) = cong₂ _&_ (dual-inv p r) (dual-inv q s)
dual-inv (d-⊕-& p q) (d-&-⊕ r s) = cong₂ _⊕_ (dual-inv p r) (dual-inv q s)
dual-inv (d-⊗-⅋ p q) (d-⅋-⊗ r s) = cong₂ _⊗_ (dual-inv p r) (dual-inv q s)
dual-inv (d-⅋-⊗ p q) (d-⊗-⅋ r s) = cong₂ _⅋_ (dual-inv p r) (dual-inv q s)
```

From this we can derive that the duality relation is actually a
function.

```agda
dual-fun-r : ∀{A B C} -> Dual A B -> Dual A C -> B ≡ C
dual-fun-r d e = dual-inv (dual-symm d) e

dual-fun-l : ∀{A B C} -> Dual B A -> Dual C A -> B ≡ C
dual-fun-l d e = dual-inv d (dual-symm e)
```
