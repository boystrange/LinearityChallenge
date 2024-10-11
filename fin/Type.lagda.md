# Types

This module defines types and proves their main properties.

## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong₂)
```

Types are propositions of multiplicative additive linear logic. The constructors
`Zero`, `One`, `Bot` and `Top` respectively represent the constants
$\mathbb{0}$, $\mathbb{1}$, $⊥$ and $⊤$. The remaining constructors represent
the binary connectives.

## Definition of Types

```agda
data Type : Set where
  Zero One Bot Top : Type
  _&_ _⊕_ _⊗_ _⅋_ : Type -> Type -> Type
```

## Duality

Duality is the standard relation between a type and its dual, which represents
the complementary protocol. A relation `Dual A B` means that $A = B^⊥$.

```agda
data Dual : Type -> Type -> Set where
  d-0-⊤ : Dual Zero Top
  d-⊤-0 : Dual Top Zero
  d-1-⊥  : Dual One Bot
  d-⊥-1  : Dual Bot One
  d-&-⊕ : ∀{A B A' B'} -> Dual A A' -> Dual B B' -> Dual (A & B) (A' ⊕ B')
  d-⊕-& : ∀{A B A' B'} -> Dual A A' -> Dual B B' -> Dual (A ⊕ B) (A' & B')
  d-⊗-⅋ : ∀{A B A' B'} -> Dual A A' -> Dual B B' -> Dual (A ⊗ B) (A' ⅋ B')
  d-⅋-⊗ : ∀{A B A' B'} -> Dual A A' -> Dual B B' -> Dual (A ⅋ B) (A' ⊗ B')
```

It is straightforward to prove that duality is a symmetric relation.

```agda
dual-symm : ∀{A B} -> Dual A B -> Dual B A
dual-symm d-0-⊤ = d-⊤-0
dual-symm d-⊤-0 = d-0-⊤
dual-symm d-1-⊥ = d-⊥-1
dual-symm d-⊥-1 = d-1-⊥
dual-symm (d-&-⊕ p q) = d-⊕-& (dual-symm p) (dual-symm q)
dual-symm (d-⊕-& p q) = d-&-⊕ (dual-symm p) (dual-symm q)
dual-symm (d-⊗-⅋ p q) = d-⅋-⊗ (dual-symm p) (dual-symm q)
dual-symm (d-⅋-⊗ p q) = d-⊗-⅋ (dual-symm p) (dual-symm q)
```

It is also easy to prove that duality is an injective function.

```agda
dual-fun-r : ∀{A B C} -> Dual A B -> Dual A C -> B ≡ C
dual-fun-r d-0-⊤ d-0-⊤ = refl
dual-fun-r d-⊤-0 d-⊤-0 = refl
dual-fun-r d-1-⊥ d-1-⊥ = refl
dual-fun-r d-⊥-1 d-⊥-1 = refl
dual-fun-r (d-&-⊕ p p') (d-&-⊕ q q') = cong₂ _⊕_ (dual-fun-r p q) (dual-fun-r p' q')
dual-fun-r (d-⊕-& p p') (d-⊕-& q q') = cong₂ _&_ (dual-fun-r p q) (dual-fun-r p' q')
dual-fun-r (d-⊗-⅋ p p') (d-⊗-⅋ q q') = cong₂ _⅋_ (dual-fun-r p q) (dual-fun-r p' q')
dual-fun-r (d-⅋-⊗ p p') (d-⅋-⊗ q q') = cong₂ _⊗_ (dual-fun-r p q) (dual-fun-r p' q')

dual-fun-l : ∀{A B C} -> Dual B A -> Dual C A -> B ≡ C
dual-fun-l d e = dual-fun-r (dual-symm d) (dual-symm e)
```
