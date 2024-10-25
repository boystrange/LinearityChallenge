# Subtyping

This module defines subtyping and proves its soundness.

## Imports

```agda
open import Data.Bool using (Bool; if_then_else_)
open Bool using (true; false)
open import Data.Sum
open import Data.Product using (Σ; _×_; _,_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Nullary using (¬_; contradiction)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong₂)

open import Type
open import Context
open import Process
open import LinkElimination
```

## Definition

We start by defining the subtyping relation `≼` for (finite)
session types as described in the paper by [Horne and
Padovani](http://dx.doi.org/10.1016/j.jlamp.2024.100986). Basically,
𝟘 is the least session type and ⊤ is the greatest one. Every other
relation follows from the expected properties of `≼`: it should be
reflexive on constants and *covariant* with respect to every
connective.

```agda
infix 4 _≼_

data _≼_ : Type -> Type -> Set where
  sub-0 : ∀{A} -> 𝟘 ≼ A
  sub-⊤ : ∀{A} -> A ≼ ⊤
  sub-1 : 𝟙 ≼ 𝟙
  sub-⊥ : ⊥ ≼ ⊥
  sub-& : ∀{A B A' B'} -> A ≼ A' -> B ≼ B' -> A & B ≼ A' & B'
  sub-⊕ : ∀{A B A' B'} -> A ≼ A' -> B ≼ B' -> A ⊕ B ≼ A' ⊕ B'
  sub-⅋ : ∀{A B A' B'} -> A ≼ A' -> B ≼ B' -> A ⅋ B ≼ A' ⅋ B'
  sub-⊗ : ∀{A B A' B'} -> A ≼ A' -> B ≼ B' -> A ⊗ B ≼ A' ⊗ B'
```

## Properties

The fact that `≼` is reflexive in general, transitive and
antisymmetric is proved below.

```agda
≼-refl : ∀{A} -> A ≼ A
≼-refl {𝟘} = sub-0
≼-refl {𝟙} = sub-1
≼-refl {⊥} = sub-⊥
≼-refl {⊤} = sub-⊤
≼-refl {A & B} = sub-& ≼-refl ≼-refl
≼-refl {A ⊕ B} = sub-⊕ ≼-refl ≼-refl
≼-refl {A ⊗ B} = sub-⊗ ≼-refl ≼-refl
≼-refl {A ⅋ B} = sub-⅋ ≼-refl ≼-refl

≼-tran : ∀{A B C} -> A ≼ B -> B ≼ C -> A ≼ C
≼-tran sub-0 t = sub-0
≼-tran s sub-⊤ = sub-⊤
≼-tran sub-1 t = t
≼-tran sub-⊥ t = t
≼-tran (sub-& s₁ s₂) (sub-& t₁ t₂) = sub-& (≼-tran s₁ t₁) (≼-tran s₂ t₂)
≼-tran (sub-⊕ s₁ s₂) (sub-⊕ t₁ t₂) = sub-⊕ (≼-tran s₁ t₁) (≼-tran s₂ t₂)
≼-tran (sub-⅋ s₁ s₂) (sub-⅋ t₁ t₂) = sub-⅋ (≼-tran s₁ t₁) (≼-tran s₂ t₂)
≼-tran (sub-⊗ s₁ s₂) (sub-⊗ t₁ t₂) = sub-⊗ (≼-tran s₁ t₁) (≼-tran s₂ t₂)

≼-anti-symm : ∀{A B} -> A ≼ B -> B ≼ A -> A ≡ B
≼-anti-symm sub-0 sub-0 = refl
≼-anti-symm sub-⊤ sub-⊤ = refl
≼-anti-symm sub-1 sub-1 = refl
≼-anti-symm sub-⊥ sub-⊥ = refl
≼-anti-symm (sub-& s₁ s₂) (sub-& t₁ t₂) = cong₂ _&_ (≼-anti-symm s₁ t₁) (≼-anti-symm s₂ t₂)
≼-anti-symm (sub-⊕ s₁ s₂) (sub-⊕ t₁ t₂) = cong₂ _⊕_ (≼-anti-symm s₁ t₁) (≼-anti-symm s₂ t₂)
≼-anti-symm (sub-⅋ s₁ s₂) (sub-⅋ t₁ t₂) = cong₂ _⅋_ (≼-anti-symm s₁ t₁) (≼-anti-symm s₂ t₂)
≼-anti-symm (sub-⊗ s₁ s₂) (sub-⊗ t₁ t₂) = cong₂ _⊗_ (≼-anti-symm s₁ t₁) (≼-anti-symm s₂ t₂)
```

Notoriously, `≼` should behave contravariantly with respect to
duality, namely if $A \leq B$ then we expect $B^\bot \leq
A^\bot$. This is proved below.

```agda
dual≼ : ∀{A A' B B'} -> Dual A A' -> Dual B B' -> A ≼ B -> B' ≼ A'
dual≼ d-𝟘-⊤ e sub-0 = sub-⊤
dual≼ d d-⊤-𝟘 sub-⊤ = sub-0
dual≼ d-𝟙-⊥ d-𝟙-⊥ sub-1 = sub-⊥
dual≼ d-⊥-𝟙 d-⊥-𝟙 sub-⊥ = sub-1
dual≼ (d-&-⊕ d₁ d₂) (d-&-⊕ e₁ e₂) (sub-& s₁ s₂) = sub-⊕ (dual≼ d₁ e₁ s₁) (dual≼ d₂ e₂ s₂)
dual≼ (d-⊕-& d₁ d₂) (d-⊕-& e₁ e₂) (sub-⊕ s₁ s₂) = sub-& (dual≼ d₁ e₁ s₁) (dual≼ d₂ e₂ s₂)
dual≼ (d-⅋-⊗ d₁ d₂) (d-⅋-⊗ e₁ e₂) (sub-⅋ s₁ s₂) = sub-⊗ (dual≼ d₁ e₁ s₁) (dual≼ d₂ e₂ s₂)
dual≼ (d-⊗-⅋ d₁ d₂) (d-⊗-⅋ e₁ e₂) (sub-⊗ s₁ s₂) = sub-⅋ (dual≼ d₁ e₁ s₁) (dual≼ d₂ e₂ s₂)
```

## Soundness

For the results that follow, it is convenient to extend subtyping
from types to typing contexts pointwise.

```agda
infix 4 _≼⁺_

data _≼⁺_ : Context -> Context -> Set where
  zero : [] ≼⁺ []
  succ : ∀{A B Γ Δ} -> A ≼ B -> Γ ≼⁺ Δ -> A :: Γ ≼⁺ B :: Δ
```

Next we have two expected results relating subtyping (for typing
contexts) and splitting.

```agda
split≼⁺ : ∀{Γ Γ₁ Γ₂ Δ} -> Γ ≼⁺ Δ -> Γ ≃ Γ₁ + Γ₂ ->
          ∃[ Δ₁ ] ∃[ Δ₂ ] Δ ≃ Δ₁ + Δ₂ × Γ₁ ≼⁺ Δ₁ × Γ₂ ≼⁺ Δ₂
split≼⁺ zero split-e = [] , [] , split-e , zero , zero
split≼⁺ (succ s₁ s₂) (split-l p) with split≼⁺ s₂ p
... | Δ₁ , Δ₂ , p' , s₃ , s₄ = _ , _ , split-l p' , succ s₁ s₃ , s₄
split≼⁺ (succ s₁ s₂) (split-r p) with split≼⁺ s₂ p
... | _ , _ , p' , s₃ , s₄ = _ , _ , split-r p' , s₃ , succ s₁ s₄

split≼ : ∀{Γ Γ' A Δ} -> Γ ≼⁺ Δ -> Γ ≃ A , Γ' ->
          ∃[ B ] ∃[ Δ' ] Δ ≃ B , Δ' × A ≼ B × Γ' ≼⁺ Δ'
split≼ s p with split≼⁺ s p
... | _ , _ , p' , succ s₁ zero , s₃ = _ , _ , p' , s₁ , s₃
```

We can now prove the soundness of subtyping as the following
**subsumption** result. Any process that is well typed in Γ can be
subsumed to a process that is well typed in Δ whenever Γ is a
subtyping context of Δ. Note that, in order to prove this result, we
use the [link elimination property](LinkElimination.lagda.md).

```agda
subsumption : ∀{Γ Δ} -> Γ ≼⁺ Δ -> Process Γ -> Process Δ
subsumption s P with link-elimination P
... | _ , Plf = aux s Plf
  where
    aux : ∀{Γ Δ} {P : Process Γ} -> Γ ≼⁺ Δ -> LinkFree P -> Process Δ
    aux s (fail p) with split≼ s p
    ... | _ , _ , p' , sub-⊤ , _ = fail p'
    aux s (wait p Plf) with split≼ s p
    ... | .⊤ , Δ' , p' , sub-⊤ , s₂ = fail p'
    ... | .⊥ , Δ' , p' , sub-⊥ , s₂ = wait p' (aux s₂ Plf)
    aux s (case p Plf Qlf)  with split≼ s p
    ... | _ , _ , p' , sub-⊤ , s₃ = fail p'
    ... | _ , _ , p' , sub-& s₁ s₂ , s₃ = case p' (aux (succ s₁ s₃) Plf) (aux (succ s₂ s₃) Qlf)
    aux s (join p Plf)  with split≼ s p
    ... | _ , _ , p' , sub-⊤ , s₂ = fail p'
    ... | _ , _ , p' , sub-⅋ s₁ s₂ , s₃ = join p' (aux (succ s₂ (succ s₁ s₃)) Plf)
    aux (succ sub-⊤ zero) close = fail (split-l split-e)
    aux (succ sub-1 zero) close = close
    aux s (select false p Plf)  with split≼ s p
    ... | _ , _ , p' , sub-⊤ , s₂ = fail p'
    ... | _ , _ , p' , sub-⊕ s₁ s₂ , s₃ = select false p' (aux (succ s₂ s₃) Plf)
    aux s (select true p Plf)  with split≼ s p
    ... | _ , _ , p' , sub-⊤ , s₂ = fail p'
    ... | _ , _ , p' , sub-⊕ s₁ s₂ , s₃ = select true p' (aux (succ s₁ s₃) Plf)
    aux s (fork p q Plf Qlf) with split≼ s p
    ... | _ , _ , p' , sub-⊤ , s₃ = fail p'
    ... | _ , _ , p' , sub-⊗ s₁ s₂ , s₃ with split≼⁺ s₃ q
    ... | _ , _ , q' , s₄ , s₅ = fork p' q' (aux (succ s₁ s₄) Plf) (aux (succ s₂ s₅) Qlf)
    aux s (cut d p Plf Qlf)  with split≼⁺ s p
    ... | _ , _ , p' , s₁ , s₂ = cut d p' (aux (succ ≼-refl s₁) Plf) (aux (succ ≼-refl s₂) Qlf)
```
