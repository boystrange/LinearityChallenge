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
```

## Definition

We start by defining the subtyping relation `<=` for (finite)
session types as described in the paper by [Horne and
Padovani](http://dx.doi.org/10.1016/j.jlamp.2024.100986). Basically,
𝟘 is the least session type and ⊤ is the greatest one. Every other
relation follows from the expected properties of `<=`: it should be
reflexive on constants and *covariant* with respect to every
connective.

```agda
infix 4 _<=_

data _<=_ : Type -> Type -> Set where
  sub-0 : ∀{A} -> 𝟘 <= A
  sub-⊤ : ∀{A} -> A <= ⊤
  sub-1 : 𝟙 <= 𝟙
  sub-⊥ : ⊥ <= ⊥
  sub-& : ∀{A B A' B'} -> A <= A' -> B <= B' -> A & B <= A' & B'
  sub-⊕ : ∀{A B A' B'} -> A <= A' -> B <= B' -> A ⊕ B <= A' ⊕ B'
  sub-⅋ : ∀{A B A' B'} -> A <= A' -> B <= B' -> A ⅋ B <= A' ⅋ B'
  sub-⊗ : ∀{A B A' B'} -> A <= A' -> B <= B' -> A ⊗ B <= A' ⊗ B'
```

## Properties

The fact that `<=` is reflexive in general, transitive and
antisymmetric is proved below.

```agda
<=-refl : ∀{A} -> A <= A
<=-refl {𝟘} = sub-0
<=-refl {𝟙} = sub-1
<=-refl {⊥} = sub-⊥
<=-refl {⊤} = sub-⊤
<=-refl {A & B} = sub-& <=-refl <=-refl
<=-refl {A ⊕ B} = sub-⊕ <=-refl <=-refl
<=-refl {A ⊗ B} = sub-⊗ <=-refl <=-refl
<=-refl {A ⅋ B} = sub-⅋ <=-refl <=-refl

<=-tran : ∀{A B C} -> A <= B -> B <= C -> A <= C
<=-tran sub-0 t = sub-0
<=-tran s sub-⊤ = sub-⊤
<=-tran sub-1 t = t
<=-tran sub-⊥ t = t
<=-tran (sub-& s₁ s₂) (sub-& t₁ t₂) = sub-& (<=-tran s₁ t₁) (<=-tran s₂ t₂)
<=-tran (sub-⊕ s₁ s₂) (sub-⊕ t₁ t₂) = sub-⊕ (<=-tran s₁ t₁) (<=-tran s₂ t₂)
<=-tran (sub-⅋ s₁ s₂) (sub-⅋ t₁ t₂) = sub-⅋ (<=-tran s₁ t₁) (<=-tran s₂ t₂)
<=-tran (sub-⊗ s₁ s₂) (sub-⊗ t₁ t₂) = sub-⊗ (<=-tran s₁ t₁) (<=-tran s₂ t₂)

<=-anti-symm : ∀{A B} -> A <= B -> B <= A -> A ≡ B
<=-anti-symm sub-0 sub-0 = refl
<=-anti-symm sub-⊤ sub-⊤ = refl
<=-anti-symm sub-1 sub-1 = refl
<=-anti-symm sub-⊥ sub-⊥ = refl
<=-anti-symm (sub-& s₁ s₂) (sub-& t₁ t₂) = cong₂ _&_ (<=-anti-symm s₁ t₁) (<=-anti-symm s₂ t₂)
<=-anti-symm (sub-⊕ s₁ s₂) (sub-⊕ t₁ t₂) = cong₂ _⊕_ (<=-anti-symm s₁ t₁) (<=-anti-symm s₂ t₂)
<=-anti-symm (sub-⅋ s₁ s₂) (sub-⅋ t₁ t₂) = cong₂ _⅋_ (<=-anti-symm s₁ t₁) (<=-anti-symm s₂ t₂)
<=-anti-symm (sub-⊗ s₁ s₂) (sub-⊗ t₁ t₂) = cong₂ _⊗_ (<=-anti-symm s₁ t₁) (<=-anti-symm s₂ t₂)
```

Notoriously, `<=` should behave contravariantly with respect to
duality, namely if $A \leq B$ then we expect $B^\bot \leq
A^\bot$. This is proved below.

```agda
dual<= : ∀{A A' B B'} -> Dual A A' -> Dual B B' -> A <= B -> B' <= A'
dual<= d-𝟘-⊤ e sub-0 = sub-⊤
dual<= d d-⊤-𝟘 sub-⊤ = sub-0
dual<= d-𝟙-⊥ d-𝟙-⊥ sub-1 = sub-⊥
dual<= d-⊥-𝟙 d-⊥-𝟙 sub-⊥ = sub-1
dual<= (d-&-⊕ d₁ d₂) (d-&-⊕ e₁ e₂) (sub-& s₁ s₂) = sub-⊕ (dual<= d₁ e₁ s₁) (dual<= d₂ e₂ s₂)
dual<= (d-⊕-& d₁ d₂) (d-⊕-& e₁ e₂) (sub-⊕ s₁ s₂) = sub-& (dual<= d₁ e₁ s₁) (dual<= d₂ e₂ s₂)
dual<= (d-⅋-⊗ d₁ d₂) (d-⅋-⊗ e₁ e₂) (sub-⅋ s₁ s₂) = sub-⊗ (dual<= d₁ e₁ s₁) (dual<= d₂ e₂ s₂)
dual<= (d-⊗-⅋ d₁ d₂) (d-⊗-⅋ e₁ e₂) (sub-⊗ s₁ s₂) = sub-⅋ (dual<= d₁ e₁ s₁) (dual<= d₂ e₂ s₂)
```

## Soundness

For the results that follow, it is convenient to extend subtyping
from types to typing contexts pointwise.

```agda
infix 4 _<=⁺_

data _<=⁺_ : Context -> Context -> Set where
  zero : [] <=⁺ []
  succ : ∀{A B Γ Δ} -> A <= B -> Γ <=⁺ Δ -> A :: Γ <=⁺ B :: Δ
```

An important auxiliary result that is needed in order to prove the
soundness of subtyping is the ability to synthesize a process that
acts as a **link** between channels of type `A'` and `B'` whenever
`A'` and `B'` are supertypes of some `A` and `B` that are dual to
one another. By reflexivity of subtyping, this result also shows
that the link (and related axiom rule) is *admissable* in πLIN.

```agda
make-link : ∀{A A' B B'} -> A <= A' -> B <= B' -> Dual A B -> Process (A' :: B' :: [])
make-link sub-0 sub-⊤ d-0-⊤ = fail (split-r (split-l split-e))
make-link sub-⊤ s₂ d = fail (split-l (split-r split-e))
make-link sub-1 sub-⊤ d-1-⊥ = fail (split-r (split-l split-e))
make-link sub-1 sub-⊥ d-1-⊥ = wait (split-r (split-l split-e)) close
make-link sub-⊥ sub-⊤ d-⊥-1 = fail (split-r (split-l split-e))
make-link sub-⊥ sub-1 d-⊥-1 = wait (split-l (split-r split-e)) close
make-link (sub-& s₁ s₃) sub-⊤ (d-&-⊕ d₁ d₂) = fail (split-r (split-l split-e))
make-link (sub-& s₁ s₃) (sub-⊕ s₂ s₄) (d-&-⊕ d₁ d₂) =
  case (split-l (split-r split-e))
       (select true (split-r (split-l split-e)) (make-link s₂ s₁ (dual-symm d₁)))
       (select false (split-r (split-l split-e)) (make-link s₄ s₃ (dual-symm d₂)))
make-link (sub-⊕ s₁ s₃) sub-⊤ (d-⊕-& d₁ d₂) = fail (split-r (split-l split-e))
make-link (sub-⊕ s₁ s₃) (sub-& s₂ s₄) (d-⊕-& d₁ d₂) =
  case (split-r (split-l split-e))
       (select true (split-r (split-l split-e)) (make-link s₁ s₂ d₁))
       (select false (split-r (split-l split-e)) (make-link s₃ s₄ d₂))
make-link (sub-⅋ s₁ s₃) sub-⊤ (d-⅋-⊗ d d₁) = fail (split-r (split-l split-e))
make-link (sub-⅋ s₁ s₃) (sub-⊗ s₂ s₄) (d-⅋-⊗ d₁ d₂) =
  join (split-l (split-r split-e))
       (fork (split-r (split-r (split-l split-e))) (split-r (split-l split-e))
             (make-link s₂ s₁ (dual-symm d₁))
             (make-link s₄ s₃ (dual-symm d₂)))
make-link (sub-⊗ s₁ s₃) sub-⊤ (d-⊗-⅋ d d₁) = fail (split-r (split-l split-e))
make-link (sub-⊗ s₁ s₃) (sub-⅋ s₂ s₄) (d-⊗-⅋ d₁ d₂) =
  join (split-r (split-l split-e))
       (fork (split-r (split-r (split-l split-e))) (split-r (split-l split-e))
             (make-link s₁ s₂ d₁)
             (make-link s₃ s₄ d₂))
```

Next we have two expected results relating subtyping (for typing
contexts) and splitting.

```agda
split<=⁺ : ∀{Γ Γ₁ Γ₂ Δ} -> Γ <=⁺ Δ -> Γ ≃ Γ₁ + Γ₂ ->
          ∃[ Δ₁ ] ∃[ Δ₂ ] Δ ≃ Δ₁ + Δ₂ × Γ₁ <=⁺ Δ₁ × Γ₂ <=⁺ Δ₂
split<=⁺ zero split-e = [] , [] , split-e , zero , zero
split<=⁺ (succ s₁ s₂) (split-l p) with split<=⁺ s₂ p
... | Δ₁ , Δ₂ , p' , s₃ , s₄ = _ , _ , split-l p' , succ s₁ s₃ , s₄
split<=⁺ (succ s₁ s₂) (split-r p) with split<=⁺ s₂ p
... | _ , _ , p' , s₃ , s₄ = _ , _ , split-r p' , s₃ , succ s₁ s₄

split<= : ∀{Γ Γ' A Δ} -> Γ <=⁺ Δ -> Γ ≃ A , Γ' ->
          ∃[ B ] ∃[ Δ' ] Δ ≃ B , Δ' × A <= B × Γ' <=⁺ Δ'
split<= s p with split<=⁺ s p
... | _ , _ , p' , succ s₁ zero , s₃ = _ , _ , p' , s₁ , s₃
```

We can now prove the soundness of subtyping as the following
**subsumption** result. Any process that is well typed in `Γ` can be
subsumed to a process that is well typed in `Δ` whenever `Γ` is a
subtyping context of `Δ`. The `sub-link` is just a special case of
this result that is better proved in isolation.

```agda
sub-link : ∀{Γ Δ A B} -> Γ <=⁺ Δ -> Dual A B -> Γ ≃ [ A ] + [ B ] -> Process Δ
sub-link (succ s₁ (succ s₂ zero)) d (split-l (split-r split-e)) = make-link s₁ s₂ d
sub-link (succ s₁ (succ s₂ zero)) d (split-r (split-l split-e)) = make-link s₁ s₂ (dual-symm d)

sub : ∀{Γ Δ} -> Γ <=⁺ Δ -> Process Γ -> Process Δ
sub s (link d p) = sub-link s d p
sub s (fail p) with split<= s p
... | _ , _ , p' , sub-⊤ , _ = fail p'
sub (succ sub-⊤ zero) close = fail (split-l split-e)
sub (succ sub-1 zero) close = close
sub s (wait p P) with split<= s p
... | .⊤ , Δ' , p' , sub-⊤ , s₂ = fail p'
... | .⊥ , Δ' , p' , sub-⊥ , s₂ = wait p' (sub s₂ P)
sub s (select false p P) with split<= s p
... | _ , _ , p' , sub-⊤ , s₂ = fail p'
... | _ , _ , p' , sub-⊕ s₁ s₂ , s₃ = select false p' (sub (succ s₂ s₃) P)
sub s (select true p P) with split<= s p
... | _ , _ , p' , sub-⊤ , s₂ = fail p'
... | _ , _ , p' , sub-⊕ s₁ s₂ , s₃ = select true p' (sub (succ s₁ s₃) P)
sub s (case p P Q) with split<= s p
... | _ , _ , p' , sub-⊤ , s₃ = fail p'
... | _ , _ , p' , sub-& s₁ s₂ , s₃ = case p' (sub (succ s₁ s₃) P) (sub (succ s₂ s₃) Q)
sub s (fork p q P Q) with split<= s p
... | _ , _ , p' , sub-⊤ , s₃ = fail p'
... | _ , _ , p' , sub-⊗ s₁ s₂ , s₃ with split<=⁺ s₃ q
... | _ , _ , q' , s₄ , s₅ = fork p' q' (sub (succ s₁ s₄) P) (sub (succ s₂ s₅) Q)
sub s (join p P) with split<= s p
... | _ , _ , p' , sub-⊤ , s₂ = fail p'
... | _ , _ , p' , sub-⅋ s₁ s₂ , s₃ = join p' (sub (succ s₂ (succ s₁ s₃)) P)
sub s (cut d p P Q) with split<=⁺ s p
... | _ , _ , p' , s₁ , s₂ = cut d p' (sub (succ <=-refl s₁) P) (sub (succ <=-refl s₂) Q)
```
