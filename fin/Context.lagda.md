# Typing contexts

This module defines typing contexts and the main operations on them.

## Imports

```agda
open import Data.Product using (_×_; Σ; _,_; ∃; Σ-syntax; ∃-syntax)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Type
```

## Definition

A **typing context** is simply a list of types. For this reason, the
*constructors* of `Context` are chosen to resemble those for plain lists. The
*position* of a type within a typing context indicates which variables it refers
to.

```agda
data Context : Set where
  []   : Context
  _::_ : Type -> Context -> Context

infixr 5 _::_
```

We define a helper function to create a singleton list.

```agda
[_] : Type -> Context
[_] = _:: []
```

## Permutations

We now define a binary relation `Γ # Δ` expressing the fact that a
typing context `Γ` is a **permutation** of another typing context
`Δ`.  A permutation is the result of a finite (possibly null) number
of *swaps* occurring in the types of a context.

```agda
data _#_ : Context -> Context -> Set where
  #refl : ∀{Γ} -> Γ # Γ
  #tran : ∀{Γ Δ Θ} -> Γ # Δ -> Δ # Θ -> Γ # Θ
  #next : ∀{Γ Δ A} -> Γ # Δ -> (A :: Γ) # (A :: Δ)
  #here : ∀{Γ A B} -> (A :: B :: Γ) # (B :: A :: Γ)
```

The constructor `#refl` represents the trivial permutation where no
swaps occur.  The constructor `#tran` builds a permutation as the
concatenation of other permutations. The constructor `#here` builds
a permutation whereby the *two topmost* elements of a typing context
are swapped. Finally, the constructor `#next` builds a permutation
occurring deep into a typing context.

It is easy to prove that `#` is symmetric. Hereafter, we will use
simple permutations to infer the shape of some simple typing
contexts: if `Γ` is a permutation of the empty context, then `Γ`
*is* the empty context; if `Γ` is a permutation of a singleton
context, then `Γ` *is* that singleton context.

```agda
#nil : ∀{Γ} -> [] # Γ -> Γ ≡ []
#nil #refl = refl
#nil {Γ} (#tran π π') rewrite #nil π = #nil π'

#one : ∀{A Γ} -> [ A ] # Γ -> Γ ≡ [ A ]
#one #refl = refl
#one (#tran π π') rewrite #one π | #one π' = refl
#one (#next π) rewrite #nil π = refl
```

It is also convenient to define once and for all the permutation
that "rotates" the first three elements in a typing context. This
permutation is named after the analogous operation on stacks in the
programming language Forth.

```agda
#rot : ∀{A B C Γ} -> (A :: B :: C :: Γ) # (C :: A :: B :: Γ)
#rot = #tran (#next #here) #here
```

## Splitting

The most important operation involving typing contexts is that of
**context splitting**. We indicate that `Γ` can be split into `Δ`
and `Θ` using the notation `Γ ≃ Δ + Θ`. Note that this ternary
relation can also be read as the fact that the **merging** of `Δ`
and `Θ` results into the typing context `Γ`. Both interpretations
are valid and can be used interchangeably.

```agda
infix 4 _≃_+_

data _≃_+_ : Context -> Context -> Context -> Set where
  split-e : [] ≃ [] + []
  split-l : ∀{A Γ Δ Θ} -> Γ ≃ Δ + Θ -> A :: Γ ≃ A :: Δ + Θ
  split-r : ∀{A Γ Δ Θ} -> Γ ≃ Δ + Θ -> A :: Γ ≃ Δ + A :: Θ
```

Note how a *proof* of `Γ ≃ Δ + Θ` specifies how each type of `Γ`
ends up in either `Δ` (by `split-l`) or in `Θ` (by `split-r`). That
is, types are all linear. The empty context can only be split into
two empty contexts by `split-e`.

In many cases we will use splitting for describing relations of the
form `Γ ≃ Δ + Θ` where `Δ` is a *singleton context*. It is therefore
convenient to introduce some syntactic sugar for this particular
form of splitting.

```agda
infix 4 _≃_,_

_≃_,_ : Context -> Type -> Context -> Set
Γ ≃ A , Δ = Γ ≃ [ A ] + Δ
```

It is easy to see that splitting is commutative.

```agda
+-comm : ∀{Γ Δ Θ} -> Γ ≃ Δ + Θ -> Γ ≃ Θ + Δ
+-comm split-e = split-e
+-comm (split-l p) = split-r (+-comm p)
+-comm (split-r p) = split-l (+-comm p)
```

The empty context behaves as the "unit" for context splitting.

```agda
+-unit-l : ∀{Γ} -> Γ ≃ [] + Γ
+-unit-l {[]} = split-e
+-unit-l {_ :: _} = split-r +-unit-l

+-unit-r : ∀{Γ} -> Γ ≃ Γ + []
+-unit-r = +-comm +-unit-l
```

Context splitting is also associative in a sense that is made
precise below. If we write $\Delta + \Theta$ for some $\Gamma$ such
that $\Gamma \simeq \Delta + \Theta$, then we can prove that
$\Gamma_1 + (\Gamma_2 + \Gamma_3) = (\Gamma_1 + \Gamma_2) +
\Gamma_3$.

```agda
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
```

A few additional results about splitting and simple contexts follow.

```agda
+-empty-l : ∀{Γ Δ} -> Γ ≃ [] + Δ -> Γ ≡ Δ
+-empty-l split-e = refl
+-empty-l (split-r p) = Eq.cong (_ ::_) (+-empty-l p)

+-sing-l : ∀{A B Γ} -> [ A ] ≃ B , Γ -> A ≡ B × Γ ≡ []
+-sing-l (split-l split-e) = refl , refl
```

## Splitting and permutations

When `Γ` is the merge of a singleton context `[ A ]` and some other
context `Δ` that is `Γ ≃ [ A ] + Δ` then the type `A` must have been
inserted "somewhere" within `Δ`. That is, `A :: Δ` must be a
permutation of `Γ`.

```agda
#cons : ∀{A Γ Δ} -> Γ ≃ A , Δ -> (A :: Δ) # Γ
#cons (split-l p) with +-empty-l p
... | refl = #refl
#cons (split-r p) with #cons p
... | π = #tran #here (#next π)
```

Splitting some context $\Gamma$ that is a permutation of another
context $\Delta$ results in two sub-contexts $\Gamma_1$ and
$\Gamma_2$ which can be merged into $\Delta$ once they are suitable
permuted into some $\Delta_1$ and $\Delta_2$.

```agda
#split : ∀{Γ Γ₁ Γ₂ Δ} -> Γ # Δ -> Γ ≃ Γ₁ + Γ₂ -> ∃[ Δ₁ ] ∃[ Δ₂ ] (Δ ≃ Δ₁ + Δ₂ × Γ₁ # Δ₁ × Γ₂ # Δ₂)
#split #refl p = _ , _ , p , #refl , #refl
#split (#tran π π') p with #split π p
... | Θ₁ , Θ₂ , p' , π₁ , π₂ with #split π' p'
... | Δ₁ , Δ₂ , q , π₁' , π₂' = Δ₁ , Δ₂ , q , #tran π₁ π₁' , #tran π₂ π₂'
#split (#next π) (split-l p) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂  = _ :: Δ₁ , Δ₂ , split-l q , #next π₁ , π₂
#split (#next π) (split-r p) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = Δ₁ , _ :: Δ₂ , split-r q , π₁ , #next π₂
#split #here (split-l (split-l p)) = _ , _ , split-l (split-l p) , #here , #refl
#split #here (split-l (split-r p)) = _ , _ , split-r (split-l p) , #refl , #refl
#split #here (split-r (split-l p)) = _ , _ , split-l (split-r p) , #refl , #refl
#split #here (split-r (split-r p)) = _ , _ , split-r (split-r p) , #refl , #here
```

Auxiliary minor properties about splitting and permutations follow.

```agda
#one+ : ∀{A Γ Γ' Δ} ->
        Γ # Δ -> Γ ≃ A , Γ' -> ∃[ Δ' ] (Δ ≃ A , Δ' × Γ' # Δ')
#one+ π p with #split π p
... | Θ , Δ' , q , π₁ , π₂ rewrite #one π₁ = Δ' , q , π₂
```
