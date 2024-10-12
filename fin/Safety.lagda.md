# Safety

This module proves the **safety** property.

## Imports

```agda
open import Data.Sum
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Nullary using (contradiction)

open import Type
open import Context
open import Process
open import Congruence
```

## Type safety

In words, a process is **type safe** if every (unguarded) cut
therein that involves two threads acting on the channel restricted
by the cut describe complementary actions (an input and an
output). To prove type safety, we introduce the class of **action
cuts** (where the composed sub-processes are [`Action`
processes](Process.lagda.md)) and the class of **safe cuts** (where
the sub-process on the left is an `Output` process and the
sub-process on the right is an `Input` process).

```agda
data ActionCut {Γ} : Process Γ -> Set where
  action-cut :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)} ->
    Action P -> Action Q -> ActionCut (cut d p P Q)

data SafeCut {Γ} : Process Γ -> Set where
  safe-cut :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)} ->
    Output P -> Input Q -> SafeCut (cut d p P Q)
```

Since we want to reason on arbitrarily deep (but unguarded) cuts we
also define the notion of reduction context. A term of type
`ReductionContext Δ Γ` represents an incomplete process that is well
typed in a context of type Γ that contains a "hole" which is assumed
to be well typed in a context of type Δ.

Safety follows easily.

```agda
data ReductionContext (Δ : Context) : Context -> Set where
  hole  : ReductionContext Δ Δ
  cut-l : ∀{Γ Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) ->
          ReductionContext Δ (A :: Γ₁) -> Process (B :: Γ₂) ->
          ReductionContext Δ Γ
  cut-r : ∀{Γ Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) ->
          Process (A :: Γ₁) -> ReductionContext Δ (B :: Γ₂) ->
          ReductionContext Δ Γ
```

We can fill the hole in a reduction context `C` with a process `P`
that is well typed in a suitable context by means of the following
function.

```agda
_⟦_⟧ : ∀{Γ Δ} -> ReductionContext Δ Γ -> Process Δ -> Process Γ
hole ⟦ P ⟧ = P
cut-l d p C Q ⟦ P ⟧ = cut d p (C ⟦ P ⟧) Q
cut-r d p Q C ⟦ P ⟧ = cut d p Q (C ⟦ P ⟧)
```

We say that `P` is a **type-safe process** if, whenever `P ⊒ C ⟦ Q
⟧` and `Q` is an action cut, then `Q ⊒ R` for some `R` that is a
safe cut. Note that type safety is called *well formedness* in the
original challenge description.

```agda
TypeSafe : ∀{Γ} -> Process Γ -> Set
TypeSafe {Γ} P =
  ∀{Δ} {C : ReductionContext Δ Γ} {Q : Process Δ} ->
  ActionCut Q -> P ⊒ (C ⟦ Q ⟧) -> ∃[ R ] Q ⊒ R × SafeCut R
```

The proof that every (well-typed) process `P` is also type safe
follows easily. In fact, it is not even necessary to look at `P` or
at the proof that `P ⊒ C ⟦ Q ⟧` since processes are intrinsically
typed.

```agda
type-safety : ∀{Γ} (P : Process Γ) -> TypeSafe P
type-safety _ (action-cut d p (inj₁ x) (inj₁ y)) _ = contradiction (x , y) (input-input d)
type-safety _ (action-cut d p (inj₁ x) (inj₂ y)) _ = _ , s-comm d (dual-symm d) p (+-comm p) , safe-cut (dual-symm d) (+-comm p) y x
type-safety _ (action-cut d p (inj₂ x) (inj₁ y)) _ = _ , s-refl , safe-cut d p x y
type-safety _ (action-cut d p (inj₂ x) (inj₂ y)) _ = contradiction (x , y) (output-output d)
```
