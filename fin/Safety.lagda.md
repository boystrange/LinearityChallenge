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

## Safety

In words, a process is safe if every cut therein that involves two
threads acting on the channel restricted by the cut describe
complementary actions (an input and an output). Since we work with
intrinsically typed processes, it is enough to show that every such
cut has the desired property. To this aim, we introduce the class of
**action cuts** (where the composed sub-processes are [`Action`
processes](Process.lagda.md)) and the class of **safe cuts** (where
the sub-process on the left is an `Output` process and the
sub-process on the right is an `Input` process).

```agda
data ActionCut {Γ} : Process Γ -> Set where
  is-action-cut :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)} ->
    Action P -> Action Q -> ActionCut (cut d p P Q)

data SafeCut {Γ} : Process Γ -> Set where
  is-safe-cut :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)} ->
    Output P -> Input Q -> SafeCut (cut d p P Q)
```

Safety follows easily.

```agda
safety : ∀{Γ} {P : Process Γ} -> ActionCut P -> ∃[ Q ] P ⊒ Q × SafeCut Q
safety (is-action-cut d p (inj₁ x) (inj₁ y)) = contradiction (x , y) (input-input d)
safety (is-action-cut d p (inj₁ x) (inj₂ y)) = _ , s-comm d (dual-symm d) p (+-comm p) , is-safe-cut (dual-symm d) (+-comm p) y x
safety (is-action-cut d p (inj₂ x) (inj₁ y)) = _ , s-refl , is-safe-cut d p x y
safety (is-action-cut d p (inj₂ x) (inj₂ y)) = contradiction (x , y) (output-output d)
```
