# Processes

This module defines the data type for representing intrinsically
typed processes.

## Imports

```agda
open import Data.Bool using (Bool; if_then_else_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Sum
open import Data.Product using (Σ; _×_; _,_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Nullary using (¬_)

open import Type
open import Context
```

## Definition

A process is a term representing a proof derivation for a given
typing context `Γ`.

```agda
data Process : Context -> Set where
   link :
     ∀{Γ A B} (d : Dual A B) (p : Γ ≃ [ A ] + [ B ]) -> Process Γ
   fail :
     ∀{Γ Δ} (p : Γ ≃ ⊤ , Δ) -> Process Γ
   close : Process (𝟙 :: [])
   wait :
     ∀{Γ Δ} (p : Γ ≃ ⊥ , Δ) -> Process Δ -> Process Γ
   select :
     ∀{Γ Δ A B} (x : Bool) (p : Γ ≃ A ⊕ B , Δ) ->
     Process ((if x then A else B) :: Δ) -> Process Γ
   case :
     ∀{Γ Δ A B} (p : Γ ≃ A & B , Δ) ->
     Process (A :: Δ) -> Process (B :: Δ) -> Process Γ
   fork :
     ∀{Γ Δ Γ₁ Γ₂ A B} (p : Γ ≃ A ⊗ B , Δ) (q : Δ ≃ Γ₁ + Γ₂) ->
     Process (A :: Γ₁) -> Process (B :: Γ₂) -> Process Γ
   join :
     ∀{Γ Δ A B} (p : Γ ≃ A ⅋ B , Δ) -> Process (B :: A :: Δ) -> Process Γ
   cut :
     ∀{Γ Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) ->
     Process (A :: Γ₁) -> Process (B :: Γ₂) -> Process Γ
```

The `link d p` process forwards a single message from a channel of
type $A^⊥$ to a channel of type $A$. It is well typed in a context
that contains exactly two types, which must be related by duality.
The `fail p` process indicates a runtime error on some channel of
type ⊤. There is no process constructor corresponding to the dual
constant 𝟘. The `close p` process sends a termination signal on a
session and is well typed in a singleton context where the only type
is 𝟙.  The `wait p P` process waits for a termination signal from a
channel and then continues according to the continuation `P`. It is
well typed in a context of the form ⊥, Δ where ⊥ (which is the dual
of 𝟙 is the type of the channel. The continuation `P` must be well
typed in the residual context Δ.  The `select x p P` process sends a
boolean value `x` along with a fresh channel on a channel of type `A
⊕ B` and continues as a process `P` that uses the fresh channel as
either `A` or `B` depending on the value of `x`.  The `case p P Q`
process receives a boolean value `x` along with a fresh channel from
a channel of type `A & B` and continues as either `P` or `Q`
depending to the the value of `x`.  The `fork p q P Q` process sends
a pair of new channels on another channel of type `A ⊗ B`. It has
*two* continuations, each using one endpoint of the new channels
created.  The `join p P` process receives a pair of channels from a
channel of type `A ⅋ B`.  Finally, the `cut d p P Q` process
represents the parallel composition of two sub-processes `P` and `Q`
connected by a new linear channel. `P` and `Q` use the new channel
according to dual types.

## Renaming

Every process that is well typed in `Γ` can be turned into a process
that is well typed in `Δ` if `Γ` is a permutation of `Δ`. This
transformation corresponds to renaming the variables occurring free
in the process.

```agda
#process : ∀{Γ Δ} -> Γ # Δ -> Process Γ -> Process Δ
#process π (link d p) with #one+ π p
... | Δ' , q , π' with #one π'
... | refl = link d q
#process π close with #one π
... | refl = close
#process π (fail p) with #one+ π p
... | Δ' , q , π' = fail q
#process π (wait p P) with #one+ π p
... | Δ' , q , π' = wait q (#process π' P)
#process π (select x p P) with #one+ π p
... | Δ' , q , π' = select x q (#process (#next π') P)
#process π (case p P Q) with #one+ π p
... | Δ' , q , π' = case q (#process (#next π') P) (#process (#next π') Q)
#process π (fork p q P Q) with #one+ π p
... | Δ' , p' , π' with #split π' q
... | Δ₁ , Δ₂ , q' , π₁ , π₂ = fork p' q' (#process (#next π₁) P) (#process (#next π₂) Q)
#process π (join p P) with #one+ π p
... | Δ' , q , π' = join q (#process (#next (#next π')) P)
#process π (cut d p P Q) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = cut d q (#process (#next π₁) P) (#process (#next π₂) Q)
```

## Classification

We define a few predicates to classify processes in various (not
necessarily disjoint) families. First of all, we distinguish between
`Input` and `Output` processes that perform an action on the
"youngest" (the most recently introduced) channel.

```agda
data Input : ∀{Γ} -> Process Γ -> Set where
  fail :
    ∀{Γ Δ}
    (p : Γ ≃ [] + Δ) -> Input (fail (split-l p))
  wait :
    ∀{Γ Δ} (p : Γ ≃ [] + Δ) {P : Process Δ} -> Input (wait (split-l p) P)
  case :
    ∀{Γ Δ A B} (p : Γ ≃ [] + Δ) {P : Process (A :: Δ)} {Q : Process (B :: Δ)} ->
    Input (case (split-l p) P Q)
  join :
    ∀{Γ Δ A B} (p : Γ ≃ [] + Δ) {P : Process (B :: A :: Δ)} ->
    Input (join (split-l p) P)

data Output : ∀{Γ} -> Process Γ -> Set where
  close : Output close
  select :
    ∀{Γ Δ A B} (x : Bool) (p : Γ ≃ [] + Δ) {P : Process ((if x then A else B) :: Δ)} ->
    Output (select x (split-l p) P)
  fork :
    ∀{Γ Δ Δ₁ Δ₂ A B} (p : Γ ≃ [] + Δ) (q : Δ ≃ Δ₁ + Δ₂)
    {P : Process (A :: Δ₁)} {Q : Process (B :: Δ₂)} ->
    Output (fork (split-l p) q P Q)
```

Then, an `Action` process is either an `Input` or an `Output`
process.

```agda
Action : ∀{Γ} -> Process Γ -> Set
Action P = Input P ⊎ Output P
```

We prove that two processes whose youngest channels have types
related by duality cannot be both `Input` or both `Output`
processes. This is key to prove [safety](Safety.lagda.md) and
[deadlock freedom](DeadlockFreedom.lagda.md).

```agda
input-input :
  ∀{Γ Δ A B} {P : Process (A :: Γ)} {Q : Process (B :: Δ)} ->
  Dual A B -> ¬ (Input P × Input Q)
input-input d-⊤-𝟘 (fail p , ())
input-input d-⊥-𝟙 (wait p , ())
input-input (d-&-⊕ d d₁) (case p , ())
input-input (d-⅋-⊗ d d₁) (join p , ())

output-output :
  ∀{Γ Δ A B} {P : Process (A :: Γ)} {Q : Process (B :: Δ)} ->
  Dual A B -> ¬ (Output P × Output Q)
output-output d-𝟙-⊥ (close , ())
output-output (d-⊕-& d d₁) (select x p , ())
output-output (d-⊗-⅋ d d₁) (fork p q , ())
```
