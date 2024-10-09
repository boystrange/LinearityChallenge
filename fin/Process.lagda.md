# Processes

This module defines the data type for representing intrinsically
typed processes.

```agda
-- MIT License

-- Copyright (c) 2024 Luca Padovani & Claudia Raffaelli

-- Permission is hereby granted, free of charge, to any person
-- obtaining a copy of this software and associated documentation
-- files (the "Software"), to deal in the Software without
-- restriction, including without limitation the rights to use,
-- copy, modify, merge, publish, distribute, sublicense, and/or sell
-- copies of the Software, and to permit persons to whom the
-- Software is furnished to do so, subject to the following
-- conditions:

-- The above copyright notice and this permission notice shall be
-- included in all copies or substantial portions of the Software.

-- THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
-- EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
-- OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
-- NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
-- HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
-- WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
-- FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
-- OTHER DEALINGS IN THE SOFTWARE.

module Process where
```

## Imports

```agda
open import Data.Bool using (Bool; if_then_else_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product using (Σ; _×_; _,_; ∃; Σ-syntax; ∃-syntax)

open import Type
open import Context
```

## Definition

A process is a term representing a proof derivation for a given
typing context $Γ$.

```agda
data Process (Γ : Context) : Set where
```

The `link d p` process forwards a single message from a channel of
type $A^⊥$ to a channel of type $A$. It is well typed in a context
that contains exactly two types, which must be related by duality.

```agda
   Link : ∀{A B} (d : Dual A B) (p : Γ ≃ [ A ] + [ B ]) -> Process Γ
```

The `fail p` process indicates a runtime error on some channel of
type $⊤$. There is no process constructor corresponding to the dual
constant $\mathbb{0}$.

```agda
   Fail : ∀{Δ} (p : Γ ≃ Top , Δ) -> Process Γ
```

The `close p` process sends a termination signal on a session and is
well typed in a singleton context where the only type is
$\mathbb{1}$.

```agda
   Close : Γ ≃ One , [] -> Process Γ
```

The `wait p P` process waits for a termination signal from a channel
and then continues according to the continuation `P`. It is well
typed in a context of the form $⊥, Δ where $⊥$ (which is the dual of
$\mathbb{1}$ is the type of the channel. The continuation `P` must
be well typed in the residual context $Δ$.

```agda
   Wait : ∀{Δ} (p : Γ ≃ Bot , Δ) -> Process Δ -> Process Γ
```

The `select x p P` process sends a boolean value `x` along with a
fresh channel on a channel of type $A ⊕ B$ and continues as a
process `P` that uses the fresh channel as either $A$ or $B$
depending on the value of `x`.

```agda
   Select : ∀{Δ A B} (x : Bool) (p : Γ ≃ A ⊕ B , Δ) ->
            Process ((if x then A else B) :: Δ) -> Process Γ
```

The `case p P Q` process receives a boolean value `x` along with a
fresh channel from a channel of type $A \mathrel\& B$ and continues
as either `P` or `Q` depending to the the value of `x`.

```agda
   Case : ∀{Δ A B} (p : Γ ≃ A & B , Δ) ->
          Process (A :: Δ) -> Process (B :: Δ) -> Process Γ
```

The `fork p q P Q` process sends a pair of new channels on another
channel of type $A ⊗ B$. It has *two* continuations, each using one
endpoint of the new channels created.

```agda
   Fork : ∀{Δ Γ₁ Γ₂ A B} (p : Γ ≃ A ⊗ B , Δ) (q : Δ ≃ Γ₁ + Γ₂) ->
          Process (A :: Γ₁) -> Process (B :: Γ₂) -> Process Γ
```

The `join p P` process receives a pair of channels from a channel of
type $A ⅋ B$.

```agda
   Join : ∀{Δ A B} (p : Γ ≃ A ⅋ B , Δ) -> Process (B :: A :: Δ) -> Process Γ
```

The `cut d p P Q` process represents the parallel composition of two
sub-processes `P` and `Q` connected by a new linear channel. `P` and
`Q` use the new channel according to dual types.

```agda
   Cut : ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) ->
         Process (A :: Γ₁) -> Process (B :: Γ₂) -> Process Γ
```

## Renaming

Every process that is well typed in `Γ` can be turned into a process
that is well typed in `Δ` if `Γ` is a permutation of `Δ`. This
transformation corresponds to renaming the variables occurring free
in the process.

```agda
#process : ∀{Γ Δ} -> Γ # Δ -> Process Γ -> Process Δ
#process π (Link d p) with #one+ π p
... | Δ' , q , π' with #one π'
... | refl = Link d q
#process π (Close p) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ with #one π₁ | #nil π₂
... | refl | refl = Close q
#process π (Fail p) with #one+ π p
... | Δ' , q , π' = Fail q
#process π (Wait p P) with #one+ π p
... | Δ' , q , π' = Wait q (#process π' P)
#process π (Select x p P) with #one+ π p
... | Δ' , q , π' = Select x q (#process (#next π') P)
#process π (Case p P Q) with #one+ π p
... | Δ' , q , π' = Case q (#process (#next π') P) (#process (#next π') Q)
#process π (Fork p q P Q) with #one+ π p
... | Δ' , p' , π' with #split π' q
... | Δ₁ , Δ₂ , q' , π₁ , π₂ = Fork p' q' (#process (#next π₁) P) (#process (#next π₂) Q)
#process π (Join p P) with #one+ π p
... | Δ' , q , π' = Join q (#process (#next (#next π')) P)
#process π (Cut d p P Q) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = Cut d q (#process (#next π₁) P) (#process (#next π₂) Q)
```
