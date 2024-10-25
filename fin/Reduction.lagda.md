# Reduction

This module defines the reduction relation for processes.

## Imports

```agda
open import Data.Bool using (Bool; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open Bool using (true; false)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

open import Type
open import Context
open import Process
open import Congruence
```

## Definition

```agda
data _~>_ {Γ} : Process Γ -> Process Γ -> Set where
  r-link :
    ∀{Δ A B}
    {P : Process (B :: Δ)}
    (d : Dual A B) (e : Dual A B)
    (p : Γ ≃ B , Δ) ->
    cut d p (link e (split-l (split-r split-e))) P ~> #process (#cons p) P

  r-fail :
    ∀{Γ₁ Γ₂ Δ A B P} (d : Dual A B)
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ ⊤ , Δ) ->
    let _ , _ , q' = +-assoc-l p q in
    cut d p (fail (split-r q)) P ~> fail q'

  r-close :
    ∀{P : Process Γ}
    (p₀ : Γ ≃ [] + Γ) (q₀ : Γ ≃ [] + Γ) ->
    cut d-𝟙-⊥ p₀ close (wait (split-l q₀) P) ~> P

  r-select-l :
    ∀{Γ₁ Γ₂ A A' B B'}
    {P : Process (A :: Γ₁)}
    {Q : Process (A' :: Γ₂)}
    {R : Process (B' :: Γ₂)}
    (d : Dual A A') (e : Dual B B')
    (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) ->
    cut (d-⊕-& d e) p
        (select true (split-l p₀) P)
        (case (split-l q₀) Q R) ~> cut d p P Q

  r-select-r :
    ∀{Γ₁ Γ₂ A A' B B'}
    {P : Process (B :: Γ₁)}
    {Q : Process (A' :: Γ₂)}
    {R : Process (B' :: Γ₂)}
    (d : Dual A A') (e : Dual B B')
    (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) ->
    cut (d-⊕-& d e) p
        (select false (split-l p₀) P)
        (case (split-l q₀) Q R) ~> cut e p P R

  r-fork :
    ∀{Γ₁ Γ₂ Γ₃ Δ A B A' B'}
    {P : Process (A :: Γ₁)}
    {Q : Process (B :: Γ₂)}
    {R : Process (B' :: A' :: Γ₃)}
    (d : Dual A A') (e : Dual B B')
    (p : Γ ≃ Δ + Γ₃) (p₀ : Γ₃ ≃ [] + Γ₃)
    (q : Δ ≃ Γ₁ + Γ₂) (q₀ : Δ ≃ [] + Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    cut (d-⊗-⅋ d e) p
        (fork (split-l q₀) q P Q)
        (join (split-l p₀) R) ~> cut d q' P (cut e (split-r p') Q R)

  r-cut :
    ∀{Γ₁ Γ₂ A B}
    {P Q : Process (A :: Γ₁)}
    {R : Process (B :: Γ₂)}
    (d : Dual A B)
    (q : Γ ≃ Γ₁ + Γ₂)
    (r : P ~> Q) ->
    cut d q P R ~> cut d q Q R

  r-cong :
    {P R Q : Process Γ}
    (p : P ⊒ R) (q : R ~> Q) -> P ~> Q
```

A process `P` is **reducible** if `P ~> Q` for some `Q`.

```agda
Reducible : ∀{Γ} -> Process Γ -> Set
Reducible P = ∃[ Q ] P ~> Q
```

We also define the reflexive, transitive closure of reduction which
is useful e.g. for stating and proving [deadlock
freedom](DeadlockFreedom.lagda.md).

```agda
data _=>_ {Γ} : Process Γ -> Process Γ -> Set where
  refl : ∀{P : Process Γ} -> P => P
  tran : ∀{P Q R : Process Γ} -> P ~> Q -> Q => R -> P => R
```

The *length* of a sequence of reductions is computed by the
following function:

```
run-length : ∀{Γ} {P Q : Process Γ} -> P => Q -> ℕ
run-length refl = 0
run-length (tran _ reds) = suc (run-length reds)
```
