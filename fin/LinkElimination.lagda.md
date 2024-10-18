# Link elimination

This module proves the link elimination property, namely that the
axiom is *admissable*.

## Imports

```agda
open import Data.Bool using (Bool; if_then_else_)
open Bool using (true; false)
open import Data.Product using (Σ; _×_; _,_; ∃; Σ-syntax; ∃-syntax)

open import Type
open import Context
open import Process
```

## Definition

We say that a process is **link free** if it contains no links. This
property is captured by the following predicate.

```agda
data LinkFree : ∀{Γ} -> Process Γ -> Set where
  fail :
    ∀{Γ Δ} (p : Γ ≃ ⊤ , Δ) -> LinkFree (fail p)
  wait :
    ∀{Γ Δ} (p : Γ ≃ ⊥ , Δ) {P : Process Δ} ->
    LinkFree P -> LinkFree (wait p P)
  case :
    ∀{Γ Δ A B} (p : Γ ≃ [ A & B ] + Δ)
    {P : Process (A :: Δ)} {Q : Process (B :: Δ)} ->
    LinkFree P -> LinkFree Q -> LinkFree (case p P Q)
  join :
    ∀{Γ Δ A B} (p : Γ ≃ [ A ⅋ B ] + Δ)
    {P : Process (B :: A :: Δ)} ->
    LinkFree P -> LinkFree (join p P)
  close : LinkFree close
  select :
    ∀{Γ Δ A B} (x : Bool) (p : Γ ≃ [ A ⊕ B ] + Δ)
    {P : Process ((if x then A else B) :: Δ)} ->
    LinkFree P -> LinkFree (select x p P)
  fork :
    ∀{Γ Δ Δ₁ Δ₂ A B} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂)
    {P : Process (A :: Δ₁)} {Q : Process (B :: Δ₂)} ->
    LinkFree P -> LinkFree Q -> LinkFree (fork p q P Q)
  cut :
    ∀{Γ Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)} ->
    LinkFree P -> LinkFree Q -> LinkFree (cut d p P Q)
```

## Proof of link elimination

In order to prove the link elimination property, we first show that
it is possible to create a link-free process that is well typed in a
context of the form $A^⊥,A$ for every $A$. Basically, the process
acts as a linear forwarder between two channels.

```agda
make-link : ∀{A B} -> Dual A B -> Σ[ P ∈ Process (A :: B :: []) ] LinkFree P
make-link d-𝟘-⊤ = _ , fail (split-r (split-l split-e))
make-link d-⊤-𝟘 = _ , fail (split-l (split-r split-e))
make-link d-𝟙-⊥ = _ , wait (split-r (split-l split-e)) close
make-link d-⊥-𝟙 = _ , wait (split-l (split-r split-e)) close
make-link (d-&-⊕ d e) with make-link (dual-symm d) | make-link (dual-symm e)
... | _ , Plf | _ , Qlf = _ , case (split-l (split-r split-e))
                                   (select true (split-r (split-l split-e)) Plf)
                                   (select false (split-r (split-l split-e)) Qlf)
make-link (d-⊕-& d e) with make-link d | make-link e
... | _ , Plf | _ , Qlf = _ , case (split-r (split-l split-e))
                                   (select true (split-r (split-l split-e)) Plf)
                                     (select false (split-r (split-l split-e)) Qlf)
make-link (d-⊗-⅋ d e) with make-link d | make-link e
... | _ , Plf | _ , Qlf = _ , join (split-r (split-l split-e))
                                   (fork (split-r (split-r (split-l split-e)))
                                         (split-r (split-l split-e)) Plf Qlf)
make-link (d-⅋-⊗ d e) with make-link (dual-symm d) | make-link (dual-symm e)
... | _ , Plf | _ , Qlf = _ , join (split-l (split-r split-e))
                                   (fork (split-r (split-r (split-l split-e)))
                                         (split-r (split-l split-e)) Plf Qlf)
```

Then, link elimination is just a matter of recurring through the
structure of a process and expanding every occurrence of a link by
means of `make-link`.

```agda
link-elimination : ∀{Γ} (P : Process Γ) -> Σ[ Q ∈ Process Γ ] LinkFree Q
link-elimination (link d (split-l (split-r split-e))) = make-link d
link-elimination (link d (split-r (split-l split-e))) = make-link (dual-symm d)
link-elimination (fail p) = _ , fail p
link-elimination close = close , close
link-elimination (wait p P) with link-elimination P
... | Q , Qlf = _ , wait p Qlf
link-elimination (select x p P) with link-elimination P
... | _ , Qlf = _ , select x p Qlf
link-elimination (case p P Q) with link-elimination P | link-elimination Q
... | _ , Plf | _ , Qlf = _ , case p Plf Qlf
link-elimination (fork p q P Q) with link-elimination P | link-elimination Q
... | _ , Plf | _ , Qlf = _ , fork p q Plf Qlf
link-elimination (join p P) with link-elimination P
... | _ , Plf = _ , join p Plf
link-elimination (cut d p P Q) with link-elimination P | link-elimination Q
... | _ , Plf | _ , Qlf = _ , cut d p Plf Qlf
```
