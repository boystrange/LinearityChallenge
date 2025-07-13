# Cut elimination

This module proves the **cut elimination** property of the type
system, namely that if some typing context Γ is derivable, then
there exists a cut-free derivation for it.

## Imports

```agda
open import Data.Bool using (Bool; if_then_else_)
open import Data.Nat
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤m⊔n; m≤n+m; m≤n⊔m)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (Σ; _×_; _,_; ∃; Σ-syntax; ∃-syntax)

open import Induction.WellFounded

open import Type
open import Context
open import Process
open import Congruence
open import DeadlockFreedom
open import Termination
```

## Definitions

We say that a process is **cut free** if it contains no cuts. This
property is captured by the following predicate.

```agda
data CutFree : ∀{Γ} -> Process Γ -> Set where
  link :
    ∀{Γ A B}
    (d : Dual A B) (p : Γ ≃ [ A ] + [ B ]) -> CutFree (link d p)
  fail :
    ∀{Γ Δ} (p : Γ ≃ ⊤ , Δ) -> CutFree (fail p)
  wait :
    ∀{Γ Δ} (p : Γ ≃ ⊥ , Δ) {P : Process Δ} ->
    CutFree P -> CutFree (wait p P)
  case :
    ∀{Γ Δ A B} (p : Γ ≃ A & B , Δ)
    {P : Process (A :: Δ)} {Q : Process (B :: Δ)} ->
    CutFree P -> CutFree Q -> CutFree (case p P Q)
  join :
    ∀{Γ Δ A B} (p : Γ ≃ A ⅋ B , Δ)
    {P : Process (B :: A :: Δ)} ->
    CutFree P -> CutFree (join p P)
  close : CutFree close
  select :
    ∀{Γ Δ A B} (x : Bool) (p : Γ ≃ A ⊕ B , Δ)
    {P : Process ((if x then A else B) :: Δ)} ->
    CutFree P -> CutFree (select x p P)
  fork :
    ∀{Γ Δ Δ₁ Δ₂ A B} (p : Γ ≃ A ⊗ B , Δ) (q : Δ ≃ Δ₁ + Δ₂)
    {P : Process (A :: Δ₁)} {Q : Process (B :: Δ₂)} ->
    CutFree P -> CutFree Q -> CutFree (fork p q P Q)
```

## Proof of cut elimination

The proof of cut elimination relies on the [weak
termination](Termination.lagda.md) property. Basically, we reduce as
much as possible a process until it becomes structurally
precongruent to a thread. By definition of reduction and of
structural precongruent the thread turns out to be well typed in the
same typing context `Γ` as the original process. That is, it is a
proof of the sequent `⊢ Γ` that does **not** end in a cut. At that
point, it is enough to recursively eliminate all cuts in the
continuations of the thread to build a cut free proof of `⊢ Γ`. As
in the proof of weak termination, we need to convince Agda that each
recursive application of `cut-elimination` is performed on a
strictly smaller process. This again resorts to the `size` function
defined in the [termination module](Termination.lagda.md).

```agda
cut-elimination : ∀{Γ} (P : Process Γ) -> Σ[ Q ∈ Process Γ ] CutFree Q
cut-elimination P = aux P (<-wellFounded (size P))
  where
  aux : ∀{Γ} (P : Process Γ) -> Acc _<_ (size P) -> Σ[ Q ∈ Process Γ ] CutFree Q
  aux P (acc rs) with weak-termination P
  aux P (acc rs) | Q , reds , R , pc , Rth with ≤-trans (cong≤ pc) (reds≤ reds)
  aux P (acc rs) | _ , _ , link d p , _ , link _ _ | le = _ , link d p
  aux P (acc rs) | _ , _ , fail p , _ , fail _ | le = _ , fail p
  aux P (acc rs) | _ , _ , wait p P' , _ , wait _ | le with aux P' (rs le)
  ... | _ , Pcf = _ , wait p Pcf
  aux P (acc rs) | _ , _ , case p P₁ P₂ , _ , case _ | le
    with aux P₁ (rs (≤-trans (s≤s (m≤m⊔n (size P₁) (size P₂))) le)) |
         aux P₂ (rs (≤-trans (s≤s (m≤n⊔m (size P₁) (size P₂))) le))
  ... | _ , Pcf₁ | _ , Pcf₂ = _ , case p Pcf₁ Pcf₂
  aux P (acc rs) | _ , _ , join p P' , _ , join _ | le with aux P' (rs le)
  ... | _ , Pcf = _ , join p Pcf
  aux P (acc rs) | _ , _ , .close , _ , close | le = _ , close
  aux P (acc rs) | _ , _ , select x p P' , _ , select _ _ | le with aux P' (rs le)
  ... | _ , Pcf = _ , select x p Pcf
  aux P (acc rs) | _ , _ , fork p q P₁ P₂ , _ , fork _ _ | le
    with aux P₁ (rs (≤-trans (s≤s (m≤m+n (size P₁) (size P₂))) le)) |
         aux P₂ (rs (≤-trans (s≤s (m≤n+m (size P₂) (size P₁))) le))
  ... | _ , Pcf₁ | _ , Pcf₂ = _ , fork p q Pcf₁ Pcf₂
```
