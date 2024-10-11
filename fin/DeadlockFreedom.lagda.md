# Deadlock Freedom

This module proves two deadlock freedom results.

## Imports

```agda
open import Data.Sum
open import Data.Product using (Σ; _×_; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Bool using (Bool; if_then_else_)
open Bool using (true; false)

open import Relation.Nullary using (¬_; contradiction)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl)

open import Type
open import Context
open import Process
open import Reduction
open import Congruence
```

## Additional Process Classification

We introduce further classes of processes, distinguishing between
**threads** (sequential processes) and **cuts** (parallel
compositions of processes).

```agda
data Thread {Γ} : Process Γ -> Set where
  link :
    ∀{A B}
    (d : Dual A B) (p : Γ ≃ [ A ] + [ B ]) -> Thread (link d p)
  fail :
    ∀{Δ}
    (p : Γ ≃ [ Top ] + Δ) -> Thread (fail p)
  wait :
    ∀{Δ} (p : Γ ≃ [ Bot ] + Δ) {P : Process Δ} -> Thread (wait p P)
  case :
    ∀{Δ A B} (p : Γ ≃ [ A & B ] + Δ) {P : Process (A :: Δ)} {Q : Process (B :: Δ)} ->
    Thread (branch p P Q)
  join :
    ∀{Δ A B} (p : Γ ≃ [ A ⅋ B ] + Δ) {P : Process (B :: A :: Δ)} ->
    Thread (join p P)
  close :
    ∀(p : Γ ≃ [ One ] + []) -> Thread (close p)
  select :
    ∀{Δ A B} (x : Bool) (p : Γ ≃ [ A ⊕ B ] + Δ) {P : Process ((if x then A else B) :: Δ)} ->
    Thread (select x p P)
  fork :
    ∀{Δ Δ₁ Δ₂ A B} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂)
    {P : Process (A :: Δ₁)} {Q : Process (B :: Δ₂)} ->
    Thread (fork p q P Q)

data Cut {Γ} : Process Γ -> Set where
  cut :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)} ->
    Cut (cut d p P Q)
```

Every process is either a thread or a cut.

```agda
process-is : ∀{Γ} (P : Process Γ) -> Thread P ⊎ Cut P
process-is (close p) = inj₁ (close p)
process-is (link d p) = inj₁ (link d p)
process-is (fail p) = inj₁ (fail p)
process-is (wait p P) = inj₁ (wait p)
process-is (select x p P) = inj₁ (select x p)
process-is (branch p P Q) = inj₁ (case p)
process-is (fork p q P Q) = inj₁ (fork p q)
process-is (join p P) = inj₁ (join p)
process-is (cut d p P Q) = inj₂ (cut d p)
```

## Thread Classification

Concerning threads, we have already made a distinction between
`Input` and `Output` threads. Here we further distinguish links and
**delayed** threads, namely those threads beginning with an action
on a channel different from the youngest one.

```agda
data Link {Γ} : Process Γ -> Set where
  link :
    ∀{A B} (d : Dual A B) (p : Γ ≃ [ A ] + [ B ]) -> Link (link d p)

data Delayed : ∀{Γ} -> Process Γ -> Set where
  fail :
    ∀{A Γ Δ}
    (p : Γ ≃ [ Top ] + Δ) -> Delayed (fail (split-r {A} p))
  wait :
    ∀{C Γ Δ} (p : Γ ≃ [ Bot ] + Δ) {P : Process (C :: Δ)} -> Delayed (wait (split-r p) P)
  case :
    ∀{Γ Δ C A B} (p : Γ ≃ [ A & B ] + Δ) {P : Process (A :: C :: Δ)} {Q : Process (B :: C :: Δ)} ->
    Delayed (branch (split-r p) P Q)
  join :
    ∀{Γ Δ C A B} (p : Γ ≃ [ A ⅋ B ] + Δ) {P : Process (B :: A :: C :: Δ)} ->
    Delayed (join (split-r p) P)
  select :
    ∀{Γ Δ C A B} (x : Bool) (p : Γ ≃ [ A ⊕ B ] + Δ) {P : Process ((if x then A else B) :: C :: Δ)} ->
    Delayed (select x (split-r p) P)
  fork-l :
    ∀{Γ Δ Δ₁ Δ₂ C A B} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂)
    {P : Process (A :: C :: Δ₁)} {Q : Process (B :: Δ₂)} ->
    Delayed (fork (split-r p) (split-l q) P Q)
  fork-r :
    ∀{Γ Δ Δ₁ Δ₂ C A B} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂)
    {P : Process (A :: Δ₁)} {Q : Process (B :: C :: Δ₂)} ->
    Delayed (fork (split-r p) (split-r q) P Q)
```

Every thread is either a link, a delayed thread, an input or an
output.

```agda
thread-is : ∀{Γ} {P : Process Γ} -> Thread P ->
  Link P ⊎ Delayed P ⊎ Input P ⊎ Output P
thread-is (link d p) = inj₁ (link d p)
thread-is (fail (split-l p)) = inj₂ (inj₂ (inj₁ (fail p)))
thread-is (fail (split-r p)) = inj₂ (inj₁ (fail p))
thread-is (wait (split-l p)) = inj₂ (inj₂ (inj₁ (wait p)))
thread-is (wait (split-r p)) = inj₂ (inj₁ (wait p))
thread-is (case (split-l p)) = inj₂ (inj₂ (inj₁ (case p)))
thread-is (case (split-r p)) = inj₂ (inj₁ (case p))
thread-is (join (split-l p)) = inj₂ (inj₂ (inj₁ (join p)))
thread-is (join (split-r p)) = inj₂ (inj₁ (join p))
thread-is (close p) = inj₂ (inj₂ (inj₂ (close p)))
thread-is (select x (split-l p)) = inj₂ (inj₂ (inj₂ (select x p)))
thread-is (select x (split-r p)) = inj₂ (inj₁ (select x p))
thread-is (fork (split-l p) q) = inj₂ (inj₂ (inj₂ (fork p q)))
thread-is (fork (split-r p) (split-l q)) = inj₂ (inj₁ (fork-l p q))
thread-is (fork (split-r p) (split-r q)) = inj₂ (inj₁ (fork-r p q))
```

## Canonical Cuts

Structural precongruence and reduction operate on cuts having a
particular form, which we call **canonical**.

```agda
data CanonicalCut {Γ} : Process Γ -> Set where
  cc-link :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)} ->
    Link P -> CanonicalCut (cut d p P Q)
  cc-delayed :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)} ->
    Delayed P -> CanonicalCut (cut d p P Q)
  cc-redex :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)} ->
    Output P -> Input Q -> CanonicalCut (cut d p P Q)
```

Every cut between two threads is structurally precongruent to a
canonical cut.

```agda
canonical-cut :
  ∀{Γ Γ₁ Γ₂ A B}
  {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)}
  (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) ->
  Thread P -> Thread Q ->
  ∃[ R ] CanonicalCut R × cut d p P Q ⊒ R
canonical-cut dc pc Pt Qt with thread-is Pt | thread-is Qt
... | inj₁ x | y = _ , cc-link dc pc x , s-refl
... | inj₂ (inj₁ x) | y = _ , cc-delayed dc pc x , s-refl
... | inj₂ (inj₂ x) | inj₁ y = _ , cc-link (dual-symm dc) (+-comm pc) y , s-comm dc (dual-symm dc) pc (+-comm pc)
... | inj₂ (inj₂ x) | inj₂ (inj₁ y) = _ , cc-delayed (dual-symm dc) (+-comm pc) y , s-comm dc (dual-symm dc) pc (+-comm pc)
... | inj₂ (inj₂ (inj₁ x)) | inj₂ (inj₂ (inj₁ y)) = contradiction (x , y) (input-input dc)
... | inj₂ (inj₂ (inj₁ x)) | inj₂ (inj₂ (inj₂ y)) = _ , cc-redex (dual-symm dc) (+-comm pc) y x , s-comm dc (dual-symm dc) pc (+-comm pc)
... | inj₂ (inj₂ (inj₂ x)) | inj₂ (inj₂ (inj₁ y)) = _ , cc-redex dc pc x y , s-refl
... | inj₂ (inj₂ (inj₂ x)) | inj₂ (inj₂ (inj₂ y)) = contradiction (x , y) (output-output dc)
```

## Deadlock Freedom for General Processes

We say that a process is **observable** if it is (structurally
precongruent to) a thread. The terminology is justified by the fact
that a thread necessarily performs an action on a free channel.

```agda
Observable : ∀{Γ} -> Process Γ -> Set
Observable P = ∃[ Q ] P ⊒ Q × Thread Q
```

Then, we say that a process is **live** if it is either observable
or reducible. **Deadlock freedom** is then defined as the
preservation of liveness throughout reductions.

```agda
Live : ∀{Γ} -> Process Γ -> Set
Live P = Observable P ⊎ Reducible P

DeadlockFree : ∀{Γ} -> Process Γ -> Set
DeadlockFree {Γ} P = ∀(Q : Process Γ) -> P ~>* Q -> Live Q
```

A few auxiliary results about the `Live` predicate follow. First of
all, we see that `Live` is backward preserved by structural
precongruence.

```agda
⊒Live : ∀{Γ} {P Q : Process Γ} -> P ⊒ Q -> Live Q -> Live P
⊒Live pcong (inj₁ (_ , x , th)) = inj₁ (_ , s-tran pcong x , th)
⊒Live pcong (inj₂ (_ , red)) = inj₂ (_ , r-cong pcong red)
```

Also, every (well-typed) process is `Live`.

```agda
live-cut : ∀{Γ} {P : Process Γ} -> CanonicalCut P -> Live P
live-cut (cc-link d p (link e (split-l (split-r split-e)))) with dual-fun-r e d
... | refl = inj₂ (_ , r-link d e p)
live-cut (cc-link d p (link e (split-r (split-l split-e)))) with dual-fun-l e (dual-symm d)
... | refl = inj₂ (_ , r-cong (s-cong-l d p (s-link e (split-r (split-l split-e)))) (r-link d (dual-symm e) p))
live-cut (cc-redex d-1-⊥ p (close (split-l split-e)) (wait q)) with +-empty-l q | +-empty-l p
... | refl | refl = inj₂ (_ , r-close p q)
live-cut (cc-redex (d-⊕-& d e) p (select false q) (case r)) with +-empty-l q | +-empty-l r
... | refl | refl = inj₂ (_ , r-select-r d e p q r)
live-cut (cc-redex (d-⊕-& d e) p (select true q) (case r)) with +-empty-l q | +-empty-l r
... | refl | refl = inj₂ (_ , r-select-l d e p q r)
live-cut (cc-redex (d-⊗-⅋ d e) p (fork q r) (join s)) with +-empty-l q | +-empty-l s
... | refl | refl = inj₂ (_ , r-fork d e p s r q)
live-cut (cc-delayed d p (fail q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , s-fail d p q , fail q')
live-cut (cc-delayed d p (wait q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , s-wait d p q , wait q')
live-cut (cc-delayed d p (case q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , s-case d p q , case q')
live-cut (cc-delayed d p (join q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , s-join d p q , join q')
live-cut (cc-delayed d p (select false q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , s-select-r d p q , select false q')
live-cut (cc-delayed d p (select true q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , s-select-l d p q , select true q')
live-cut (cc-delayed d p (fork-l q r)) =
  let _ , p' , q' = +-assoc-l p q in
  let _ , p'' , r' = +-assoc-l p' r in
  let _ , q'' , r'' = +-assoc-r r' (+-comm p'') in
  inj₁ (_ , s-fork-l d p q r , fork q' r'')
live-cut (cc-delayed d p (fork-r q r)) =
  let _ , p' , q' = +-assoc-l p q in
  let _ , p'' , r' = +-assoc-l p' r in
  inj₁ (_ , s-fork-r d p q r , fork q' r')

live : ∀{Γ} (P : Process Γ) -> Live P
live P with process-is P
... | inj₁ x = inj₁ (_ , s-refl , x)
... | inj₂ (cut d p {P} {Q}) with live P
... | inj₂ (P' , red) = inj₂ (_ , r-cut d p red)
... | inj₁ (P' , Pc , Pt) with live Q
... | inj₂ (Q' , red) = inj₂ (_ , r-cong (s-comm d (dual-symm d) p (+-comm p)) (r-cut (dual-symm d) (+-comm p) red))
... | inj₁ (Q' , Qc , Qt) with canonical-cut d p Pt Qt
... | _ , cc , pcong = ⊒Live (s-tran (s-cong-2 d p Pc Qc) pcong) (live-cut cc)
```

At this point the proof of deadlock freedom is straightforward.

```agda
deadlock-freedom : ∀{Γ} (P : Process Γ) -> DeadlockFree P
deadlock-freedom P Q reds = live Q
```

## Deadlock Freedom for Closed Processes

Processes that are well typed in a singleton context containing only
the type `One` enjoy a specialized deadlock-freedom result that more
closely resembles those for calculi/languages not based on logic. To
prove this version of deadlock freedom, let us introduce the `Close`
class to easily identify `close p` processes.

```agda
data Close : ∀{Γ} -> Process Γ -> Set where
  close : Close (close (split-l split-e))
```

It is easy to prove that the only thread that is well typed in the
singleton context `[ One ]` is `Close`.

```agda
thread-closed : {P : Process [ One ]} -> Thread P -> Close P
thread-closed (link d (split-l ()))
thread-closed (link d (split-r ()))
thread-closed (fail (split-r ()))
thread-closed (wait (split-r ()))
thread-closed (case (split-r ()))
thread-closed (join (split-r ()))
thread-closed (close (split-l split-e)) = close
thread-closed (select x (split-r ()))
thread-closed (fork (split-r ()) q)
```

Further, `Close` is backward preserved by structural precongruence.

```agda
⊒Close : {P Q : Process [ One ]} -> P ⊒ Q -> Close Q -> Close P
⊒Close s-refl Qc = Qc
⊒Close (s-tran pcong₁ pcong₂) Qc = ⊒Close pcong₁ (⊒Close pcong₂ Qc)
```

The specialized version of deadlock freedom that we prove is based
on `Live'` predicate that characterizes those processes that are
either `Close` or `Reducible`.

```agda
Live' : ∀{Γ} -> Process Γ -> Set
Live' P = Close P ⊎ Reducible P

DeadlockFree' : ∀{Γ} -> Process Γ -> Set
DeadlockFree' {Γ} P = ∀(Q : Process Γ) -> P ~>* Q -> Live' Q
```

Every process that is well typed in the singleton context `[ One ]`
is also `Live'` and therefore `DeadlockFree'`.

```agda
live' : (P : Process [ One ]) -> Live' P
live' P with live P
... | inj₂ x = inj₂ x
... | inj₁ (Q , pcong , Qt) = inj₁ (⊒Close pcong (thread-closed Qt))

deadlock-freedom' : (P : Process [ One ]) -> DeadlockFree' P
deadlock-freedom' P Q reds = live' Q
```
