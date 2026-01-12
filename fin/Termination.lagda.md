# Termination

This module proves that the calculus is terminating.

## Imports

```agda
open import Data.Bool using (Bool)
open Bool using (true; false)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Sum
open import Data.Product using (Σ; _×_; _,_; ∃; Σ-syntax; ∃-syntax)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym)
open import Induction.WellFounded

open import Context
open import Process
open import Congruence
open import Reduction
open import DeadlockFreedom
```

## Size of a process

The proof of (weak) termination is not structurally
recursive. Therefore, in order to convince Agda that it is well
founded, it is necessary to introduce a **measure** for processes
that is shown to strictly reduce after each reduction step. The
following function provides the required measure. Essentially, `size
P` accounts for all the prefixes found in the process `P`, except
for `fail` which can be given a null measure.

```agda
size : ∀{Γ} -> Process Γ -> ℕ
size (link d p) = 1
size (fail p) = 0
size close = 1
size (wait p P) = suc (size P)
size (select x p P) = suc (size P)
size (case p P Q) = suc (size P ⊔ size Q)
size (fork p q P Q) = suc (size P + size Q)
size (join p P) = suc (size P)
size (cut d p P Q) = size P + size Q
```

The next auxiliary result shows that renaming does not change the
size of a process, as expected.

```agda
#size : ∀{Γ Δ} (P : Process Γ) (π : Γ # Δ) -> size (#process π P) ≡ size P
#size (link d p) π with #one+ π p
... | _ , q , π' with #one π'
... | refl = refl
#size (fail p) π = refl
#size close π with #one π
... | refl = refl
#size (wait p P) π with #one+ π p
... | _ , q , π' rewrite #size P π' = refl
#size (select x p P) π with #one+ π p
... | _ , q , π' rewrite #size P (#next π') = refl
#size (case p P Q) π with #one+ π p
... | _ , q , π' rewrite #size P (#next π') | #size Q (#next π') = refl
#size (fork p q P Q) π with #one+ π p
... | _ , p' , π' with #split π' q
... | _ , _ , q' , π₁ , π₂ rewrite #size P (#next π₁)| #size Q (#next π₂) = refl
#size (join p P) π with #one+ π p
... | _ , p' , π' rewrite #size P (#next (#next π')) = refl
#size (cut d p P Q) π with #split π p
... | _ , _ , p' , π₁ , π₂ rewrite #size P (#next π₁) | #size Q (#next π₂) = refl
```

Next is a result showing that structural precongruence does not
increase the size of a process. In fact, in all cases except for
`s-fail` the size of the process remains exactly the same.

```agda
cong≤ : ∀{Γ} {P Q : Process Γ} -> P ⊒ Q -> size Q ≤ size P
cong≤ {_} {cut d p P Q} (s-comm d d' p p')
  rewrite Data.Nat.Properties.+-comm (size Q) (size P) = ≤-refl
cong≤ {_} {_} (s-link _ _) = ≤-refl
cong≤ {_} {_} (s-fail d p q) = z≤n
cong≤ {_} {_} (s-wait d p q) = ≤-refl
cong≤ {_} {cut _ _ (select true _ P) _} (s-select-l d p q)
  rewrite #size P #here = ≤-refl
cong≤ {_} {cut _ _ (select false _ P) _} (s-select-r d p q)
  rewrite #size P #here = ≤-refl
cong≤ {_} {cut d p (case _ P Q) R} (s-case d p q)
  rewrite #size P #here | #size Q #here | sym (+-distribʳ-⊔ (size R) (size P) (size Q)) = ≤-refl
cong≤ {_} {cut d p (fork _ _ P Q) R} (s-fork-l d p q r)
  rewrite #size P #here = begin
    (suc (size P) + size R) + size Q ≡⟨ +-assoc (suc (size P)) (size R) (size Q) ⟩
    suc (size P) + (size R + size Q) ≡⟨ cong (suc (size P) +_) (Data.Nat.Properties.+-comm (size R) (size Q)) ⟩
    suc (size P) + (size Q + size R) ≡⟨ sym (+-assoc (suc (size P)) (size Q) (size R)) ⟩
    (suc (size P) + size Q) + size R ∎
  where open ≤-Reasoning
cong≤ {_} {cut d p (fork _ _ P Q) R} (s-fork-r d p q r)
  rewrite #size Q #here | +-assoc (size P) (size Q) (size R) = ≤-refl
cong≤ {_} {cut d p (join _ P) _} (s-join d p q)
  rewrite #size P (#tran (#next #here) #here) = ≤-refl
cong≤ {_} {P} s-refl = ≤-refl
cong≤ {_} {P} (s-tran pc₁ pc₂) = ≤-trans (cong≤ pc₂) (cong≤ pc₁)
cong≤ {_} {cut d p _ R} (s-cong-l d p pc) = +-monoˡ-≤ (size R) (cong≤ pc)
```

Finally, we prove that reductions decrease the size of a
process. Intuitively, this follows from the fact that each reduction
removes two prefixes from a well-typed process. This observation
suggests that it would be sufficient to account for only one prefix
(say the one associated with the positive logical connective) in
order to prove termination. We choose to take into account both
prefixes because this simplifies the proof of [cut
elimination](CutElimination.lagda.md).

```
red< : ∀{Γ} {P Q : Process Γ} -> P ~> Q -> size Q < size P
red< {_} {cut _ _ (link _ _) P} (r-link _ _ p) rewrite #size P (#cons p) = ≤-refl
red< {_} (r-close _ _) = s≤s (n≤1+n _)
red< {_} {cut _ _ (select true _ P) (case _ Q R)} (r-select-l d e p p₀ q₀) = begin
  suc (size P) + size Q            ≤⟨ +-monoʳ-≤ (suc (size P)) (m≤m⊔n (size Q) (size R)) ⟩
  suc (size P) + (size Q ⊔ size R) ≤⟨ +-monoʳ-≤ (suc (size P)) (n≤1+n _) ⟩
  suc (size P) + suc (size Q ⊔ size R) ∎
  where open ≤-Reasoning
red< {_} {cut _ _ (select false _ P) (case _ Q R)} (r-select-r d e p p₀ q₀) = begin
  suc (size P) + size R            ≤⟨ +-monoʳ-≤ (suc (size P)) (m≤n⊔m (size Q) (size R)) ⟩
  suc (size P) + (size Q ⊔ size R) ≤⟨ +-monoʳ-≤ (suc (size P)) (n≤1+n _) ⟩
  suc (size P) + suc (size Q ⊔ size R) ∎
  where open ≤-Reasoning
red< {_} {cut _ p (fork _ _ P Q) (join _ R)} (r-fork d e p p₀ q q₀) =
  begin
    suc (size P + (size Q + size R)) ≡⟨ cong suc (sym (+-assoc (size P) (size Q) (size R))) ⟩
    (suc (size P + size Q) + size R) ≤⟨ +-monoʳ-≤ (suc (size P + size Q)) (n≤1+n _) ⟩
    (suc (size P + size Q) + suc (size R))
  ∎
  where open ≤-Reasoning
red< {_} {cut d q P R} (r-cut d q red) = +-monoˡ-< (size R) (red< red)
red< {_} {P} (r-cong pc red) = ≤-trans (red< red) (cong≤ pc)
```

The result easily extends to arbitrary sequences of reductions in
the expected way.

```agda
reds≤ : ∀{Γ} {P Q : Process Γ} -> P => Q -> size Q ≤ size P
reds≤ refl = ≤-refl
reds≤ (tran red reds) = ≤-trans (reds≤ reds) (<⇒≤ (red< red))
```

## Termination Results

Weak termination is the existence of a reduction sequence that leads
to an observable process, namely a process that is structurally
precongruent to a thread.

```agda
weak-termination : ∀{Γ} (P : Process Γ) -> ∃[ Q ] P => Q × Observable Q
weak-termination P = aux P (<-wellFounded (size P))
  where
    aux : ∀{Γ} (P : Process Γ) -> Acc _<_ (size P) -> ∃[ Q ] P => Q × Observable Q
    aux P ac with live P
    aux P (acc rs) | inj₁ obs = _ , refl , obs
    aux P (acc rs) | inj₂ (R , red) with aux R (rs (red< red))
    ... | Q , reds , obs = Q , tran red reds , obs
```

Strong termination is the existence of an upper bound for *every*
reduction sequence.

```agda
strong-termination : ∀{Γ} (P Q : Process Γ) -> ∃[ n ] ((reds : P => Q) -> run-length reds ≤ n)
strong-termination P Q = size P , aux
  where
    aux : ∀{Γ} {P Q : Process Γ} (reds : P => Q) -> run-length reds ≤ size P
    aux refl = z≤n
    aux (tran red reds) = ≤-trans (s≤s (aux reds)) (red< red)
```
