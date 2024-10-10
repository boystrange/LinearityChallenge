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
open import Kind
open import Reduction
open import Congruence

-- LIVENESS

Observable : ∀{Γ} -> Process Γ -> Set
Observable P = ∃[ Q ] P ⊒ Q × Thread Q

Reducible : ∀{Γ} -> Process Γ -> Set
Reducible P = ∃[ Q ] P ~> Q

data Closed : ∀{Γ} -> Process Γ -> Set where
  close : Closed (Close (split-l split-e))

thread-closed : {P : Process [ One ]} -> Thread P -> Closed P
thread-closed (link d (split-l ()))
thread-closed (link d (split-r ()))
thread-closed (fail (split-r ()))
thread-closed (wait (split-r ()))
thread-closed (case (split-r ()))
thread-closed (join (split-r ()))
thread-closed (close (split-l split-e)) = close
thread-closed (select x (split-r ()))
thread-closed (fork (split-r ()) q)

⊒Closed : {P Q : Process [ One ]} -> P ⊒ Q -> Closed Q -> Closed P
⊒Closed s-refl Qc = Qc
⊒Closed (s-tran pcong₁ pcong₂) Qc = ⊒Closed pcong₁ (⊒Closed pcong₂ Qc)

Live : ∀{Γ} -> Process Γ -> Set
Live P = Observable P ⊎ Reducible P

Live' : Process [ One ] -> Set
Live' P = Closed P ⊎ Reducible P

⊒Live : ∀{Γ} {P Q : Process Γ} -> P ⊒ Q -> Live Q -> Live P
⊒Live pcong (inj₁ (_ , x , th)) = inj₁ (_ , s-tran pcong x , th)
⊒Live pcong (inj₂ (_ , red)) = inj₂ (_ , r-cong pcong red)

live-cut : ∀{Γ} {P : Process Γ} -> CanonicalCut P -> Live P
live-cut (cc-link d p (link e (split-l (split-r split-e)))) with dual-fun-r e d
... | refl = inj₂ (_ , r-link d e p)
live-cut (cc-link d p (link e (split-r (split-l split-e)))) with dual-fun-l e (dual-symm d)
... | refl = inj₂ (_ , r-cong (s-cong-l d p (s-link e (split-r (split-l split-e)))) (r-link d (dual-symm e) p))
live-cut (cc-redex dual-one-bot p (close (split-l split-e)) (wait q)) with +-empty-l q | +-empty-l p
... | refl | refl = inj₂ (_ , r-close p q)
live-cut (cc-redex (dual-plus-with d e) p (select false q) (case r)) with +-empty-l q | +-empty-l r
... | refl | refl = inj₂ (_ , r-select-r d e p q r)
live-cut (cc-redex (dual-plus-with d e) p (select true q) (case r)) with +-empty-l q | +-empty-l r
... | refl | refl = inj₂ (_ , r-select-l d e p q r)
live-cut (cc-redex (dual-fork-join d e) p (fork q r) (join s)) with +-empty-l q | +-empty-l s
... | refl | refl = inj₂ (_ , r-fork d e p s r q)
live-cut (cc-next d p (fail q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , s-fail d p q , fail q')
live-cut (cc-next d p (wait q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , s-wait d p q , wait q')
live-cut (cc-next d p (case q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , s-case d p q , case q')
live-cut (cc-next d p (join q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , s-join d p q , join q')
live-cut (cc-next d p (select false q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , s-select-r d p q , select false q')
live-cut (cc-next d p (select true q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , s-select-l d p q , select true q')
live-cut (cc-next d p (fork-l q r)) =
  let _ , p' , q' = +-assoc-l p q in
  let _ , p'' , r' = +-assoc-l p' r in
  let _ , q'' , r'' = +-assoc-r r' (+-comm p'') in
  inj₁ (_ , s-fork-l d p q r , fork q' r'')
live-cut (cc-next d p (fork-r q r)) =
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

live' : (P : Process [ One ]) -> Live' P
live' P with live P
... | inj₂ x = inj₂ x
... | inj₁ (Q , pcong , Qt) = inj₁ (⊒Closed pcong (thread-closed Qt))

-- TODO: MOVE THIS RELATION TO LANGUAGE

DeadlockFree : ∀{Γ} -> Process Γ -> Set
DeadlockFree {Γ} P = ∀(Q : Process Γ) -> P ~>* Q -> Live Q

DeadlockFree' : Process [ One ] -> Set
DeadlockFree' P = ∀(Q : Process [ One ]) -> P ~>* Q -> Live' Q

deadlock-freedom : ∀{Γ} (P : Process Γ) -> DeadlockFree P
deadlock-freedom P Q reds = live Q

deadlock-freedom' : (P : Process [ One ]) -> DeadlockFree' P
deadlock-freedom' P Q reds = live' Q
