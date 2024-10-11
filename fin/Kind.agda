open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Bool using (Bool; if_then_else_)
open Bool using (true; false)

open import Relation.Nullary using (¬_; contradiction)

open import Type
open import Context
open import Process
open import Congruence

data Link {Γ} : Process Γ -> Set where
  link :
    ∀{A B} (d : Dual A B) (p : Γ ≃ [ A ] + [ B ]) -> Link (link d p)

data Input : ∀{Γ} -> Process Γ -> Set where
  fail :
    ∀{Γ Δ}
    (p : Γ ≃ [] + Δ) -> Input (fail (split-l p))
  wait :
    ∀{Γ Δ} (p : Γ ≃ [] + Δ) {P : Process Δ} -> Input (wait (split-l p) P)
  case :
    ∀{Γ Δ A B} (p : Γ ≃ [] + Δ) {P : Process (A :: Δ)} {Q : Process (B :: Δ)} ->
    Input (branch (split-l p) P Q)
  join :
    ∀{Γ Δ A B} (p : Γ ≃ [] + Δ) {P : Process (B :: A :: Δ)} ->
    Input (join (split-l p) P)

data Output : ∀{Γ} -> Process Γ -> Set where
  close :
    ∀{Γ} (p : Γ ≃ [ One ] + []) -> Output (close p)
  select :
    ∀{Γ Δ A B} (x : Bool) (p : Γ ≃ [] + Δ) {P : Process ((if x then A else B) :: Δ)} ->
    Output (select x (split-l p) P)
  fork :
    ∀{Γ Δ Δ₁ Δ₂ A B} (p : Γ ≃ [] + Δ) (q : Δ ≃ Δ₁ + Δ₂)
    {P : Process (A :: Δ₁)} {Q : Process (B :: Δ₂)} ->
    Output (fork (split-l p) q P Q)

Action : ∀{Γ} -> Process Γ -> Set
Action P = Input P ⊎ Output P

data ThreadNext : ∀{Γ} -> Process Γ -> Set where
  fail :
    ∀{A Γ Δ}
    (p : Γ ≃ [ Top ] + Δ) -> ThreadNext (fail (split-r {A} p))
  wait :
    ∀{C Γ Δ} (p : Γ ≃ [ Bot ] + Δ) {P : Process (C :: Δ)} -> ThreadNext (wait (split-r p) P)
  case :
    ∀{Γ Δ C A B} (p : Γ ≃ [ A & B ] + Δ) {P : Process (A :: C :: Δ)} {Q : Process (B :: C :: Δ)} ->
    ThreadNext (branch (split-r p) P Q)
  join :
    ∀{Γ Δ C A B} (p : Γ ≃ [ A ⅋ B ] + Δ) {P : Process (B :: A :: C :: Δ)} ->
    ThreadNext (join (split-r p) P)
  select :
    ∀{Γ Δ C A B} (x : Bool) (p : Γ ≃ [ A ⊕ B ] + Δ) {P : Process ((if x then A else B) :: C :: Δ)} ->
    ThreadNext (select x (split-r p) P)
  fork-l :
    ∀{Γ Δ Δ₁ Δ₂ C A B} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂)
    {P : Process (A :: C :: Δ₁)} {Q : Process (B :: Δ₂)} ->
    ThreadNext (fork (split-r p) (split-l q) P Q)
  fork-r :
    ∀{Γ Δ Δ₁ Δ₂ C A B} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂)
    {P : Process (A :: Δ₁)} {Q : Process (B :: C :: Δ₂)} ->
    ThreadNext (fork (split-r p) (split-r q) P Q)

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

data CutFree {Γ} : Process Γ -> Set where
  link :
    ∀{A B}
    (d : Dual A B) (p : Γ ≃ [ A ] + [ B ]) -> CutFree (link d p)
  fail :
    ∀{Δ} (p : Γ ≃ [ Top ] + Δ) -> CutFree (fail p)
  wait :
    ∀{Δ} (p : Γ ≃ [ Bot ] + Δ) {P : Process Δ} -> CutFree P -> CutFree (wait p P)
  case :
    ∀{Δ A B} (p : Γ ≃ [ A & B ] + Δ) {P : Process (A :: Δ)} {Q : Process (B :: Δ)} ->
    CutFree P -> CutFree Q -> CutFree (branch p P Q)
  join :
    ∀{Δ A B} (p : Γ ≃ [ A ⅋ B ] + Δ) {P : Process (B :: A :: Δ)} ->
    CutFree P -> CutFree (join p P)
  close :
    ∀(p : Γ ≃ [ One ] + []) -> CutFree (close p)
  select :
    ∀{Δ A B} (x : Bool) (p : Γ ≃ [ A ⊕ B ] + Δ) {P : Process ((if x then A else B) :: Δ)} ->
    CutFree P -> CutFree (select x p P)
  fork :
    ∀{Δ Δ₁ Δ₂ A B} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂)
    {P : Process (A :: Δ₁)} {Q : Process (B :: Δ₂)} ->
    CutFree P -> CutFree Q -> CutFree (fork p q P Q)

thread-is : ∀{Γ} {P : Process Γ} -> Thread P ->
  Link P ⊎ ThreadNext P ⊎ Input P ⊎ Output P
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

-- CLASSIFICATION OF CUTS

data Cut {Γ} : Process Γ -> Set where
  cut :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)} ->
    Cut (cut d p P Q)

data CanonicalCut {Γ} : Process Γ -> Set where
  cc-link :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)} ->
    Link P -> CanonicalCut (cut d p P Q)
  cc-next :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)} ->
    ThreadNext P -> CanonicalCut (cut d p P Q)
  cc-redex :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)} ->
    Output P -> Input Q -> CanonicalCut (cut d p P Q)

input-input :
  ∀{Γ Δ A B} {P : Process (A :: Γ)} {Q : Process (B :: Δ)} ->
  Dual A B -> ¬ (Input P × Input Q)
input-input d-⊤-0 (fail p , ())
input-input d-⊥-1 (wait p , ())
input-input (d-&-⊕ d d₁) (case p , ())
input-input (d-⅋-⊗ d d₁) (join p , ())

output-output :
  ∀{Γ Δ A B} {P : Process (A :: Γ)} {Q : Process (B :: Δ)} ->
  Dual A B -> ¬ (Output P × Output Q)
output-output d-1-⊥ (close _ , close ())
output-output (d-⊕-& d d₁) (select _ p , close ())
output-output (d-⊗-⅋ d d₁) (fork p q , close ())

canonical-cut :
  ∀{Γ Γ₁ Γ₂ A B}
  {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)}
  (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) ->
  Thread P -> Thread Q ->
  ∃[ R ] CanonicalCut R × cut d p P Q ⊒ R
canonical-cut dc pc Pt Qt with thread-is Pt | thread-is Qt
... | inj₁ x | y = _ , cc-link dc pc x , s-refl
... | inj₂ (inj₁ x) | y = _ , cc-next dc pc x , s-refl
... | inj₂ (inj₂ x) | inj₁ y = _ , cc-link (dual-symm dc) (+-comm pc) y , s-comm dc (dual-symm dc) pc (+-comm pc)
... | inj₂ (inj₂ x) | inj₂ (inj₁ y) = _ , cc-next (dual-symm dc) (+-comm pc) y , s-comm dc (dual-symm dc) pc (+-comm pc)
... | inj₂ (inj₂ (inj₁ x)) | inj₂ (inj₂ (inj₁ y)) = contradiction (x , y) (input-input dc)
... | inj₂ (inj₂ (inj₁ x)) | inj₂ (inj₂ (inj₂ y)) = _ , cc-redex (dual-symm dc) (+-comm pc) y x , s-comm dc (dual-symm dc) pc (+-comm pc)
... | inj₂ (inj₂ (inj₂ x)) | inj₂ (inj₂ (inj₁ y)) = _ , cc-redex dc pc x y , s-refl
... | inj₂ (inj₂ (inj₂ x)) | inj₂ (inj₂ (inj₂ y)) = contradiction (x , y) (output-output dc)

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
