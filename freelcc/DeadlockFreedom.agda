{-# OPTIONS --rewriting --guardedness #-}
open import Data.Unit using (tt)
open import Data.Sum
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.List.Base using ([]; _∷_; [_])
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (refl)

open import Type
open import Equivalence
open import Context
open import Process
open import Reduction
open import Congruence

data Link {n Σ} : ∀{Γ} → Proc {n} Σ Γ → Set where
  link : ∀{Γ A B} (eq : dual A ≈ B) (p : Γ ≃ [ A ] + [ B ]) → Link (link eq (ch ⟨ p ⟩ ch))

data Input {n Σ} : ∀{Γ} → Proc {n} Σ Γ → Set where
  fail : ∀{Γ Δ} (p : Γ ≃ [] + Δ) → Input (fail (ch ⟨ < p ⟩ tt))
  wait : ∀{Γ Δ P} (p : Γ ≃ [] + Δ) → Input (wait (ch ⟨ < p ⟩ P))
  case : ∀{Γ Δ A B P Q} (p : Γ ≃ [] + Δ) → Input (case {A = A} {B} (ch ⟨ < p ⟩ (P , Q)))
  join : ∀{Γ Δ A B P} (p : Γ ≃ [] + Δ) → Input (join {A = A} {B} (ch ⟨ < p ⟩ P))

data Output {n Σ} : ∀{Γ} → Proc {n} Σ Γ → Set where
  close    : Output (close ch)
  select-l : ∀{Γ Δ A B P} (p : Γ ≃ [] + Δ) → Output (select {A = A} {B} (ch ⟨ < p ⟩ inj₁ P))
  select-r : ∀{Γ Δ A B P} (p : Γ ≃ [] + Δ) → Output (select {A = A} {B} (ch ⟨ < p ⟩ inj₂ P))
  fork     : ∀{Γ Δ Δ₁ Δ₂ A B P Q} (p : Γ ≃ [] + Δ) (q : Δ ≃ Δ₁ + Δ₂) → Output (fork {A = A} {B} (ch ⟨ < p ⟩ (P ⟨ q ⟩ Q)))

data Delayed {n Σ} : ∀{Γ} → Proc {n} Σ Γ → Set where
  fail     : ∀{C Γ Δ} (p : Γ ≃ [ ⊤ ] + Δ) → Delayed (fail (ch ⟨ >_ {_} {C} p ⟩ tt))
  wait     : ∀{C Γ Δ P} (p : Γ ≃ [ ⊥ ] + Δ) → Delayed (wait (ch ⟨ >_ {_} {C} p ⟩ P))
  case     : ∀{Γ Δ C A B P} (p : Γ ≃ [ A & B ] + Δ) → Delayed (case {A = A} {B} (ch ⟨ >_ {_} {C} p ⟩ P))
  select-l : ∀{Γ Δ C A B P} (p : Γ ≃ [ A ⊕ B ] + Δ) → Delayed (select (ch ⟨ >_ {_} {C} p ⟩ inj₁ P))
  select-r : ∀{Γ Δ C A B P} (p : Γ ≃ [ A ⊕ B ] + Δ) → Delayed (select (ch ⟨ >_ {_} {C} p ⟩ inj₂ P))
  join     : ∀{Γ Δ C A B P} (p : Γ ≃ [ A ⅋ B ] + Δ) → Delayed (join (ch ⟨ >_ {_} {C} p ⟩ P))
  fork-l   : ∀{Γ Δ Δ₁ Δ₂ C A B P Q} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂) →
             Delayed (fork (ch ⟨ >_ {_} {C} p ⟩ (P ⟨ < q ⟩ Q)))
  fork-r   : ∀{Γ Δ Δ₁ Δ₂ C A B P Q} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂) →
             Delayed (fork (ch ⟨ >_ {_} {C} p ⟩ (P ⟨ > q ⟩ Q)))

data Thread {n Σ Γ} (P : Proc {n} Σ Γ) : Set where
  link    : Link P → Thread P
  delayed : Delayed P → Thread P
  output  : Output P → Thread P
  input   : Input P → Thread P

Observable : ∀{n Σ Γ} → Proc {n} Σ Γ → Set
Observable P = ∃[ Q ] P ⊒ Q × Thread Q

Reducible : ∀{n Σ Γ} → Def Σ → Proc {n} Σ Γ → Set
Reducible ℙ P = ∃[ Q ] ℙ ⊢ P ↝ Q

Alive : ∀{n Σ Γ} → Def Σ → Proc {n} Σ Γ → Set
Alive ℙ P = Observable P ⊎ Reducible ℙ P

fail→thread : ∀{n Σ Γ Δ} (p : Γ ≃ [ ⊤ ] + Δ) → Thread {n} {Σ} (fail (ch ⟨ p ⟩ tt))
fail→thread (< p) = input (fail p)
fail→thread (> p) = delayed (fail p)

wait→thread : ∀{n Σ Γ Δ P} (p : Γ ≃ [ ⊥ ] + Δ) → Thread {n} {Σ} (wait (ch ⟨ p ⟩ P))
wait→thread (< p) = input (wait p)
wait→thread (> p) = delayed (wait p)

case→thread : ∀{n Σ A B Γ Δ P} (p : Γ ≃ [ A & B ] + Δ) → Thread {n} {Σ} (case (ch ⟨ p ⟩ P))
case→thread (< p) = input (case p)
case→thread (> p) = delayed (case p)

left→thread : ∀{n Σ A B Γ Δ P} (p : Γ ≃ [ A ⊕ B ] + Δ) → Thread {n} {Σ} (select (ch ⟨ p ⟩ inj₁ P))
left→thread (< p) = output (select-l p)
left→thread (> p) = delayed (select-l p)

right→thread : ∀{n Σ A B Γ Δ P} (p : Γ ≃ [ A ⊕ B ] + Δ) → Thread {n} {Σ} (select (ch ⟨ p ⟩ inj₂ P))
right→thread (< p) = output (select-r p)
right→thread (> p) = delayed (select-r p)

join→thread : ∀{n Σ A B Γ Δ P} (p : Γ ≃ [ A ⅋ B ] + Δ) → Thread {n} {Σ} (join (ch ⟨ p ⟩ P))
join→thread (< p) = input (join p)
join→thread (> p) = delayed (join p)

fork→thread : ∀{n Σ A B Γ Δ Δ₁ Δ₂ P Q} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂) → Thread {n} {Σ} (fork (ch ⟨ p ⟩ (P ⟨ q ⟩ Q)))
fork→thread (< p) q = output (fork p q)
fork→thread (> p) (< q) = delayed (fork-l p q)
fork→thread (> p) (> q) = delayed (fork-r p q)

data CanonicalCut {n Σ Γ} : Proc {n} Σ Γ → Set where
  cc-link    : ∀{Γ₁ Γ₂ A B P Q} (eq : dual A ≈ B) (p : Γ ≃ Γ₁ + Γ₂) →
               Link P → CanonicalCut (cut {A = A} eq (P ⟨ p ⟩ Q))
  cc-redex   : ∀{Γ₁ Γ₂ A B P Q} (eq : dual A ≈ B) (p : Γ ≃ Γ₁ + Γ₂) →
               Input P → Output Q → CanonicalCut (cut {A = A} eq (P ⟨ p ⟩ Q))
  cc-delayed : ∀{Γ₁ Γ₂ A B P Q} (eq : dual A ≈ B) (p : Γ ≃ Γ₁ + Γ₂) →
               Delayed P → CanonicalCut (cut {A = A} eq (P ⟨ p ⟩ Q))

output-output : ∀{n Σ A B Γ Δ P Q} → dual A ≈ B → ¬ (Output {n} {Σ} {A ∷ Γ} P × Output {n} {Σ} {B ∷ Δ} Q)
output-output eq (close , close) = {!!}
output-output eq (close , select-l p) = {!!}
output-output eq (close , select-r p) = {!!}
output-output eq (close , fork p q) = {!!}
output-output eq (select-l p , close) = {!!}
output-output eq (select-l p , select-l p₁) = {!!}
output-output eq (select-l p , select-r p₁) = {!!}
output-output eq (select-l p , fork p₁ q) = {!!}
output-output eq (select-r p , close) = {!!}
output-output eq (select-r p , select-l p₁) = {!!}
output-output eq (select-r p , select-r p₁) = {!!}
output-output eq (select-r p , fork p₁ q) = {!!}
output-output eq (fork p q , close) = {!!}
output-output eq (fork p q , select-l p₁) = {!!}
output-output eq (fork p q , select-r p₁) = {!!}
output-output eq (fork p q , fork p₁ q₁) = {!!}

input-input : ∀{n Σ A B Γ Δ P Q} → dual A ≈ B → ¬ (Input {n} {Σ} {A ∷ Γ} P × Input {n} {Σ} {B ∷ Δ} Q)
input-input eq (P , Q) = {!!}

canonical-cut : ∀{n Σ A B Γ Γ₁ Γ₂ P Q} (eq : dual A ≈ B) (p : Γ ≃ Γ₁ + Γ₂) →
                Thread {n} {Σ} P → Thread Q → ∃[ R ] CanonicalCut R × cut {A = A} eq (P ⟨ p ⟩ Q) ⊒ R
canonical-cut eq pc (link x) Qt = _ , cc-link eq pc x , s-refl
canonical-cut eq pc Pt (link y) = _ , cc-link (≈sym (≈dual eq)) (+-comm pc) y , s-comm eq pc
canonical-cut eq pc (delayed x) Qt = _ , cc-delayed eq pc x , s-refl
canonical-cut eq pc Pt (delayed y) = _ , cc-delayed (≈sym (≈dual eq)) (+-comm pc) y , s-comm eq pc
canonical-cut eq pc (output x) (output y) = contradiction (x , y) {!!}
canonical-cut eq pc (output x) (input y) = _ , cc-redex (≈sym (≈dual eq)) (+-comm pc) y x , s-comm eq pc
canonical-cut eq pc (input x) (output y) = _ , cc-redex eq pc x y , s-refl
canonical-cut eq pc (input x) (input y) = contradiction (x , y) {!!}

-- ⊒Alive : ∀{Γ} {P Q : Proc Γ} → P ⊒ Q → Alive Q → Alive P
-- ⊒Alive pcong (inj₁ (_ , x , th)) = inj₁ (_ , s-tran pcong x , th)
-- ⊒Alive pcong (inj₂ (_ , red)) = inj₂ (_ , r-cong pcong red)

-- canonical-cut-alive : ∀{Γ} {C : Proc Γ} → CanonicalCut C → Alive C
-- canonical-cut-alive (cc-link pc (link (< > •))) = inj₂ (_ , r-link pc)
-- canonical-cut-alive (cc-link pc (link (> < •))) =
--   inj₂ (_ , r-cong (s-cong pc (s-link _) s-refl) (r-link pc))
-- canonical-cut-alive (cc-redex pc (inj₁ (wait p)) close) with +-empty-l p | +-empty-l (+-comm pc)
-- ... | refl | refl = inj₂ (_ , r-close pc p)
-- canonical-cut-alive (cc-redex pc (inj₁ (case p)) (select-l q)) with +-empty-l p | +-empty-l q
-- ... | refl | refl = inj₂ (_ , r-select-l pc p q)
-- canonical-cut-alive (cc-redex pc (inj₁ (case p)) (select-r q)) with +-empty-l p | +-empty-l q
-- ... | refl | refl = inj₂ (_ , r-select-r pc p q)
-- canonical-cut-alive (cc-redex pc (inj₁ (join p)) (fork q r)) with +-empty-l p | +-empty-l q
-- ... | refl | refl = inj₂ (_ , r-fork pc p r q)
-- canonical-cut-alive (cc-delayed pc (fail p)) =
--   let _ , _ , p' = +-assoc-l pc p in
--   inj₁ (_ , s-fail pc p , fail→thread p')
-- canonical-cut-alive (cc-delayed pc (wait p)) =
--   let _ , _ , p' = +-assoc-l pc p in
--   inj₁ (_ , s-wait pc p , wait→thread p')
-- canonical-cut-alive (cc-delayed pc (case p)) =
--   let _ , _ , p' = +-assoc-l pc p in
--   inj₁ (_ , s-case pc p , case→thread p')
-- canonical-cut-alive (cc-delayed pc (join p)) =
--   let _ , _ , p' = +-assoc-l pc p in
--   inj₁ (_ , s-join pc p , join→thread p')
-- canonical-cut-alive (cc-delayed pc (select-l p)) =
--   let _ , _ , p' = +-assoc-l pc p in
--   inj₁ (_ , s-select-l pc p , left→thread p')
-- canonical-cut-alive (cc-delayed pc (select-r p)) =
--   let _ , _ , p' = +-assoc-l pc p in
--   inj₁ (_ , s-select-r pc p , right→thread p')
-- canonical-cut-alive (cc-delayed p (fork-l q r)) =
--   let _ , p' , q' = +-assoc-l p q in
--   let _ , p'' , r' = +-assoc-l p' r in
--   let _ , q'' , r'' = +-assoc-r r' (+-comm p'') in
--   inj₁ (_ , s-fork-l p q r , fork→thread q' r'')
-- canonical-cut-alive (cc-delayed p (fork-r q r)) =
--   let _ , p' , q' = +-assoc-l p q in
--   let _ , p'' , r' = +-assoc-l p' r in
--   inj₁ (_ , s-fork-r p q r , fork→thread q' r')

-- deadlock-freedom : ∀{Γ} (P : Proc Γ) → Alive P
-- deadlock-freedom (link (ch ⟨ p ⟩ ch)) = inj₁ (_ , s-refl , link (link p))
-- deadlock-freedom (fail (ch ⟨ p ⟩ _)) = inj₁ (_ , s-refl , fail→thread p)
-- deadlock-freedom (wait (ch ⟨ p ⟩ _)) = inj₁ (_ , s-refl , wait→thread p)
-- deadlock-freedom (close ch) = inj₁ (_ , s-refl , output close)
-- deadlock-freedom (case (ch ⟨ p ⟩ _)) = inj₁ (_ , s-refl , case→thread p)
-- deadlock-freedom (select (ch ⟨ p ⟩ inj₁ _)) = inj₁ (_ , s-refl , left→thread p)
-- deadlock-freedom (select (ch ⟨ p ⟩ inj₂ _)) = inj₁ (_ , s-refl , right→thread p)
-- deadlock-freedom (join (ch ⟨ p ⟩ _)) = inj₁ (_ , s-refl , join→thread p)
-- deadlock-freedom (fork (ch ⟨ p ⟩ (P ⟨ q ⟩ Q))) = inj₁ (_ , s-refl , fork→thread p q)
-- deadlock-freedom (cut (P ⟨ p ⟩ Q)) with deadlock-freedom P
-- ... | inj₂ (_ , red) = inj₂ (_ , r-cut p red)
-- ... | inj₁ (_ , Pc , Pt) with deadlock-freedom Q
-- ... | inj₂ (_ , red) = inj₂ (_ , r-cong (s-comm p) (r-cut (+-comm p) red))
-- ... | inj₁ (_ , Qc , Qt) with canonical-cut p Pt Qt
-- ... | _ , cc , pcong = ⊒Alive (s-tran (s-cong p Pc Qc) pcong) (canonical-cut-alive cc)
