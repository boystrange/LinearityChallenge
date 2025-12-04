{-# OPTIONS --rewriting #-}
open import Data.Sum
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.List.Base using ([]; _∷_; [_])
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality using (refl)

open import Type
open import Context
open import Permutations
open import Process
open import Reduction
open import Congruence

data Cut : ∀{Γ} → Process Γ → Set where
  cut : ∀{Γ Γ₁ Γ₂ A P Q} (p : Γ ≃ Γ₁ + Γ₂) -> Cut (cut {A} p P Q)

data Link : ∀{Γ} → Process Γ → Set where
  link : ∀{Γ A} (p : Γ ≃ [ A ] + [ dual A ]) → Link (link p)

data Input : ∀{Γ} → Process Γ → Set where
  fail : ∀{Γ Δ} (p : Γ ≃ [] + Δ) → Input (fail (< p))
  wait : ∀{Γ Δ P} (p : Γ ≃ [] + Δ) → Input (wait (< p) P)
  case : ∀{Γ Δ A B P Q} (p : Γ ≃ [] + Δ) → Input (case {A} {B} (< p) P Q)
  join : ∀{Γ Δ A B P} (p : Γ ≃ [] + Δ) → Input (join {A} {B} (< p) P)
  all  : ∀{A Γ Δ F} (p : Γ ≃ [] + Δ) -> Input (all {A} (< p) F)

data Output : ∀{Γ} → Process Γ → Set where
  close  : Output close
  left   : ∀{Γ Δ A B P} (p : Γ ≃ [] + Δ) → Output (left {A} {B} (< p) P)
  right  : ∀{Γ Δ A B P} (p : Γ ≃ [] + Δ) → Output (right {A} {B} (< p) P)
  fork   : ∀{Γ Δ Δ₁ Δ₂ A B P Q} (p : Γ ≃ [] + Δ) (q : Δ ≃ Δ₁ + Δ₂) -> Output (fork {A} {B} (< p) q P Q)
  ex     : ∀{A B Γ Δ P} (p : Γ ≃ [] + Δ) -> Output (ex {A} {B} (< p) P)

data Delayed : ∀{Γ} → Process Γ → Set where
  fail     : ∀{C Γ Δ} (p : Γ ∋ ⊤ ⊳ Δ) → Delayed (fail (>_ {C} p))
  wait     : ∀{C Γ Δ P} (p : Γ ∋ ⊥ ⊳ Δ) → Delayed (wait (>_ {C} p) P)
  case     : ∀{Γ Δ C A B P Q} (p : Γ ∋ A & B ⊳ Δ) → Delayed (case {A} {B} (>_ {C} p) P Q)
  join     : ∀{Γ Δ C A B P} (p : Γ ∋ A ⅋ B ⊳ Δ) → Delayed (join (>_ {C} p) P)
  left     : ∀{Γ Δ C A B P} (p : Γ ∋ A ⊕ B ⊳ Δ) → Delayed (left (>_ {C} p) P)
  right    : ∀{Γ Δ C A B P} (p : Γ ∋ A ⊕ B ⊳ Δ) → Delayed (right (>_ {C} p) P)
  fork-l   : ∀{Γ Δ Δ₁ Δ₂ C A B P Q} (p : Γ ∋ A ⊗ B ⊳ Δ) (q : Δ ≃ Δ₁ + Δ₂) →
             Delayed (fork (>_ {C} p) (< q) P Q)
  fork-r   : ∀{Γ Δ Δ₁ Δ₂ C A B P Q} (p : Γ ∋ A ⊗ B ⊳ Δ) (q : Δ ≃ Δ₁ + Δ₂) →
             Delayed (fork (>_ {C} p) (> q) P Q)
  client   : ∀{Γ Δ A C P} (p : Γ ∋ `? A ⊳ Δ) → Delayed (client (>_ {C} p) P)
  weaken   : ∀{Γ Δ A C P} (p : Γ ∋ `? A ⊳ Δ) → Delayed (weaken (>_ {C} p) P)
  contract : ∀{Γ Δ A C P} (p : Γ ∋ `? A ⊳ Δ) → Delayed (contract (>_ {C} p) P)
  ex       : ∀{A B C Γ Δ P} (p : Γ ∋ `∃ A ⊳ Δ) → Delayed (ex {A} {B} (>_ {C} p) P)
  all      : ∀{A C Γ Δ F} (p : Γ ∋ `∀ A ⊳ Δ) → Delayed (all (>_ {C} p) F)

data Client : ∀{Γ} → Process Γ → Set where
  client   : ∀{Γ Δ A P} (p : Γ ≃ [] + Δ) → Client (client {A} (< p) P)
  weaken   : ∀{Γ Δ A P} (p : Γ ≃ [] + Δ) → Client (weaken {A} (< p) P)
  contract : ∀{Γ Δ A P} (p : Γ ≃ [] + Δ) → Client (contract {A} (< p) P)

data Server : ∀{Γ} → Process Γ → Set where
  server : ∀{Γ Δ A P} (p : Γ ≃ [] + Δ) (un : Un Δ) → Server (server {A} (< p) un P)

data DelayedServer : ∀{Γ} → Process Γ → Set where
  server : ∀{Γ Δ A C P} (p : Γ ∋ `! A ⊳ Δ) (un : Un Δ) →
           DelayedServer (server (> p) (un-∷ {C} un) P)

Thread : ∀{Γ} → Process Γ → Set
Thread P = Link P ⊎ Delayed P ⊎ Output P ⊎ Input P ⊎ Client P ⊎ Server P ⊎ DelayedServer P

Observable : ∀{Γ} → Process Γ → Set
Observable P = ∃[ Q ] P ⊒ Q × Thread Q

Reducible : ∀{Γ} → Process Γ → Set
Reducible P = ∃[ Q ] P ↝ Q

Alive : ∀{Γ} → Process Γ → Set
Alive P = Observable P ⊎ Reducible P

link-thread : ∀{A Γ} (p : Γ ≃ [ A ] + [ dual A ]) → Thread (link p)
link-thread p = inj₁ (link p)

close-thread : Thread close
close-thread = inj₂ (inj₂ (inj₁ close))

wait-thread : ∀{Γ Δ P} (p : Γ ≃ [ ⊥ ] + Δ) → Thread (wait p P)
wait-thread (< p) = inj₂ (inj₂ (inj₂ (inj₁ (wait p))))
wait-thread (> p) = inj₂ (inj₁ (wait p))

fail-thread : ∀{Γ Δ} (p : Γ ≃ [ ⊤ ] + Δ) → Thread (fail p)
fail-thread (< p) = inj₂ (inj₂ (inj₂ (inj₁ (fail p))))
fail-thread (> p) = inj₂ (inj₁ (fail p))

case-thread : ∀{A B Γ Δ P Q} (p : Γ ≃ [ A & B ] + Δ) → Thread (case p P Q)
case-thread (< p) = inj₂ (inj₂ (inj₂ (inj₁ (case p))))
case-thread (> p) = inj₂ (inj₁ (case p))

join-thread : ∀{A B Γ Δ P} (p : Γ ≃ [ A ⅋ B ] + Δ) → Thread (join p P)
join-thread (< p) = inj₂ (inj₂ (inj₂ (inj₁ (join p))))
join-thread (> p) = inj₂ (inj₁ (join p))

left-thread : ∀{A B Γ Δ P} (p : Γ ∋ A ⊕ B ⊳ Δ) → Thread (left p P)
left-thread (< p) = inj₂ (inj₂ (inj₁ (left p)))
left-thread (> p) = inj₂ (inj₁ (left p))

right-thread : ∀{A B Γ Δ P} (p : Γ ∋ A ⊕ B ⊳ Δ) → Thread (right p P)
right-thread (< p) = inj₂ (inj₂ (inj₁ (right p)))
right-thread (> p) = inj₂ (inj₁ (right p))

fork-thread : ∀{A B Γ Δ Δ₁ Δ₂ P Q} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂) → Thread (fork p q P Q)
fork-thread (< p) q = inj₂ (inj₂ (inj₁ (fork p q)))
fork-thread (> p) (< q) = inj₂ (inj₁ (fork-l p q))
fork-thread (> p) (> q) = inj₂ (inj₁ (fork-r p q))

client-thread : ∀{A Γ Δ P} (p : Γ ≃ [ `? A ] + Δ) → Thread (client p P)
client-thread (< p) = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (client p)))))
client-thread (> p) = inj₂ (inj₁ (client p))

weaken-thread : ∀{A Γ Δ P} (p : Γ ≃ [ `? A ] + Δ) → Thread (weaken {A = A} p P)
weaken-thread (< p) = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (weaken p)))))
weaken-thread (> p) = inj₂ (inj₁ (weaken p))

contract-thread : ∀{A Γ Δ P} (p : Γ ≃ [ `? A ] + Δ) → Thread (contract p P)
contract-thread (< p) = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (contract p)))))
contract-thread (> p) = inj₂ (inj₁ (contract p))

server-thread : ∀{A Γ Δ P} (p : Γ ≃ [ `! A ] + Δ) (un : Un Δ) → Thread (server p un P)
server-thread (< p) un = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (server p un))))))
server-thread (> p) (un-∷ un) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (server p un))))))

ex-thread : ∀{A B Γ Δ P} (p : Γ ∋ `∃ A ⊳ Δ) -> Thread (ex {A} {B} p P)
ex-thread (< p) = inj₂ (inj₂ (inj₁ (ex p)))
ex-thread (> p) = inj₂ (inj₁ (ex p))

all-thread : ∀{A Γ Δ F} (p : Γ ∋ `∀ A ⊳ Δ) -> Thread (all p F)
all-thread (< p) = inj₂ (inj₂ (inj₂ (inj₁ (all p))))
all-thread (> p) = inj₂ (inj₁ (all p))

data CanonicalCut {Γ} : Process Γ → Set where
  cc-link           : ∀{Γ₁ Γ₂ A P Q} (p : Γ ≃ Γ₁ + Γ₂) →
                      Link P → CanonicalCut (cut {A} p P Q)
  cc-delayed        : ∀{Γ₁ Γ₂ A P Q} (p : Γ ≃ Γ₁ + Γ₂) →
                      Delayed P → CanonicalCut (cut {A} p P Q)
  cc-delayed-server : ∀{Γ₁ Γ₂ A P Q} (p : Γ ≃ Γ₁ + Γ₂) →
                      DelayedServer P → Server Q → CanonicalCut (cut {A} p P Q)
  cc-redex          : ∀{Γ₁ Γ₂ A P Q} (p : Γ ≃ Γ₁ + Γ₂) →
                      Output P → Input Q → CanonicalCut (cut {A} p P Q)
  cc-connect        : ∀{Γ₁ Γ₂ A P Q} (p : Γ ≃ Γ₁ + Γ₂) →
                      Server P → Client Q → CanonicalCut (cut {A} p P Q)

output-output : ∀{A Γ Δ P Q} → ¬ (Output {A ∷ Γ} P × Output {dual A ∷ Δ} Q)
output-output (close , ())

output-client : ∀{A Γ Δ P Q} → ¬ (Output {A ∷ Γ} P × Client {dual A ∷ Δ} Q)
output-client (close , ())

output-server : ∀{A Γ Δ P Q} → ¬ (Output {A ∷ Γ} P × Server {dual A ∷ Δ} Q)
output-server (close , ())

output-delayed-server : ∀{A Γ Δ P Q} → ¬ (Output {A ∷ Γ} P × DelayedServer {dual A ∷ Δ} Q)
output-delayed-server (close , ())

input-input : ∀{A Γ Δ P Q} → ¬ (Input {A ∷ Γ} P × Input {dual A ∷ Δ} Q)
input-input (fail _ , ())

input-client : ∀{A Γ Δ P Q} → ¬ (Input {A ∷ Γ} P × Client {dual A ∷ Δ} Q)
input-client (fail _ , ())

input-server : ∀{A Γ Δ P Q} → ¬ (Input {A ∷ Γ} P × Server {dual A ∷ Δ} Q)
input-server (fail _ , ())

input-delayed-server : ∀{A Γ Δ P Q} → ¬ (Input {A ∷ Γ} P × DelayedServer {dual A ∷ Δ} Q)
input-delayed-server (fail _ , ())

client-client : ∀{A Γ Δ P Q} → ¬ (Client {A ∷ Γ} P × Client {dual A ∷ Δ} Q)
client-client (client _ , ())

client-delayed-server : ∀{A Γ Δ P Q} → ¬ (Client {A ∷ Γ} P × DelayedServer {dual A ∷ Δ} Q)
client-delayed-server (client _ , ())

server-server : ∀{A Γ Δ P Q} → ¬ (Server {A ∷ Γ} P × Server {dual A ∷ Δ} Q)
server-server (server _ _ , ())

delayed-server-delayed-served : ∀{A Γ Δ P Q} → ¬ (DelayedServer {A ∷ Γ} P × DelayedServer {dual A ∷ Δ} Q)
delayed-server-delayed-served (server _ _ , ())

canonical-cut : ∀{A Γ Γ₁ Γ₂ P Q} (p : Γ ≃ Γ₁ + Γ₂) →
                Thread P → Thread Q → ∃[ R ] CanonicalCut R × cut {A} p P Q ⊒ R
canonical-cut pc (inj₁ x) Qt = _ , cc-link pc x , s-refl
canonical-cut pc (inj₂ x) (inj₁ y) = _ , cc-link (+-comm pc) y , s-comm pc
canonical-cut pc (inj₂ (inj₁ x)) (inj₂ y) = _ , cc-delayed pc x , s-refl
canonical-cut pc (inj₂ (inj₂ x)) (inj₂ (inj₁ y)) = _ , cc-delayed (+-comm pc) y , s-comm pc
canonical-cut pc (inj₂ (inj₂ (inj₁ x))) (inj₂ (inj₂ (inj₁ y))) = contradiction (x , y) output-output
canonical-cut pc (inj₂ (inj₂ (inj₁ x))) (inj₂ (inj₂ (inj₂ (inj₁ y)))) = _ , cc-redex pc x y , s-refl
canonical-cut pc (inj₂ (inj₂ (inj₁ x))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y))))) = contradiction (x , y) output-client
canonical-cut pc (inj₂ (inj₂ (inj₁ x))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y)))))) = contradiction (x , y) output-server
canonical-cut pc (inj₂ (inj₂ (inj₁ x))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ y)))))) = contradiction (x , y) output-delayed-server
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₁ x)))) (inj₂ (inj₂ (inj₁ y))) = _ , cc-redex (+-comm pc) y x , s-comm pc
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))) (inj₂ (inj₂ (inj₁ y))) = contradiction (y , x) output-client
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))) (inj₂ (inj₂ (inj₁ y))) = contradiction (y , x) output-server
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x)))))) (inj₂ (inj₂ (inj₁ y))) = contradiction (y , x) output-delayed-server
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₁ x)))) (inj₂ (inj₂ (inj₂ (inj₁ y)))) = contradiction (x , y) (input-input)
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₁ x)))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y))))) = contradiction (x , y) input-client
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₁ x)))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y)))))) = contradiction (x , y) input-server
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₁ x)))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ y)))))) = contradiction (x , y) input-delayed-server
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))) (inj₂ (inj₂ (inj₂ (inj₁ y)))) = contradiction (y , x) input-client
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))) (inj₂ (inj₂ (inj₂ (inj₁ y)))) = contradiction (y , x) input-server
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x)))))) (inj₂ (inj₂ (inj₂ (inj₁ y)))) = contradiction (y , x) input-delayed-server
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y))))) = contradiction (x , y) client-client
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y)))))) = _ , cc-connect (+-comm pc) y x , s-comm pc
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ y)))))) = contradiction (x , y) client-delayed-server
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y))))) = _ , cc-connect pc x y , s-refl
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x)))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y))))) = contradiction (y , x) client-delayed-server
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y)))))) = contradiction (x , y) server-server
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ y)))))) = _ , cc-delayed-server (+-comm pc) y x , s-comm pc
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x)))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y)))))) = _ , cc-delayed-server pc x y , s-refl
canonical-cut pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x)))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ y)))))) = contradiction (x , y) delayed-server-delayed-served

⊒Alive : ∀{Γ} {P Q : Process Γ} → P ⊒ Q → Alive Q → Alive P
⊒Alive pcong (inj₁ (_ , x , th)) = inj₁ (_ , s-tran pcong x , th)
⊒Alive pcong (inj₂ (_ , red)) = inj₂ (_ , r-cong pcong red)

canonical-cut-alive : ∀{Γ} {P : Process Γ} → CanonicalCut P → Alive P
canonical-cut-alive (cc-link p (link (< > •))) = inj₂ (_ , r-link p)
canonical-cut-alive (cc-link p (link (> < •))) =
  inj₂ (_ , r-cong (s-cong p (s-link (> < •)) s-refl) (r-link p))
canonical-cut-alive (cc-redex p close (wait q)) with +-empty-l p | +-empty-l q
... | refl | refl = inj₂ (_ , r-close p q)
canonical-cut-alive (cc-redex p (right q) (case r)) with +-empty-l q | +-empty-l r
... | refl | refl = inj₂ (_ , r-right p q r)
canonical-cut-alive (cc-redex p (left q) (case r)) with +-empty-l q | +-empty-l r
... | refl | refl = inj₂ (_ , r-left p q r)
canonical-cut-alive (cc-redex p (fork q r) (join s)) with +-empty-l q | +-empty-l s
... | refl | refl = inj₂ (_ , r-fork p s r q)
canonical-cut-alive (cc-redex p (ex q) (all r)) with +-empty-l q | +-empty-l r
... | refl | refl = inj₂ (_ , r-exists p q r)
canonical-cut-alive (cc-connect p (server q un) (client r)) with +-empty-l q | +-empty-l r
... | refl | refl = inj₂ (_ , r-client p q r un)
canonical-cut-alive (cc-connect p (server q un) (weaken r)) with +-empty-l q | +-empty-l r
... | refl | refl = inj₂ (_ , r-weaken p q r un)
canonical-cut-alive (cc-connect p (server q un) (contract r)) with +-empty-l q | +-empty-l r
... | refl | refl = inj₂ (_ , r-contract p q r un)
canonical-cut-alive (cc-delayed p (wait q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-wait p q , wait-thread q′)
canonical-cut-alive (cc-delayed p (case q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-case p q , case-thread q′)
canonical-cut-alive (cc-delayed p (join q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-join p q , join-thread q′)
canonical-cut-alive (cc-delayed p (right q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-right p q , right-thread q′)
canonical-cut-alive (cc-delayed p (left q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-left p q , left-thread q′)
canonical-cut-alive (cc-delayed p (fork-l q r)) =
  let _ , p′ , q′ = +-assoc-l p q in
  let _ , p′′ , r′ = +-assoc-l p′ r in
  let _ , q′′ , r′′ = +-assoc-r r′ (+-comm p′′) in
  inj₁ (_ , s-fork-l p q r , fork-thread q′ r′′)
canonical-cut-alive (cc-delayed p (fork-r q r)) =
  let _ , p′ , q′ = +-assoc-l p q in
  let _ , p′′ , r′ = +-assoc-l p′ r in
  inj₁ (_ , s-fork-r p q r , fork-thread q′ r′)
canonical-cut-alive (cc-delayed p (fail q)) =
  let _ , p′ , q′ = +-assoc-l p q in
  inj₁ (_ , s-fail p q , fail-thread q′)
canonical-cut-alive (cc-delayed p (client q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-client p q , client-thread q′)
canonical-cut-alive (cc-delayed p (weaken q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-weaken p q , weaken-thread q′)
canonical-cut-alive (cc-delayed p (contract q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-contract p q , contract-thread q′)
canonical-cut-alive (cc-delayed p (ex q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , s-ex p q , ex-thread q')
canonical-cut-alive (cc-delayed p (all q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , s-all p q , all-thread q')
canonical-cut-alive (cc-delayed-server p (server q un) (server r un′)) with +-empty-l r
... | refl =
  let _ , p′ , q′ = +-assoc-l p q in
  inj₁ (_ , s-server p q r un un′ , server-thread q′ (+-un p′ un un′))

deadlock-freedom : ∀{Γ} (P : Process Γ) → Alive P
deadlock-freedom (link p) = inj₁ (_ , s-refl , link-thread p)
deadlock-freedom (fail p) = inj₁ (_ , s-refl , fail-thread p)
deadlock-freedom close = inj₁ (_ , s-refl , close-thread)
deadlock-freedom (wait p P) = inj₁ (_ , s-refl , wait-thread p)
deadlock-freedom (left p P) = inj₁ (_ , s-refl , left-thread p)
deadlock-freedom (right p P) = inj₁ (_ , s-refl , right-thread p)
deadlock-freedom (case p P Q) = inj₁ (_ , s-refl , case-thread p)
deadlock-freedom (fork p q P Q) = inj₁ (_ , s-refl , fork-thread p q)
deadlock-freedom (join p P) = inj₁ (_ , s-refl , join-thread p)
deadlock-freedom (server p un P) = inj₁ (_ , s-refl , server-thread p un)
deadlock-freedom (client p P) = inj₁ (_ , s-refl , client-thread p)
deadlock-freedom (weaken p P) = inj₁ (_ , s-refl , weaken-thread p)
deadlock-freedom (contract p P) = inj₁ (_ , s-refl , contract-thread p)
deadlock-freedom (ex p P) = inj₁ (_ , s-refl , ex-thread p)
deadlock-freedom (all p F) = inj₁ (_ , s-refl , all-thread p)
deadlock-freedom (cut p P Q) with deadlock-freedom P
... | inj₂ (_ , red) = inj₂ (_ , r-cut p red)
... | inj₁ (_ , Pc , Pt) with deadlock-freedom Q
... | inj₂ (_ , red) = inj₂ (_ , r-cong (s-comm p) (r-cut (+-comm p) red))
... | inj₁ (_ , Qc , Qt) with canonical-cut p Pt Qt
... | _ , cc , pcong = ⊒Alive (s-tran (s-cong p Pc Qc) pcong) (canonical-cut-alive cc)
