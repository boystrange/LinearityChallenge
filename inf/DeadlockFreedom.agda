{-# OPTIONS --rewriting --guardedness #-}
open import Data.Sum
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Bool using (Bool; true; false; if_then_else_)
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
  cut : ∀{Γ Γ₁ Γ₂ A} (p : Γ ≃ Γ₁ + Γ₂) {P : Process (A ∷ Γ₁)} {Q : Process (dual A .force ∷ Γ₂)} →
        Cut (cut p P Q)

data Link : ∀{Γ} → Process Γ → Set where
  link : ∀{Γ A} (p : Γ ≃ [ A ] + [ dual A .force ]) → Link (link p)

data Input : ∀{Γ} → Process Γ → Set where
  fail : ∀{Γ Δ} (p : Γ ≃ [] + Δ) → Input (fail (split-l p))
  wait : ∀{Γ Δ} (p : Γ ≃ [] + Δ) {P : Process Δ} → Input (wait (split-l p) P)
  case : ∀{A B Γ Δ} (p : Γ ≃ [] + Δ) {P : Process (A .force ∷ Δ)} {Q : Process (B .force ∷ Δ)} →
         Input (case {A} {B} (split-l p) P Q)
  join : ∀{A B Γ Δ} (p : Γ ≃ [] + Δ) {P : Process (B .force ∷ A .force ∷ Δ)} →
         Input (join {A} {B} (split-l p) P)
  all  : ∀{A Γ Δ} (p : Γ ≃ [] + Δ)
         {F : (B : Type) -> Process (subst (make-subst B) (A .force) .force ∷ Δ)} ->
         Input (all {A} (split-l p) F)

data Output : ∀{Γ} → Process Γ → Set where
  close  : Output close
  select : ∀{Γ Δ A B} (x : Bool) (p : Γ ≃ [] + Δ) {P : Process ((if x then A else B) .force ∷ Δ)} →
           Output (select {A} {B} x (split-l p) P)
  fork   : ∀{Γ Δ Δ₁ Δ₂ A B} (p : Γ ≃ [] + Δ) (q : Δ ≃ Δ₁ + Δ₂)
           {P : Process (A .force ∷ Δ₁)} {Q : Process (B .force ∷ Δ₂)} →
           Output (fork {A} {B} (split-l p) q P Q)
  ex     : ∀{A B Γ Δ} (p : Γ ≃ [] + Δ)
           {P : Process (subst (make-subst B) (A .force) .force ∷ Δ)} ->
           Output (ex {A} (split-l p) P)

data Delayed : ∀{Γ} → Process Γ → Set where
  fail     : ∀{A Γ Δ} (p : Γ ≃ ⊤ , Δ) → Delayed (fail (split-r {A} p))
  wait     : ∀{C Γ Δ} (p : Γ ≃ ⊥ , Δ) {P : Process (C ∷ Δ)} →
             Delayed (wait (split-r p) P)
  case     : ∀{Γ Δ C A B} (p : Γ ≃ A & B , Δ) {P : Process (A .force ∷ C ∷ Δ)} {Q : Process (B .force ∷ C ∷ Δ)} →
             Delayed (case (split-r p) P Q)
  join     : ∀{Γ Δ C A B} (p : Γ ≃ A ⅋ B , Δ) {P : Process (B .force ∷ A .force ∷ C ∷ Δ)} →
             Delayed (join (split-r p) P)
  select   : ∀{Γ Δ C A B} (x : Bool) (p : Γ ≃ A ⊕ B , Δ) {P : Process ((if x then A else B) .force ∷ C ∷ Δ)} →
             Delayed (select x (split-r p) P)
  fork-l   : ∀{Γ Δ Δ₁ Δ₂ C A B} (p : Γ ≃ A ⊗ B , Δ) (q : Δ ≃ Δ₁ + Δ₂)
             {P : Process (A .force ∷ C ∷ Δ₁)} {Q : Process (B .force ∷ Δ₂)} →
             Delayed (fork (split-r p) (split-l q) P Q)
  fork-r   : ∀{Γ Δ Δ₁ Δ₂ C A B} (p : Γ ≃ A ⊗ B , Δ) (q : Δ ≃ Δ₁ + Δ₂)
             {P : Process (A .force ∷ Δ₁)} {Q : Process (B .force ∷ C ∷ Δ₂)} →
             Delayed (fork (split-r p) (split-r q) P Q)
  all      : ∀{A C Γ Δ} (p : Γ ≃ `∀ A , Δ)
             {F : (B : Type) -> Process (subst (make-subst B) (A .force) .force ∷ C ∷ Δ)} ->
             Delayed (all (split-r p) F)
  ex       : ∀{A B C Γ Δ} (p : Γ ≃ `∃ A , Δ)
             {P : Process (subst (make-subst B) (A .force) .force ∷ C ∷ Δ)} ->
             Delayed (ex (split-r p) P)
  client   : ∀{Γ Δ A C} (p : Γ ≃ `? A , Δ) {P : Process (A .force ∷ C ∷ Δ)} →
             Delayed (client (split-r p) P)
  weaken   : ∀{Γ Δ A C} (p : Γ ≃ `? A , Δ) {P : Process (C ∷ Δ)} →
             Delayed (weaken (split-r p) P)
  contract : ∀{Γ Δ A C} (p : Γ ≃ `? A , Δ) {P : Process (`? A ∷ `? A ∷ C ∷ Δ)} →
             Delayed (contract (split-r p) P)

data Client : ∀{Γ} → Process Γ → Set where
  client   : ∀{Γ Δ A} (p : Γ ≃ [] + Δ) {P : Process (A .force ∷ Δ)} →
             Client (client {A} (split-l p) P)
  weaken   : ∀{Γ Δ A} (p : Γ ≃ [] + Δ) {P : Process Δ} →
             Client (weaken {A} (split-l p) P)
  contract : ∀{Γ Δ A} (p : Γ ≃ [] + Δ) {P : Process (`? A ∷ `? A ∷ Δ)} →
             Client (contract (split-l p) P)

data Server : ∀{Γ} → Process Γ → Set where
  server : ∀{Γ Δ A} (p : Γ ≃ [] + Δ) (un : Un Δ) {P : Process (A .force ∷ Δ)} →
           Server (server {A} (split-l p) un P)

data DelayedServer : ∀{Γ} → Process Γ → Set where
  server : ∀{Γ Δ A C} (p : Γ ≃ `! A , Δ) (un : Un Δ) {P : Process (A .force ∷ `? C ∷ Δ)} →
           DelayedServer (server (split-r p) (un-∷ un) P)

Thread : ∀{Γ} → Process Γ → Set
Thread P = Link P ⊎ Delayed P ⊎ Output P ⊎ Input P ⊎ Client P ⊎ Server P ⊎ DelayedServer P

Observable : ∀{Γ} → Process Γ → Set
Observable P = ∃[ Q ] P ⊒ Q × Thread Q

Reducible : ∀{Γ} → Process Γ → Set
Reducible P = ∃[ Q ] P ↝ Q

Alive : ∀{Γ} → Process Γ → Set
Alive P = Observable P ⊎ Reducible P

link-thread : ∀{A Γ} (p : Γ ≃ [ A ] + [ dual A .force ]) → Thread (link p)
link-thread p = inj₁ (link p)

close-thread : Thread close
close-thread = inj₂ (inj₂ (inj₁ close))

wait-thread : ∀{Γ Δ} (p : Γ ≃ [ ⊥ ] + Δ) {P : Process Δ} → Thread (wait p P)
wait-thread (split-l p) = inj₂ (inj₂ (inj₂ (inj₁ (wait p))))
wait-thread (split-r p) = inj₂ (inj₁ (wait p))

fail-thread : ∀{Γ Δ} (p : Γ ≃ [ ⊤ ] + Δ) → Thread (fail p)
fail-thread (split-l p) = inj₂ (inj₂ (inj₂ (inj₁ (fail p))))
fail-thread (split-r p) = inj₂ (inj₁ (fail p))

case-thread :
  ∀{A B Γ Δ} (p : Γ ≃ [ A & B ] + Δ) {P : Process (A .force ∷ Δ)} {Q : Process (B .force ∷ Δ)} →
  Thread (case p P Q)
case-thread (split-l p) = inj₂ (inj₂ (inj₂ (inj₁ (case p))))
case-thread (split-r p) = inj₂ (inj₁ (case p))

join-thread :
  ∀{A B Γ Δ} (p : Γ ≃ [ A ⅋ B ] + Δ) {P : Process (B .force ∷ A .force ∷ Δ)} →
  Thread (join p P)
join-thread (split-l p) = inj₂ (inj₂ (inj₂ (inj₁ (join p))))
join-thread (split-r p) = inj₂ (inj₁ (join p))

select-thread :
  ∀{A B Γ Δ} (x : Bool) (p : Γ ≃ A ⊕ B , Δ) {P : Process ((if x then A else B) .force ∷ Δ)} →
  Thread (select x p P)
select-thread x (split-l p) = inj₂ (inj₂ (inj₁ (select x p)))
select-thread x (split-r p) = inj₂ (inj₁ (select x p))

fork-thread :
  ∀{A B Γ Δ Δ₁ Δ₂} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂)
  {P : Process (A .force ∷ Δ₁)} {Q : Process (B .force ∷ Δ₂)} →
  Thread (fork p q P Q)
fork-thread (split-l p) q = inj₂ (inj₂ (inj₁ (fork p q)))
fork-thread (split-r p) (split-l q) = inj₂ (inj₁ (fork-l p q))
fork-thread (split-r p) (split-r q) = inj₂ (inj₁ (fork-r p q))

all-thread :
  ∀{A Γ Δ} (p : Γ ≃ `∀ A , Δ)
  {F : (B : Type) -> Process (subst (make-subst B) (A .force) .force ∷ Δ)} ->
  Thread (all p F)
all-thread (split-l p) = inj₂ (inj₂ (inj₂ (inj₁ (all p))))
all-thread (split-r p) = inj₂ (inj₁ (all p))

ex-thread :
  ∀{A B Γ Δ} (p : Γ ≃ `∃ A , Δ)
  {P : Process (subst (make-subst B) (A .force) .force ∷ Δ)} ->
  Thread (ex p P)
ex-thread (split-l p) = inj₂ (inj₂ (inj₁ (ex p)))
ex-thread (split-r p) = inj₂ (inj₁ (ex p))

client-thread :
  ∀{A Γ Δ} (p : Γ ≃ [ `? A ] + Δ)
  {P : Process (A .force ∷ Δ)} →
  Thread (client p P)
client-thread (split-l p) = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (client p)))))
client-thread (split-r p) = inj₂ (inj₁ (client p))

weaken-thread :
  ∀{A Γ Δ} (p : Γ ≃ [ `? A ] + Δ)
  {P : Process Δ} →
  Thread (weaken {A} p P)
weaken-thread (split-l p) = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (weaken p)))))
weaken-thread (split-r p) = inj₂ (inj₁ (weaken p))

contract-thread :
  ∀{A Γ Δ} (p : Γ ≃ [ `? A ] + Δ)
  {P : Process (`? A ∷ `? A ∷ Δ)} →
  Thread (contract p P)
contract-thread (split-l p) = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (contract p)))))
contract-thread (split-r p) = inj₂ (inj₁ (contract p))

server-thread :
  ∀{A Γ Δ} (p : Γ ≃ [ `! A ] + Δ) (un : Un Δ) {P : Process (A .force ∷ Δ)} →
  Thread (server p un P)
server-thread (split-l p) un = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (server p un))))))
server-thread (split-r p) (un-∷ un) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (server p un))))))

data CanonicalCut {Γ} : Process Γ → Set where
  cc-link           : ∀{Γ₁ Γ₂ A} (p : Γ ≃ Γ₁ + Γ₂)
                      {P : Process (A ∷ Γ₁)} {Q : Process (dual A .force ∷ Γ₂)} →
                      Link P → CanonicalCut (cut p P Q)
  cc-delayed        : ∀{Γ₁ Γ₂ A} (p : Γ ≃ Γ₁ + Γ₂)
                      {P : Process (A ∷ Γ₁)} {Q : Process (dual A .force ∷ Γ₂)} →
                      Delayed P → CanonicalCut (cut p P Q)
  cc-delayed-server : ∀{Γ₁ Γ₂ A} (p : Γ ≃ Γ₁ + Γ₂)
                      {P : Process (A ∷ Γ₁)} {Q : Process (dual A .force ∷ Γ₂)} →
                      DelayedServer P → Server Q → CanonicalCut (cut p P Q)
  cc-redex          : ∀{Γ₁ Γ₂ A} (p : Γ ≃ Γ₁ + Γ₂)
                      {P : Process (A ∷ Γ₁)} {Q : Process (dual A .force ∷ Γ₂)} →
                      Output P → Input Q → CanonicalCut (cut p P Q)
  cc-connect        : ∀{Γ₁ Γ₂ A} (p : Γ ≃ Γ₁ + Γ₂)
                      {P : Process (A ∷ Γ₁)} {Q : Process (dual A .force ∷ Γ₂)} →
                      Server P → Client Q → CanonicalCut (cut p P Q)

output-output :
  ∀{A Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (dual A .force ∷ Δ)} → ¬ (Output P × Output Q)
output-output (close , ())

output-client :
  ∀{A Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (dual A .force ∷ Δ)} → ¬ (Output P × Client Q)
output-client (close , ())

output-server :
  ∀{A Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (dual A .force ∷ Δ)} → ¬ (Output P × Server Q)
output-server (close , ())

output-delayed-server :
  ∀{A Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (dual A .force ∷ Δ)} → ¬ (Output P × DelayedServer Q)
output-delayed-server (close , ())

input-input :
  ∀{A Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (dual A .force ∷ Δ)} → ¬ (Input P × Input Q)
input-input (fail p , ())

input-client :
  ∀{A Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (dual A .force ∷ Δ)} → ¬ (Input P × Client Q)
input-client (fail p₁ , ())

input-server :
  ∀{A Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (dual A .force ∷ Δ)} → ¬ (Input P × Server Q)
input-server (fail p₁ , ())

input-delayed-server :
  ∀{A Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (dual A .force ∷ Δ)} → ¬ (Input P × DelayedServer Q)
input-delayed-server (fail p₁ , ())

client-client :
  ∀{A Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (dual A .force ∷ Δ)} → ¬ (Client P × Client Q)
client-client (client p , ())

client-delayed-server :
  ∀{A Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (dual A .force ∷ Δ)} → ¬ (Client P × DelayedServer Q)
client-delayed-server (client p₁ , ())

server-server :
  ∀{A Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (dual A .force ∷ Δ)} → ¬ (Server P × Server Q)
server-server (server p un , ())

delayed-server-delayed-served :
  ∀{A Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (dual A .force ∷ Δ)} → ¬ (DelayedServer P × DelayedServer Q)
delayed-server-delayed-served (server p un , ())

canonical-cut :
  ∀{A Γ Γ₁ Γ₂} {P : Process (A ∷ Γ₁)} {Q : Process (dual A .force ∷ Γ₂)} (p : Γ ≃ Γ₁ + Γ₂) →
  Thread P → Thread Q → ∃[ R ] CanonicalCut R × cut p P Q ⊒ R
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
canonical-cut-alive (cc-link p (link (split-l (split-r split-e)))) = inj₂ (_ , r-link p)
canonical-cut-alive (cc-link p (link (split-r (split-l split-e)))) =
  inj₂ (_ , r-cong (s-cong p (s-link (split-r (split-l split-e))) s-refl) (r-link p))
canonical-cut-alive (cc-redex p close (wait q)) with +-empty-l p | +-empty-l q
... | refl | refl = inj₂ (_ , r-close p q)
canonical-cut-alive (cc-redex p (select false q) (case r)) with +-empty-l q | +-empty-l r
... | refl | refl = inj₂ (_ , r-select-r p q r)
canonical-cut-alive (cc-redex p (select true q) (case r)) with +-empty-l q | +-empty-l r
... | refl | refl = inj₂ (_ , r-select-l p q r)
canonical-cut-alive (cc-redex p (fork q r) (join s)) with +-empty-l q | +-empty-l s
... | refl | refl = inj₂ (_ , r-fork p s r q)
canonical-cut-alive (cc-redex p (ex q) (all r)) with +-empty-l q | +-empty-l r
... | refl | refl = inj₂ (_ , r-poly p q r)
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
canonical-cut-alive (cc-delayed p (select false q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-select-r p q , select-thread false q′)
canonical-cut-alive (cc-delayed p (select true q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-select-l p q , select-thread true q′)
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
canonical-cut-alive (cc-delayed p (all q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , s-all p q , all-thread q')
canonical-cut-alive (cc-delayed p (ex q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , s-ex p q , ex-thread q')
canonical-cut-alive (cc-delayed p (client q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-client p q , client-thread q′)
canonical-cut-alive (cc-delayed p (weaken q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-weaken p q , weaken-thread q′)
canonical-cut-alive (cc-delayed p (contract q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-contract p q , contract-thread q′)
canonical-cut-alive (cc-delayed-server p (server q un) (server r un′)) with +-empty-l r
... | refl =
  let _ , p′ , q′ = +-assoc-l p q in
  inj₁ (_ , s-server p q r un un′ , server-thread q′ (#un+ p′ un un′))

deadlock-freedom : ∀{Γ} (P : Process Γ) → Alive P
deadlock-freedom (link p) = inj₁ (_ , s-refl , link-thread p)
deadlock-freedom (fail p) = inj₁ (_ , s-refl , fail-thread p)
deadlock-freedom close = inj₁ (_ , s-refl , close-thread)
deadlock-freedom (wait p P) = inj₁ (_ , s-refl , wait-thread p)
deadlock-freedom (select x p P) = inj₁ (_ , s-refl , select-thread x p)
deadlock-freedom (case p P Q) = inj₁ (_ , s-refl , case-thread p)
deadlock-freedom (fork p q P Q) = inj₁ (_ , s-refl , fork-thread p q)
deadlock-freedom (join p P) = inj₁ (_ , s-refl , join-thread p)
deadlock-freedom (all p F) = inj₁ (_ , s-refl , all-thread p)
deadlock-freedom (ex p P) = inj₁ (_ , s-refl , ex-thread p)
deadlock-freedom (server p un P) = inj₁ (_ , s-refl , server-thread p un)
deadlock-freedom (client p P) = inj₁ (_ , s-refl , client-thread p)
deadlock-freedom (weaken p P) = inj₁ (_ , s-refl , weaken-thread p)
deadlock-freedom (contract p P) = inj₁ (_ , s-refl , contract-thread p)
deadlock-freedom (cut p P Q) with deadlock-freedom P
... | inj₂ (_ , red) = inj₂ (_ , r-cut p red)
... | inj₁ (_ , Pc , Pt) with deadlock-freedom Q
... | inj₂ (_ , red) = inj₂ (_ , r-cong (s-comm p) (r-cut (+-comm p) red))
... | inj₁ (_ , Qc , Qt) with canonical-cut p Pt Qt
... | _ , cc , pcong = ⊒Alive (s-tran (s-cong p Pc Qc) pcong) (canonical-cut-alive cc)
