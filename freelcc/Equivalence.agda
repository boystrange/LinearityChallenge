{-# OPTIONS --rewriting --guardedness #-}
open import Function using (id; _∘_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.List.Base using (List; []; _∷_; [_]; _++_; map)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Agda.Builtin.Equality.Rewrite

open import Type
open import Skip
open import Transitions

-- SIMULATION

record Sim (A B : GroundType) : Set where
  coinductive
  field
    sim-skip : Skip A → Skip B
    sim-next : ∀{ℓ A'} → A ⊨ ℓ ⇒ A' → ∃[ B' ] (B ⊨ ℓ ⇒ B' × Sim A' B')

open Sim

sim-refl : ∀{A} → Sim A A
sim-refl .sim-skip sk = sk
sim-refl .sim-next tr = _ , tr , sim-refl

sim-trans : ∀{A B C} → Sim A B → Sim B C → Sim A C
sim-trans p q .sim-skip sk = q .sim-skip (p .sim-skip sk)
sim-trans p q .sim-next tr with p .sim-next tr
... | _ , tr' , p' with q .sim-next tr'
... | _ , tr'' , q' = _ , tr'' , sim-trans p' q'

sim-dual : ∀{A B} → Sim A B → Sim (dual A) (dual B)
sim-dual le .sim-skip sk = skip-dual (le .sim-skip (skip-dual sk))
sim-dual le .sim-next tr with le .sim-next (transition-dual tr)
... | _ , tr' , le' = _ , transition-dual tr' , sim-dual le'

sim-after : ∀{ℓ A B A' B'} → Sim A B → A ⊨ ℓ ⇒ A' → B ⊨ ℓ ⇒ B' → Sim A' B'
sim-after le p q .sim-skip sk with le .sim-next p
... | _ , q' , le' rewrite deterministic q q' = le' .sim-skip sk
sim-after le p q .sim-next tr with le .sim-next p
... | _ , q' , le' rewrite deterministic q q' = le' .sim-next tr

-- HALF EQUIVALENCE

_≲_ : ∀{n} → Type n → Type n → Set
_≲_ {n} A B = ∀{σ : ∀{u} → Fin n → PreType 0 u} → Sim (subst σ A) (subst σ B)

≲refl : ∀{n} {A : Type n} → A ≲ A
≲refl = sim-refl

≲trans : ∀{n} {A B C : Type n} → A ≲ B → B ≲ C → A ≲ C
≲trans p q = sim-trans p q

≲dual : ∀{n} {A B : Type n} → A ≲ B → dual A ≲ dual B
≲dual {n} {A} {B} le {σ}
  rewrite sym (dual-subst σ A) | sym (dual-subst σ B) = sim-dual le

≲subst : ∀{m n} {A B : Type m} (σ : ∀{u} → Fin m → PreType n u) →
         A ≲ B → subst σ A ≲ subst σ B
≲subst {A = A} {B} σ le {τ} rewrite subst-compose σ τ A | subst-compose σ τ B = le

≲after⊕L : ∀{n} {A A' B B' : Type n} → (A ⊕ B) ≲ (A' ⊕ B') → A ≲ A'
≲after⊕L le .sim-skip sk with le .sim-next ⊕L
... | _ , ⊕L , le' = le' .sim-skip sk
≲after⊕L le .sim-next tr with le .sim-next ⊕L
... | _ , ⊕L , le' = le' .sim-next tr

≲after⊕R : ∀{n} {A A' B B' : Type n} → (A ⊕ B) ≲ (A' ⊕ B') → B ≲ B'
≲after⊕R le .sim-skip sk with le .sim-next ⊕R
... | _ , ⊕R , le' = le' .sim-skip sk
≲after⊕R le .sim-next tr with le .sim-next ⊕R
... | _ , ⊕R , le' = le' .sim-next tr

≲after⊗L : ∀{n} {A A' B B' : Type n} → (A ⊗ B) ≲ (A' ⊗ B') → A ≲ A'
≲after⊗L le .sim-skip sk with le .sim-next ⊗L
... | _ , ⊗L , le' = le' .sim-skip sk
≲after⊗L le .sim-next tr with le .sim-next ⊗L
... | _ , ⊗L , le' = le' .sim-next tr

≲after⊗R : ∀{n} {A A' B B' : Type n} → (A ⊗ B) ≲ (A' ⊗ B') → B ≲ B'
≲after⊗R le .sim-skip sk with le .sim-next ⊗R
... | _ , ⊗R , le' = le' .sim-skip sk
≲after⊗R le .sim-next tr with le .sim-next ⊗R
... | _ , ⊗R , le' = le' .sim-next tr

-- EQUIVALENCE

record _≈_ {n} (A B : Type n) : Set where
  field
    to   : A ≲ B
    from : B ≲ A

open _≈_ public

≈refl : ∀{n} {A : Type n} → A ≈ A
≈refl .to = sim-refl
≈refl .from = sim-refl

≈sym : ∀{n} {A B : Type n} → A ≈ B → B ≈ A
≈sym p .to = p .from
≈sym p .from = p .to

≈trans : ∀{n} {A B C : Type n} → A ≈ B → B ≈ C → A ≈ C
≈trans p q .to = sim-trans (p .to) (q .to)
≈trans p q .from = sim-trans (q .from) (p .from)

≈dual : ∀{n} {A B : Type n} → A ≈ B → dual A ≈ dual B
≈dual {A = A} {B} eq .to   = ≲dual {A = A} {B} (eq .to)
≈dual {A = A} {B} eq .from = ≲dual {A = B} {A} (eq .from)

≈subst : ∀{m n} {A B : Type m} (σ : ∀{u} → Fin m → PreType n u) → A ≈ B →
         subst σ A ≈ subst σ B
≈subst {A = A} {B} σ eq .to = ≲subst {A = A} {B} σ (eq .to)
≈subst {A = A} {B} σ eq .from = ≲subst {A = B} {A} σ (eq .from)

≈after⊕L : ∀{n} {A A' B B' : Type n} → (A ⊕ B) ≈ (A' ⊕ B') → A ≈ A'
≈after⊕L {_} {A} {A'} {B} {B'} eq .to   = ≲after⊕L {_} {A} {A'} {B} {B'} (eq .to)
≈after⊕L {_} {A} {A'} {B} {B'} eq .from = ≲after⊕L {_} {A'} {A} {B'} {B} (eq .from)

≈after⊕R : ∀{n} {A A' B B' : Type n} → (A ⊕ B) ≈ (A' ⊕ B') → B ≈ B'
≈after⊕R {_} {A} {A'} {B} {B'} eq .to   = ≲after⊕R {_} {A} {A'} {B} {B'} (eq .to)
≈after⊕R {_} {A} {A'} {B} {B'} eq .from = ≲after⊕R {_} {A'} {A} {B'} {B} (eq .from)

≈after⊗L : ∀{n} {A A' B B' : Type n} → (A ⊗ B) ≈ (A' ⊗ B') → A ≈ A'
≈after⊗L {_} {A} {A'} {B} {B'} eq .to   = ≲after⊗L {_} {A} {A'} {B} {B'} (eq .to)
≈after⊗L {_} {A} {A'} {B} {B'} eq .from = ≲after⊗L {_} {A'} {A} {B'} {B} (eq .from)

≈after⊗R : ∀{n} {A A' B B' : Type n} → (A ⊗ B) ≈ (A' ⊗ B') → B ≈ B'
≈after⊗R {_} {A} {A'} {B} {B'} eq .to   = ≲after⊗R {_} {A} {A'} {B} {B'} (eq .to)
≈after⊗R {_} {A} {A'} {B} {B'} eq .from = ≲after⊗R {_} {A'} {A} {B'} {B} (eq .from)
