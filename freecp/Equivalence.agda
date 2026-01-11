{-# OPTIONS --rewriting --guardedness #-}
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.List.Base using (List; []; _∷_; [_])
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Type
open import Transitions

-- SIMULATION

record Sim {n} (A B : Type n) : Set where
  coinductive
  field
    next : ∀{ℓ A'} → A ⊨ ℓ ⇒ A' → ∃[ B' ] (B ⊨ ℓ ⇒ B' × Sim A' B')

sim-refl : ∀{n} {A : Type n} → Sim A A
sim-refl .Sim.next tr = _ , tr , sim-refl

sim-trans : ∀{n} {A B C : Type n} → Sim A B → Sim B C → Sim A C
sim-trans p q .Sim.next tr with p .Sim.next tr
... | _ , tr' , p' with q .Sim.next tr'
... | _ , tr'' , q' = _ , tr'' , sim-trans p' q'

sim-dual : ∀{n} {A B : Type n} → Sim A B → Sim (dual A) (dual B)
sim-dual le .Sim.next tr with le .Sim.next (transition-dual tr)
... | _ , tr' , le' = _ , transition-dual tr' , sim-dual le'

sim-after : ∀{n ℓ} {A B A' B' : Type n} → Sim A B → A ⊨ ℓ ⇒ A' → B ⊨ ℓ ⇒ B' → Sim A' B'
sim-after le p q .Sim.next tr with le .Sim.next p
... | _ , q' , le' rewrite deterministic q q' = le' .Sim.next tr

sim⊥𝟙 : ∀{n} → ¬ Sim {n} ⊥ 𝟙
sim⊥𝟙 sim with sim .Sim.next ⊥
... | _ , () , _

sim⊥⊕ : ∀{n A B} → ¬ Sim {n} ⊥ (A ⊕ B)
sim⊥⊕ sim with sim .Sim.next ⊥
... | _ , () , _

sim𝟙⊕ : ∀{n A B} → ¬ Sim {n} 𝟙 (A ⊕ B)
sim𝟙⊕ sim with sim .Sim.next 𝟙
... | _ , () , _

sim𝟙⊗ : ∀{n A B} → ¬ Sim {n} 𝟙 (A ⊗ B)
sim𝟙⊗ sim with sim .Sim.next 𝟙
... | _ , () , _

sim⊥⊗ : ∀{n A B} → ¬ Sim {n} ⊥ (A ⊗ B)
sim⊥⊗ sim with sim .Sim.next ⊥
... | _ , () , _

sim⊥put : ∀{n μ A} → ¬ Sim {n} ⊥ (μ ⊲ A)
sim⊥put sim with sim .Sim.next ⊥
... | _ , () , _

sim𝟙put : ∀{n μ A} → ¬ Sim {n} 𝟙 (μ ⊲ A)
sim𝟙put sim with sim .Sim.next 𝟙
... | _ , () , _

sim⊤𝟘 : ∀{n} → ¬ Sim {n} ⊤ 𝟘
sim⊤𝟘 sim with sim .Sim.next ⊤
... | _ , () , _

sim⊤𝟙 : ∀{n} → ¬ Sim {n} ⊤ 𝟙
sim⊤𝟙 sim with sim .Sim.next ⊤
... | _ , () , _

sim⊤put : ∀{n μ A} → ¬ Sim {n} ⊤ (μ ⊲ A)
sim⊤put sim with sim .Sim.next ⊤
... | _ , () , _

sim⊤get : ∀{n μ A} → ¬ Sim {n} ⊤ (μ ⊳ A)
sim⊤get sim with sim .Sim.next ⊤
... | _ , () , _

sim𝟘𝟙 : ∀{n} → ¬ Sim {n} 𝟘 𝟙
sim𝟘𝟙 sim with sim .Sim.next 𝟘
... | _ , () , _

sim⊤⊕ : ∀{n A B} → ¬ Sim {n} ⊤ (A ⊕ B)
sim⊤⊕ sim with sim .Sim.next ⊤
... | _ , () , _

sim⊤& : ∀{n A B} → ¬ Sim {n} ⊤ (A & B)
sim⊤& sim with sim .Sim.next ⊤
... | _ , () , _

sim⊤⊗ : ∀{n A B} → ¬ Sim {n} ⊤ (A ⊗ B)
sim⊤⊗ sim with sim .Sim.next ⊤
... | _ , () , _

sim⊤⅋ : ∀{n A B} → ¬ Sim {n} ⊤ (A ⅋ B)
sim⊤⅋ sim with sim .Sim.next ⊤
... | _ , () , _

sim&⊕ : ∀{n A B C D} → ¬ Sim {n} (A & B) (C ⊕ D)
sim&⊕ sim with sim .Sim.next &L
... | _ , () , _

sim&⊗ : ∀{n A B C D} → ¬ Sim {n} (A & B) (C ⊗ D)
sim&⊗ sim with sim .Sim.next &L
... | _ , () , _

sim&put : ∀{n A B μ C} → ¬ Sim {n} (A & B) (μ ⊲ C)
sim&put sim with sim .Sim.next &L
... | _ , () , _

sim⊕put : ∀{n A B μ C} → ¬ Sim {n} (A ⊕ B) (μ ⊲ C)
sim⊕put sim with sim .Sim.next ⊕L
... | _ , () , _

sim⅋put : ∀{n A B μ C} → ¬ Sim {n} (A ⅋ B) (μ ⊲ C)
sim⅋put sim with sim .Sim.next ⅋L
... | _ , () , _

sim⊗put : ∀{n A B μ C} → ¬ Sim {n} (A ⊗ B) (μ ⊲ C)
sim⊗put sim with sim .Sim.next ⊗L
... | _ , () , _

simgetput : ∀{n A B μ ν} → ¬ Sim {n} (μ ⊳ A) (ν ⊲ B)
simgetput sim with sim .Sim.next get
... | _ , () , _

sim⊕⊗ : ∀{n A B C D} → ¬ Sim {n} (A ⊕ B) (C ⊗ D)
sim⊕⊗ sim with sim .Sim.next ⊕L
... | _ , () , _

sim⅋⊗ : ∀{n A B C D} → ¬ Sim {n} (A ⅋ B) (C ⊗ D)
sim⅋⊗ sim with sim .Sim.next ⅋L
... | _ , () , _

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
≲after⊕L le .Sim.next tr with le .Sim.next ⊕L
... | _ , ⊕L , le' = le' .Sim.next tr

≲after⊕R : ∀{n} {A A' B B' : Type n} → (A ⊕ B) ≲ (A' ⊕ B') → B ≲ B'
≲after⊕R le .Sim.next tr with le .Sim.next ⊕R
... | _ , ⊕R , le' = le' .Sim.next tr

≲after⊗L : ∀{n} {A A' B B' : Type n} → (A ⊗ B) ≲ (A' ⊗ B') → A ≲ A'
≲after⊗L le .Sim.next tr with le .Sim.next ⊗L
... | _ , ⊗L , le' = le' .Sim.next tr

≲after⊗R : ∀{n} {A A' B B' : Type n} → (A ⊗ B) ≲ (A' ⊗ B') → B ≲ B'
≲after⊗R le .Sim.next tr with le .Sim.next ⊗R
... | _ , ⊗R , le' = le' .Sim.next tr

≲after-put : ∀{n μ} {A A' : Type n} → (μ ⊲ A) ≲ (μ ⊲ A') → A ≲ A'
≲after-put le .Sim.next tr with le .Sim.next put
... | _ , put , le' = le' .Sim.next tr

-- ≲after : ∀{n ℓ} {A B A' B' : Type n} →
--          ((σ : ∀{m u} → Fin n → PreType m u) → A ⊨ ℓ ⇒ A') → B ⊨ ℓ ⇒ B' → A ≲ B → A' ≲ B'
-- ≲after x y le {σ} with le {σ}
-- ... | sim = {!!}

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

≈after-put : ∀{n μ} {A A' : Type n}  → (μ ⊲ A) ≈ (μ ⊲ A') → A ≈ A'
≈after-put {_} {μ} {A} {A'} eq .to = ≲after-put {_} {μ} {A} {A'} (eq .to)
≈after-put {_} {μ} {A} {A'} eq .from = ≲after-put {_} {μ} {A'} {A} (eq .from)

not≈ : ∀{n} {A B : Type n} → ¬ Sim (subst (λ _ → skip) A) (subst (λ _ → skip) B) → ¬ A ≈ B
not≈ nsim eq = contradiction (eq .to) nsim

≈measure : ∀{n} {μ ν} {A B : Type n} → (μ ⊲ A) ≈ (ν ⊲ B) → μ ≡ ν
≈measure eq with eq .to {σ = λ _ → skip} .Sim.next put
... | _ , put , _ = refl

