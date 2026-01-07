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

-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning

open import Type
open import Skip
open import Transitions

-- SIMULATION

record Sim {n r} (A B : PreType n r) : Set where
  coinductive
  field
    sim-skip : Skip A → Skip B
    sim-next : ∀{ℓ A'} → A ⊨ ℓ ⇒ A' → ∃[ B' ] (B ⊨ ℓ ⇒ B' × Sim A' B')

open Sim public

sim-refl : ∀{n r} {A : PreType n r} → Sim A A
sim-refl .sim-skip sk = sk
sim-refl .sim-next tr = _ , tr , sim-refl

sim-trans : ∀{n r} {A B C : PreType n r} → Sim A B → Sim B C → Sim A C
sim-trans p q .sim-skip sk = q .sim-skip (p .sim-skip sk)
sim-trans p q .sim-next tr with p .sim-next tr
... | _ , tr' , p' with q .sim-next tr'
... | _ , tr'' , q' = _ , tr'' , sim-trans p' q'

sim-rec-unfold : ∀{n r} {A : PreType n (suc r)} → Sim (rec A) (unfold A)
sim-rec-unfold .sim-skip (rec sk) = sk
sim-rec-unfold .sim-next (rec tr) = _ , tr , sim-refl

sim-unfold-rec : ∀{n r} {A : PreType n (suc r)} → Sim (unfold A) (rec A)
sim-unfold-rec .sim-skip sk = rec sk
sim-unfold-rec .sim-next tr = _ , rec tr , sim-refl

sim-dual : ∀{n r} {A B : PreType n r} → Sim A B → Sim (dual A) (dual B)
sim-dual le .sim-skip sk = skip-dual (le .sim-skip (skip-dual sk))
sim-dual le .sim-next tr with le .sim-next (transition-dual tr)
... | _ , tr' , le' = _ , transition-dual tr' , sim-dual le'

-- closed-absorbing-r : ∀{n r} {A B : PreType n r} → Closed A → A sim- (A ⨟ B)
-- closed-absorbing-r comp .sim-next tr = _ , seql tr (comp .closed-skip tr) , closed-absorbing-r (comp .closed-cont tr)

-- closed-absorbing-l : ∀{n r} {A B : PreType n r} → Closed A → (A ⨟ B) sim- A
-- closed-absorbing-l comp .sim-next (seql tr neq) = _ , tr , closed-absorbing-l (comp .closed-cont tr)
-- closed-absorbing-l comp .sim-next (seqr tr tr') = contradiction refl (comp .closed-skip tr)

-- ClosedSubstitution : ∀{m n r} → (Fin m → PreType n r) → Set
-- ClosedSubstitution σ = ∀ x → Closed (σ x)

-- DualPreserving : ∀{m n r s} (f : PreType m r → PreType n s) → Set
-- DualPreserving f = dual ∘ f ≡ f ∘ dual

-- dual-preserving : ∀{m n r s} {f : PreType m r → PreType n s} → DualPreserving f → DualPreserving (dual ∘ f)
-- dual-preserving = cong (dual ∘_)

_≲_ : ∀{n r} → PreType n r → PreType n r → Set
_≲_ {n} {r} A B = ∀{m s} {σ : Fin n → PreType m s} {τ : Fin r → PreType m s} → Sim (subst σ τ A) (subst σ τ B)

≲refl : ∀{n r} {A : PreType n r} → A ≲ A
≲refl = sim-refl

≲trans : ∀{n r} {A B C : PreType n r} → A ≲ B → B ≲ C → A ≲ C
≲trans p q = sim-trans p q

≲dual : ∀{n r} {A B : PreType n r} → A ≲ B → dual A ≲ dual B
≲dual {n} {r} {A} {B} le = {!!}

subst-compose : ∀{m n o r s t} (σ : Fin m → PreType n s) (τ : Fin r → PreType n s)
                (σ' : Fin n → PreType o t) (τ' : Fin s → PreType o t) →
                (A : PreType m r) →
                subst σ' τ' (subst σ τ A) ≡ subst (subst σ' τ' ∘ σ) (subst σ' τ' ∘ τ) A
subst-compose {m} {n} {o} {r} {s} {t} σ τ σ' τ' (var x) = refl
subst-compose {m} {n} {o} {r} {s} {t} σ τ σ' τ' (rav x) = {!!}
subst-compose {m} {n} {o} {r} {s} {t} σ τ σ' τ' skip = refl
subst-compose {m} {n} {o} {r} {s} {t} σ τ σ' τ' ⊤ = refl
subst-compose {m} {n} {o} {r} {s} {t} σ τ σ' τ' 𝟘 = {!!}
subst-compose {m} {n} {o} {r} {s} {t} σ τ σ' τ' ⊥ = {!!}
subst-compose {m} {n} {o} {r} {s} {t} σ τ σ' τ' 𝟙 = {!!}
subst-compose {m} {n} {o} {r} {s} {t} σ τ σ' τ' (A ⨟ A₁) = {!!}
subst-compose {m} {n} {o} {r} {s} {t} σ τ σ' τ' (A & A₁) = {!!}
subst-compose {m} {n} {o} {r} {s} {t} σ τ σ' τ' (A ⊕ A₁) = {!!}
subst-compose {m} {n} {o} {r} {s} {t} σ τ σ' τ' (A ⅋ A₁) = {!!}
subst-compose {m} {n} {o} {r} {s} {t} σ τ σ' τ' (A ⊗ A₁) = {!!}
subst-compose {m} {n} {o} {r} {s} {t} σ τ σ' τ' (inv x) = refl
subst-compose {m} {n} {o} {r} {s} {t} σ τ σ' τ' (rec A) =
  cong rec {!!}

≲subst : ∀{m n r s} {A B : PreType m r} (σ : Fin m → PreType n s) (τ : Fin r → PreType n s) →
         A ≲ B → subst σ τ A ≲ subst σ τ B
≲subst σ τ le = {!!}

-- EQUIVALENCE

record _≅_ {n r} (A B : PreType n r) : Set where
  field
    to   : A ≲ B
    from : B ≲ A

open _≅_ public

≅refl : ∀{n r} {A : PreType n r} → A ≅ A
≅refl .to = sim-refl
≅refl .from = sim-refl

-- ≅sym : ∀{n r} {A B : PreType n r} → A ≅ B → B ≅ A
-- ≅sym p .to = p .from
-- ≅sym p .from = p .to

-- ≅trans : ∀{n r} {A B C : PreType n r} → A ≅ B → B ≅ C → A ≅ C
-- ≅trans p q .to = sim-trans (p .to) (q .to)
-- ≅trans p q .from = sim-trans (q .from) (p .from)

-- ≅after : ∀{n r} {ℓ} {A B A' B' : PreType n r} → A ≅ B → A ⊨ ℓ ⇒ A' → B ⊨ ℓ ⇒ B' → A' ≅ B'
-- ≅after eq at bt with eq .to .sim-next at | eq .from .sim-next bt
-- ... | _ , bt' , ale | _ , at' , ble rewrite deterministic at at' | deterministic bt bt' = record { to = ale ; from = ble }

-- ≅dual : ∀{n r} {A B : PreType n r} → A ≅ B → dual A ≅ dual B
-- ≅dual {n} {r} {A} {B} eq .to   = ≲dual {n} {r} {A} {B} (eq .to)
-- ≅dual {n} {r} {A} {B} eq .from = ≲dual {n} {r} {B} {A} (eq .from)

≅unfold : ∀{n r} {A : PreType n (suc r)} → rec A ≅ unfold A
≅unfold .to   = {!!}
≅unfold .from = {!!}

-- closed-absorbing : ∀{n r} {A B : PreType n r} → Closed A → A ≅ (A ⨟ B)
-- closed-absorbing comp .to = closed-absorbing-r comp
-- closed-absorbing comp .from = closed-absorbing-l comp

-- ≅subst : ∀{m n r} {A B : PreType m r} (σ : Fin m → PreType n r) → A ≅ B → subst σ inv A ≅ subst σ inv B
-- ≅subst σ eq .to = sim-subst σ (eq .to)
-- ≅subst σ eq .from = sim-subst σ (eq .from)
