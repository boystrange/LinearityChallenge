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

record _≲_ {n r} (A B : PreType n r) : Set where
  coinductive
  field
    ≲skip : Skip A → Skip B
    ≲cont : ∀{ℓ A'} → A ⊨ ℓ ⇒ A' → ∃[ B' ] (B ⊨ ℓ ⇒ B' × A' ≲ B')

open _≲_ public

≲refl : ∀{n r} {A : PreType n r} → A ≲ A
≲refl .≲skip sk = sk
≲refl .≲cont tr = _ , tr , ≲refl

≲trans : ∀{n r} {A B C : PreType n r} → A ≲ B → B ≲ C → A ≲ C
≲trans p q .≲skip sk = q .≲skip (p .≲skip sk)
≲trans p q .≲cont tr with p .≲cont tr
... | _ , tr' , p' with q .≲cont tr'
... | _ , tr'' , q' = _ , tr'' , ≲trans p' q'

≲unfold : ∀{n r} {A : PreType n (suc r)} → rec A ≲ unfold A
≲unfold .≲skip (rec sk) = sk
≲unfold .≲cont (rec tr) = _ , tr , ≲refl

unfold≲ : ∀{n r} {A : PreType n (suc r)} → unfold A ≲ rec A
unfold≲ .≲skip sk = rec sk
unfold≲ .≲cont tr = _ , rec tr , ≲refl

≲dual : ∀{n r} {A B : PreType n r} → A ≲ B → dual A ≲ dual B
≲dual le .≲skip sk = skip-dual (le .≲skip (skip-dual sk))
≲dual le .≲cont tr with le .≲cont (transition-dual tr)
... | _ , tr' , le' = _ , transition-dual tr' , ≲dual le'

-- closed-absorbing-r : ∀{n r} {A B : PreType n r} → Closed A → A ≲ (A ⨟ B)
-- closed-absorbing-r comp .≲cont tr = _ , seql tr (comp .closed-skip tr) , closed-absorbing-r (comp .closed-cont tr)

-- closed-absorbing-l : ∀{n r} {A B : PreType n r} → Closed A → (A ⨟ B) ≲ A
-- closed-absorbing-l comp .≲cont (seql tr neq) = _ , tr , closed-absorbing-l (comp .closed-cont tr)
-- closed-absorbing-l comp .≲cont (seqr tr tr') = contradiction refl (comp .closed-skip tr)

-- ClosedSubstitution : ∀{m n r} → (Fin m → PreType n r) → Set
-- ClosedSubstitution σ = ∀ x → Closed (σ x)

≲subst : ∀{m n r} {A B : PreType m r} (σ : Fin m → PreType n r) → A ≲ B → subst σ inv A ≲ subst σ inv B
≲subst σ le .≲skip = {!!}
≲subst σ le .≲cont = {!!}

-- TRACES

data Trace (n : ℕ) : Set where
  [] ε : Trace n
  _∷_  : Label n → Trace n → Trace n

data _HasTrace_ {n r} (A : PreType n r) : Trace n → Set where
  nil : A HasTrace []
  eps : Skip A → A HasTrace ε
  obs : ∀{ℓ B φ} → A ⊨ ℓ ⇒ B → B HasTrace φ → A HasTrace (ℓ ∷ φ)

_⊆_ : ∀{n r} (A B : PreType n r) → Set
A ⊆ B = ∀{φ} → A HasTrace φ → B HasTrace φ

-- after-ε-skip : ∀{n r} {A B : PreType n r} → A ⊨ ε ⇒ B → B ≡ skip
-- after-ε-skip skip = refl
-- after-ε-skip (seql _ ne) = contradiction refl ne
-- after-ε-skip (seqr _ tr) = after-ε-skip tr
-- after-ε-skip (rec tr) = after-ε-skip tr

≲-⊆ : ∀{n r} {A B : PreType n r} → A ≲ B → A ⊆ B
≲-⊆ le nil = nil
≲-⊆ le (eps sk) = eps (le .≲skip sk)
≲-⊆ le (obs tr x) with le .≲cont tr
... | _ , tr' , le' = obs tr' (≲-⊆ le' x)

⊆after : ∀{n r ℓ} {A A' B : PreType n r} → A ⊆ B → A ⊨ ℓ ⇒ A' → ∃[ B' ] B ⊨ ℓ ⇒ B' × A' ⊆ B'
⊆after inc tr = {!!}

⊆-≲ : ∀{n r} {A B : PreType n r} → A ⊆ B → A ≲ B
⊆-≲ inc .≲skip sk with inc (eps sk)
... | eps sk' = sk'
⊆-≲ inc .≲cont tr with ⊆after inc tr
... | _ , tr' , inc' = _ , tr' , ⊆-≲ inc'

-- EQUIVALENCE

record _≅_ {n r} (A B : PreType n r) : Set where
  field
    to : A ≲ B
    from : B ≲ A

open _≅_ public

≅refl : ∀{n r} {A : PreType n r} → A ≅ A
≅refl .to = ≲refl
≅refl .from = ≲refl

≅sym : ∀{n r} {A B : PreType n r} → A ≅ B → B ≅ A
≅sym p .to = p .from
≅sym p .from = p .to

≅trans : ∀{n r} {A B C : PreType n r} → A ≅ B → B ≅ C → A ≅ C
≅trans p q .to = ≲trans (p .to) (q .to)
≅trans p q .from = ≲trans (q .from) (p .from)

≅after : ∀{n r} {ℓ} {A B A' B' : PreType n r} → A ≅ B → A ⊨ ℓ ⇒ A' → B ⊨ ℓ ⇒ B' → A' ≅ B'
≅after eq at bt with eq .to .≲cont at | eq .from .≲cont bt
... | _ , bt' , ale | _ , at' , ble rewrite deterministic at at' | deterministic bt bt' = record { to = ale ; from = ble }

≅dual : ∀{n r} {A B : PreType n r} → A ≅ B → dual A ≅ dual B
≅dual eq .to = ≲dual (eq .to)
≅dual eq .from = ≲dual (eq .from)

≅unfold : ∀{n r} {A : PreType n (suc r)} → rec A ≅ unfold A
≅unfold .to = ≲unfold
≅unfold .from = unfold≲

-- closed-absorbing : ∀{n r} {A B : PreType n r} → Closed A → A ≅ (A ⨟ B)
-- closed-absorbing comp .to = closed-absorbing-r comp
-- closed-absorbing comp .from = closed-absorbing-l comp

≅subst : ∀{m n r} {A B : PreType m r} (σ : Fin m → PreType n r) → A ≅ B → subst σ inv A ≅ subst σ inv B
≅subst σ eq .to = ≲subst σ (eq .to)
≅subst σ eq .from = ≲subst σ (eq .from)
