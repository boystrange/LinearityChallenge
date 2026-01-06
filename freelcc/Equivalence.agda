{-# OPTIONS --rewriting --guardedness #-}
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Agda.Builtin.Equality.Rewrite

open import Type

-- SIMULATION

record _≲_ {n r} (A B : PreType n r) : Set where
  coinductive
  field
    ≲cont : ∀{ℓ A'} → A ⊨ ℓ ⇒ A' → ∃[ B' ] (B ⊨ ℓ ⇒ B' × A' ≲ B')

open _≲_ public

≲refl : ∀{n r} {A : PreType n r} → A ≲ A
≲refl .≲cont tr = _ , tr , ≲refl

≲trans : ∀{n r} {A B C : PreType n r} → A ≲ B → B ≲ C → A ≲ C
≲trans p q .≲cont tr with p .≲cont tr
... | _ , tr' , p' with q .≲cont tr'
... | _ , tr'' , q' = _ , tr'' , ≲trans p' q'

≲unfold : ∀{n r} {A : PreType n (suc r)} → rec A ≲ unfold A
≲unfold .≲cont (rec tr) = _ , tr , ≲refl

unfold≲ : ∀{n r} {A : PreType n (suc r)} → unfold A ≲ rec A
unfold≲ .≲cont tr = _ , rec tr , ≲refl

≲dual : ∀{n r} {A B : PreType n r} → A ≲ B → dual A ≲ dual B
≲dual le .≲cont tr with le .≲cont (transition-dual tr)
... | _ , tr' , le' = _ , transition-dual tr' , ≲dual le'

closed-absorbing-r : ∀{n r} {A B : PreType n r} → Closed A → A ≲ (A ⨟ B)
closed-absorbing-r comp .≲cont tr = _ , seql tr (comp .closed-skip tr) , closed-absorbing-r (comp .closed-cont tr)

closed-absorbing-l : ∀{n r} {A B : PreType n r} → Closed A → (A ⨟ B) ≲ A
closed-absorbing-l comp .≲cont (seql tr neq) = _ , tr , closed-absorbing-l (comp .closed-cont tr)
closed-absorbing-l comp .≲cont (seqr tr tr') = contradiction refl (comp .closed-skip tr)

≲subst : ∀{m n r} {A B : PreType m r} (σ : Fin m → PreType n r) → A ≲ B → subst σ inv A ≲ subst σ inv B
≲subst σ le .≲cont = {!!}

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

closed-absorbing : ∀{n r} {A B : PreType n r} → Closed A → A ≅ (A ⨟ B)
closed-absorbing comp .to = closed-absorbing-r comp
closed-absorbing comp .from = closed-absorbing-l comp

≅subst : ∀{m n r} {A B : PreType m r} (σ : Fin m → PreType n r) → A ≅ B → subst σ inv A ≅ subst σ inv B
≅subst σ eq .to = ≲subst σ (eq .to)
≅subst σ eq .from = ≲subst σ (eq .from)
