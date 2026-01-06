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

record _≲_ {r} (A B : PreType r) : Set where
  coinductive
  field
    ≲cont : ∀{ℓ A'} → A ⊨ ℓ ⇒ A' → ∃[ B' ] (B ⊨ ℓ ⇒ B' × A' ≲ B')

open _≲_ public

≲refl : ∀{r} {A : PreType r} → A ≲ A
≲refl .≲cont tr = _ , tr , ≲refl

≲trans : ∀{r} {A B C : PreType r} → A ≲ B → B ≲ C → A ≲ C
≲trans p q .≲cont tr with p .≲cont tr
... | _ , tr' , p' with q .≲cont tr'
... | _ , tr'' , q' = _ , tr'' , ≲trans p' q'

≲unfold : ∀{r} {A : PreType (suc r)} → rec A ≲ unfold A
≲unfold .≲cont (rec tr) = _ , tr , ≲refl

unfold≲ : ∀{r} {A : PreType (suc r)} → unfold A ≲ rec A
unfold≲ .≲cont tr = _ , rec tr , ≲refl

≲dual : ∀{n} {A B : PreType n} → A ≲ B → dual A ≲ dual B
≲dual le .≲cont tr with le .≲cont (transition-dual tr)
... | _ , tr' , le' = _ , transition-dual tr' , ≲dual le'

closed-absorbing-r : ∀{n} {A B : PreType n} → Closed A → A ≲ (A ⨟ B)
closed-absorbing-r comp .≲cont tr = _ , seql tr (comp .closed-skip tr) , closed-absorbing-r (comp .closed-cont tr)

closed-absorbing-l : ∀{r} {A B : PreType r} → Closed A → (A ⨟ B) ≲ A
closed-absorbing-l comp .≲cont (seql tr neq) = _ , tr , closed-absorbing-l (comp .closed-cont tr)
closed-absorbing-l comp .≲cont (seqr tr tr') = contradiction refl (comp .closed-skip tr)

-- EQUIVALENCE

record _≅_ {r} (A B : PreType r) : Set where
  field
    to : A ≲ B
    from : B ≲ A

open _≅_ public

≅refl : ∀{r} {A : PreType r} → A ≅ A
≅refl .to = ≲refl
≅refl .from = ≲refl

≅sym : ∀{r} {A B : PreType r} → A ≅ B → B ≅ A
≅sym p .to = p .from
≅sym p .from = p .to

≅trans : ∀{r} {A B C : PreType r} → A ≅ B → B ≅ C → A ≅ C
≅trans p q .to = ≲trans (p .to) (q .to)
≅trans p q .from = ≲trans (q .from) (p .from)

≅after : ∀{r} {ℓ} {A B A' B' : PreType r} → A ≅ B → A ⊨ ℓ ⇒ A' → B ⊨ ℓ ⇒ B' → A' ≅ B'
≅after eq at bt with eq .to .≲cont at | eq .from .≲cont bt
... | _ , bt' , ale | _ , at' , ble rewrite deterministic at at' | deterministic bt bt' = record { to = ale ; from = ble }

≅dual : ∀{r} {A B : PreType r} → A ≅ B → dual A ≅ dual B
≅dual eq .to = ≲dual (eq .to)
≅dual eq .from = ≲dual (eq .from)

≅unfold : ∀{r} {A : PreType (suc r)} → rec A ≅ unfold A
≅unfold .to = ≲unfold
≅unfold .from = unfold≲

closed-absorbing : ∀{r} {A B : PreType r} → Closed A → A ≅ (A ⨟ B)
closed-absorbing comp .to = closed-absorbing-r comp
closed-absorbing comp .from = closed-absorbing-l comp
