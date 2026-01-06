{-# OPTIONS --rewriting --guardedness #-}
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Agda.Builtin.Equality.Rewrite

open import Type

data Skip {n r} : PreType n r → Set where
  skip : Skip skip
  seq  : ∀{A B} → Skip A → Skip B → Skip (A ⨟ B)
  rec  : ∀{A} → Skip (unfold A) → Skip (rec A)

skip-dual : ∀{n r} {A : PreType n r} → Skip A → Skip (dual A)
skip-dual skip = skip
skip-dual (seq sk sk') = seq (skip-dual sk) (skip-dual sk')
skip-dual (rec {A} sk) with skip-dual sk
... | sk' rewrite dual-unfold A = rec sk'

