{-# OPTIONS --rewriting --guardedness #-}
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Agda.Builtin.Equality.Rewrite

open import Type

data Label : Set where
  ε ⊥ 𝟙 ⊤ 𝟘 &L &R ⊕L ⊕R ⅋L ⅋R ⊗L ⊗R : Label

dual-label : Label → Label
dual-label ε = ε
dual-label ⊥ = 𝟙
dual-label 𝟙 = ⊥
dual-label ⊤ = 𝟘
dual-label 𝟘 = ⊤
dual-label &L = ⊕L
dual-label &R = ⊕R
dual-label ⊕L = &L
dual-label ⊕R = &R
dual-label ⅋L = ⊗L
dual-label ⅋R = ⊗R
dual-label ⊗L = ⅋L
dual-label ⊗R = ⅋R

dual-label-inv : ∀{ℓ} → dual-label (dual-label ℓ) ≡ ℓ
dual-label-inv {ε} = refl
dual-label-inv {⊥} = refl
dual-label-inv {𝟙} = refl
dual-label-inv {⊤} = refl
dual-label-inv {𝟘} = refl
dual-label-inv {&L} = refl
dual-label-inv {&R} = refl
dual-label-inv {⊕L} = refl
dual-label-inv {⊕R} = refl
dual-label-inv {⅋L} = refl
dual-label-inv {⅋R} = refl
dual-label-inv {⊗L} = refl
dual-label-inv {⊗R} = refl

{-# REWRITE dual-label-inv #-}

dual-label-not-skip : ∀{ℓ} → ℓ ≢ ε → dual-label ℓ ≢ ε
dual-label-not-skip neq eq = contradiction (cong dual-label eq) neq

data _⊨_⇒_ : GroundType → Label → GroundType → Set where
  skip : skip ⊨ ε ⇒ skip
  ⊥    : ⊥ ⊨ ⊥ ⇒ ⊥
  𝟙    : 𝟙 ⊨ 𝟙 ⇒ 𝟙
  ⊤    : ⊤ ⊨ ⊤ ⇒ ⊤
  𝟘    : 𝟘 ⊨ 𝟘 ⇒ 𝟘
  &L   : ∀{A B} → (A & B) ⊨ &L ⇒ A
  &R   : ∀{A B} → (A & B) ⊨ &R ⇒ B
  ⊕L   : ∀{A B} → (A ⊕ B) ⊨ ⊕L ⇒ A
  ⊕R   : ∀{A B} → (A ⊕ B) ⊨ ⊕R ⇒ B
  ⅋L   : ∀{A B} → (A ⅋ B) ⊨ ⅋L ⇒ A
  ⅋R   :  ∀{A B} → (A ⅋ B) ⊨ ⅋R ⇒ B
  ⊗L   : ∀{A B} → (A ⊗ B) ⊨ ⊗L ⇒ A
  ⊗R   : ∀{A B} → (A ⊗ B) ⊨ ⊗R ⇒ B
  seql : ∀{A B C ℓ} → A ⊨ ℓ ⇒ B → ℓ ≢ ε → (A ⨟ C) ⊨ ℓ ⇒ (B ⨟ C)
  seqr : ∀{A B C ℓ} → A ⊨ ε ⇒ skip → B ⊨ ℓ ⇒ C → (A ⨟ B) ⊨ ℓ ⇒ C
  rec  : ∀{A B ℓ} → unfold A ⊨ ℓ ⇒ B → rec A ⊨ ℓ ⇒ B

only-skip : ∀{ℓ A B C} → A ⊨ ℓ ⇒ B → A ⊨ ε ⇒ C → ℓ ≡ ε
only-skip skip skip = refl
only-skip (seql _ _) (seql _ ne) = contradiction refl ne
only-skip (seqr _ _) (seql _ ne) = contradiction refl ne
only-skip (seql x ne) (seqr y _) = contradiction (only-skip x y) ne
only-skip (seqr _ x) (seqr _ y) = only-skip x y
only-skip (rec x) (rec y) = only-skip x y

deterministic : ∀{ℓ A B C} → A ⊨ ℓ ⇒ B → A ⊨ ℓ ⇒ C → B ≡ C
deterministic skip skip = refl
deterministic ⊥ ⊥ = refl
deterministic 𝟙 𝟙 = refl
deterministic ⊤ ⊤ = refl
deterministic 𝟘 𝟘 = refl
deterministic &L &L = refl
deterministic &R &R = refl
deterministic ⊕L ⊕L = refl
deterministic ⊕R ⊕R = refl
deterministic ⅋L ⅋L = refl
deterministic ⅋R ⅋R = refl
deterministic ⊗L ⊗L = refl
deterministic ⊗R ⊗R = refl
deterministic (seql x ne) (seql y ne') = cong₂ _⨟_ (deterministic x y) refl
deterministic (seql x ne) (seqr y _) = contradiction (only-skip x y) ne
deterministic (seqr sk _) (seql y ne) = contradiction (only-skip y sk) ne
deterministic (seqr _ x) (seqr _ y) = deterministic x y
deterministic (rec x) (rec y) = deterministic x y

transition-dual : ∀{A B ℓ} → A ⊨ ℓ ⇒ B → dual A ⊨ dual-label ℓ ⇒ dual B
transition-dual skip = skip
transition-dual ⊥ = 𝟙
transition-dual 𝟙 = ⊥
transition-dual ⊤ = 𝟘
transition-dual 𝟘 = ⊤
transition-dual &L = ⊕L
transition-dual &R = ⊕R
transition-dual ⊕L = &L
transition-dual ⊕R = &R
transition-dual ⅋L = ⊗L
transition-dual ⅋R = ⊗R
transition-dual ⊗L = ⅋L
transition-dual ⊗R = ⅋R
transition-dual (seqr sk tr) = seqr (transition-dual sk) (transition-dual tr)
transition-dual (seql tr ne) = seql (transition-dual tr) (dual-label-not-skip ne)
transition-dual {A = rec A} (rec tr) with transition-dual tr
... | tr' rewrite dual-unfold A = rec tr'

-- record Closed {n r} (A : PreType n r) : Set where
--   coinductive
--   field
--     closed-skip : ¬ Skip A
--     closed-cont : ∀{ℓ B} → A ⊨ ℓ ⇒ B → Closed B

-- open Closed public
