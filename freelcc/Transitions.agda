{-# OPTIONS --rewriting --guardedness #-}
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Agda.Builtin.Equality.Rewrite

open import Type
open import Skip

data Label (n : ℕ) : Set where
  -- ε : Label n
  ⊥ 𝟙 ⊤ 𝟘 &L &R ⊕L ⊕R ⅋L ⅋R ⊗L ⊗R : Label n
  var rav : Fin n → Label n

dual-label : ∀{n} → Label n → Label n
-- dual-label ε = ε
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
dual-label (var x) = rav x
dual-label (rav x) = var x

dual-label-inv : ∀{n} {ℓ : Label n} → dual-label (dual-label ℓ) ≡ ℓ
dual-label-inv {_} {var x} = refl
dual-label-inv {_} {rav x} = refl
-- dual-label-inv {_} {ε} = refl
dual-label-inv {_} {⊥} = refl
dual-label-inv {_} {𝟙} = refl
dual-label-inv {_} {⊤} = refl
dual-label-inv {_} {𝟘} = refl
dual-label-inv {_} {&L} = refl
dual-label-inv {_} {&R} = refl
dual-label-inv {_} {⊕L} = refl
dual-label-inv {_} {⊕R} = refl
dual-label-inv {_} {⅋L} = refl
dual-label-inv {_} {⅋R} = refl
dual-label-inv {_} {⊗L} = refl
dual-label-inv {_} {⊗R} = refl

{-# REWRITE dual-label-inv #-}

-- dual-label-not-skip : ∀{n} {ℓ : Label n} → ℓ ≢ ε → dual-label ℓ ≢ ε
-- dual-label-not-skip neq eq = contradiction (cong dual-label eq) neq

data _⊨_⇒_ {n r} : PreType n r → Label n → PreType n r → Set where
  -- skip : skip ⊨ ε ⇒ skip
  ⊥    : ⊥ ⊨ ⊥ ⇒ ⊥
  𝟙    : 𝟙 ⊨ 𝟙 ⇒ 𝟙
  ⊤    : ⊤ ⊨ ⊤ ⇒ ⊤
  𝟘    : 𝟘 ⊨ 𝟘 ⇒ 𝟘
  var  : ∀{x} → var x ⊨ var x ⇒ var x
  rav  : ∀{x} → rav x ⊨ rav x ⇒ rav x
  &L   : ∀{A B} → (A & B) ⊨ &L ⇒ A
  &R   : ∀{A B} → (A & B) ⊨ &R ⇒ B
  ⊕L   : ∀{A B} → (A ⊕ B) ⊨ ⊕L ⇒ A
  ⊕R   : ∀{A B} → (A ⊕ B) ⊨ ⊕R ⇒ B
  ⅋L   : ∀{A B} → (A ⅋ B) ⊨ ⅋L ⇒ A
  ⅋R   :  ∀{A B} → (A ⅋ B) ⊨ ⅋R ⇒ B
  ⊗L   : ∀{A B} → (A ⊗ B) ⊨ ⊗L ⇒ A
  ⊗R   : ∀{A B} → (A ⊗ B) ⊨ ⊗R ⇒ B
  seql : ∀{A B C ℓ} → A ⊨ ℓ ⇒ B → (A ⨟ C) ⊨ ℓ ⇒ (B ⨟ C)
  seqr : ∀{A B C ℓ} → Skip A → B ⊨ ℓ ⇒ C → (A ⨟ B) ⊨ ℓ ⇒ C
  rec  : ∀{A B ℓ} → unfold A ⊨ ℓ ⇒ B → rec A ⊨ ℓ ⇒ B

-- only-skip : ∀{n r ℓ} {A B C : PreType n r} → A ⊨ ℓ ⇒ B → A ⊨ ε ⇒ C → ℓ ≡ ε
-- only-skip skip skip = refl
-- only-skip (seql _ _) (seql _ ne) = contradiction refl ne
-- only-skip (seqr _ _) (seql _ ne) = contradiction refl ne
-- only-skip (seql x ne) (seqr y _) = contradiction (only-skip x y) ne
-- only-skip (seqr _ x) (seqr _ y) = only-skip x y
-- only-skip (rec x) (rec y) = only-skip x y

transition-not-skip : ∀{n r ℓ} {A B : PreType n r} → A ⊨ ℓ ⇒ B → ¬ Skip A
transition-not-skip (seql tr) (seq sk _) = transition-not-skip tr sk
transition-not-skip (seqr _ tr) (seq _ sk) = transition-not-skip tr sk
transition-not-skip (rec tr) (rec sk) = transition-not-skip tr sk

deterministic : ∀{n r ℓ} {A B C : PreType n r} → A ⊨ ℓ ⇒ B → A ⊨ ℓ ⇒ C → B ≡ C
deterministic var var = refl
deterministic rav rav = refl
-- deterministic skip skip = refl
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
deterministic (seql x) (seql y) = cong₂ _⨟_ (deterministic x y) refl
-- deterministic (seql x ne) (seqr y _) = contradiction (only-skip x y) ne
deterministic (seql x) (seqr sk _) = contradiction sk (transition-not-skip x)
-- deterministic (seqr x _) (seql y ne) = contradiction (only-skip y x) ne
deterministic (seqr sk _) (seql y) = contradiction sk (transition-not-skip y)
deterministic (seqr _ x) (seqr _ y) = deterministic x y
deterministic (rec x) (rec y) = deterministic x y

transition-dual : ∀{n r} {A B : PreType n r} {ℓ} → A ⊨ ℓ ⇒ B → dual A ⊨ dual-label ℓ ⇒ dual B
transition-dual var = rav
transition-dual rav = var
-- transition-dual skip = skip
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
-- transition-dual (seqr tr tr') = seqr (transition-dual tr) (transition-dual tr')
transition-dual (seqr sk tr) = seqr (skip-dual sk) (transition-dual tr)
-- transition-dual (seql tr neq) = seql (transition-dual tr) (dual-label-not-skip neq)
transition-dual (seql tr) = seql (transition-dual tr)
transition-dual {A = rec A} (rec tr) with transition-dual tr
... | tr' rewrite dual-subst var (s-just (rec A)) A | dual-s-just (rec A) = rec tr'

record Closed {n r} (A : PreType n r) : Set where
  coinductive
  field
    closed-skip : ¬ Skip A
    closed-cont : ∀{ℓ B} → A ⊨ ℓ ⇒ B → Closed B

open Closed public

