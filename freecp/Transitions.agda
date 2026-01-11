{-# OPTIONS --rewriting --guardedness #-}
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Nullary using (¬_; contradiction; contraposition)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂)

open import Type

data Label : Set where
  ε ⊥ 𝟙 ⊤ 𝟘 &L &R ⊕L ⊕R ⅋L ⅋R ⊗L ⊗R : Label
  put get : ℕ → Label

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
dual-label (put μ) = get μ
dual-label (get μ) = put μ

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
dual-label-inv {put μ} = refl
dual-label-inv {get μ} = refl

{-# REWRITE dual-label-inv #-}

data Special : Label → Set where
  ε  : Special ε
  ⊗L : Special ⊗L
  ⅋L : Special ⅋L

dual-special : ∀{ℓ} → Special ℓ → Special (dual-label ℓ)
dual-special ε = ε
dual-special ⊗L = ⅋L
dual-special ⅋L = ⊗L

data _⊨_⇒_ {n r} : PreType n r → Label → PreType n r → Set where
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
  seq  : ∀{A B C ℓ} → A ⊨ ℓ ⇒ B → ¬ Special ℓ → (A ⨟ C) ⊨ ℓ ⇒ (B ⨟ C)
  seqε : ∀{A B C ℓ} → A ⊨ ε ⇒ skip → B ⊨ ℓ ⇒ C → (A ⨟ B) ⊨ ℓ ⇒ C
  seq⊗ : ∀{A B C} → A ⊨ ⊗L ⇒ C → (A ⨟ B) ⊨ ⊗L ⇒ C
  seq⅋ : ∀{A B C} → A ⊨ ⅋L ⇒ C → (A ⨟ B) ⊨ ⅋L ⇒ C
  put  : ∀{μ A} → (μ ⊲ A) ⊨ put μ ⇒ A
  get  : ∀{μ A} → (μ ⊳ A) ⊨ get μ ⇒ A
  rec  : ∀{A B ℓ} → unfold A ⊨ ℓ ⇒ B → rec A ⊨ ℓ ⇒ B

-- data _⊨_ {n r} : PreType n r → Label → Set where
--   skip : skip ⊨ ε
--   ⊥    : ⊥ ⊨ ⊥
--   𝟙    : 𝟙 ⊨ 𝟙
--   ⊤    : ⊤ ⊨ ⊤
--   𝟘    : 𝟘 ⊨ 𝟘
--   &L   : ∀{A B} → (A & B) ⊨ &L
--   &R   : ∀{A B} → (A & B) ⊨ &R
--   ⊕L   : ∀{A B} → (A ⊕ B) ⊨ ⊕L
--   ⊕R   : ∀{A B} → (A ⊕ B) ⊨ ⊕R
--   ⅋L   : ∀{A B} → (A ⅋ B) ⊨ ⅋L
--   ⅋R   :  ∀{A B} → (A ⅋ B) ⊨ ⅋R
--   ⊗L   : ∀{A B} → (A ⊗ B) ⊨ ⊗L
--   ⊗R   : ∀{A B} → (A ⊗ B) ⊨ ⊗R
--   seq  : ∀{A B ℓ} → ¬ Special ℓ → A ⊨ ℓ → (A ⨟ B) ⊨ ℓ
--   seqε : ∀{A B ℓ} → A ⊨ ε → B ⊨ ℓ → (A ⨟ B) ⊨ ℓ
--   seq⊗ : ∀{A B} → A ⊨ ⊗L → (A ⨟ B) ⊨ ⊗L
--   seq⅋ : ∀{A B} → A ⊨ ⅋L → (A ⨟ B) ⊨ ⅋L
--   put  : ∀{μ A} → (μ ⊲ A) ⊨ put μ
--   get  : ∀{μ A} → (μ ⊳ A) ⊨ get μ
--   rec  : ∀{A ℓ} → unfold A ⊨ ℓ → rec A ⊨ ℓ

-- dual-transition : ∀{n r ℓ} {A : PreType n r} → A ⊨ ℓ → dual A ⊨ dual-label ℓ
-- dual-transition skip = skip
-- dual-transition ⊥ = 𝟙
-- dual-transition 𝟙 = ⊥
-- dual-transition ⊤ = 𝟘
-- dual-transition 𝟘 = ⊤
-- dual-transition &L = ⊕L
-- dual-transition &R = ⊕R
-- dual-transition ⊕L = &L
-- dual-transition ⊕R = &R
-- dual-transition ⅋L = ⊗L
-- dual-transition ⅋R = ⊗R
-- dual-transition ⊗L = ⅋L
-- dual-transition ⊗R = ⅋R
-- dual-transition (seq ns tr) = seq (contraposition dual-special ns) (dual-transition tr)
-- dual-transition (seqε sk tr) = seqε (dual-transition sk) (dual-transition tr)
-- dual-transition (seq⊗ tr) = seq⅋ (dual-transition tr)
-- dual-transition (seq⅋ tr) = seq⊗ (dual-transition tr)
-- dual-transition put = get
-- dual-transition get = put
-- dual-transition {A = rec A} (rec tr) = rec (dual-transition tr)

-- after : ∀{n r ℓ} {A : PreType n r} → A ⊨ ℓ → PreType n r
-- after {A = skip} skip = skip
-- after {A = ⊤} ⊤ = ⊤
-- after {A = 𝟘} 𝟘 = 𝟘
-- after {A = ⊥} ⊥ = ⊥
-- after {A = 𝟙} 𝟙 = 𝟙
-- after {A = A ⨟ B} (seq ns tr) = after tr ⨟ B
-- after {A = A ⨟ B} (seqε sk tr) = after tr
-- after {A = A ⨟ B} (seq⊗ tr) = after tr
-- after {A = A ⨟ B} (seq⅋ tr) = after tr
-- after {A = A & B} &L = A
-- after {A = A & B} &R = B
-- after {A = A ⊕ B} ⊕L = A
-- after {A = A ⊕ B} ⊕R = B
-- after {A = A ⅋ B} ⅋L = A
-- after {A = A ⅋ B} ⅋R = B
-- after {A = A ⊗ B} ⊗L = A
-- after {A = A ⊗ B} ⊗R = B
-- after {A = _ ⊲ A} put = A
-- after {A = _ ⊳ A} get = A
-- after {A = rec A} (rec tr) = after tr

only-skip : ∀{n ℓ} {A B C : Type n} → A ⊨ ε ⇒ B → A ⊨ ℓ ⇒ C → ℓ ≡ ε
only-skip skip skip = refl
only-skip (seq x xns) _ = contradiction ε xns
only-skip (seqε sk x) (seq y yns) rewrite only-skip sk y = refl
only-skip (seqε _ x) (seqε _ y) = only-skip x y
only-skip (seqε sk x) (seq⊗ y) with only-skip sk y
... | ()
only-skip (seqε sk x) (seq⅋ y) with only-skip sk y
... | ()
only-skip (rec x) (rec y) = only-skip x y

deterministic : ∀{n ℓ} {A B C : Type n} → A ⊨ ℓ ⇒ B → A ⊨ ℓ ⇒ C → B ≡ C
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
deterministic (seq x xns) (seq y yns) = cong₂ _⨟_ (deterministic x y) refl
deterministic (seq x xns) (seqε sk y) rewrite only-skip sk x = contradiction ε xns
deterministic (seq x xns) (seq⊗ y) = contradiction ⊗L xns
deterministic (seq x xns) (seq⅋ y) = contradiction ⅋L xns
deterministic (seqε sk x) (seq y yns) rewrite only-skip sk y = contradiction ε yns
deterministic (seqε _ x) (seqε _ y) = deterministic x y
deterministic (seqε sk x) (seq⊗ y) with only-skip sk y
... | ()
deterministic (seqε sk x) (seq⅋ y) with only-skip sk y
... | ()
deterministic (seq⊗ x) (seq y yns) = contradiction ⊗L yns
deterministic (seq⊗ x) (seqε sk y) with only-skip sk x
... | ()
deterministic (seq⊗ x) (seq⊗ y) = deterministic x y
deterministic (seq⅋ x) (seq y yns) = contradiction ⅋L yns
deterministic (seq⅋ x) (seqε sk y) with only-skip sk x
... | ()
deterministic (seq⅋ x) (seq⅋ y) = deterministic x y
deterministic put put = refl
deterministic get get = refl
deterministic (rec x) (rec y) = deterministic x y

transition-dual : ∀{n ℓ} {A B : Type n} → A ⊨ ℓ ⇒ B → dual A ⊨ dual-label ℓ ⇒ dual B
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
transition-dual (seq x xns) = seq (transition-dual x) (contraposition dual-special xns)
transition-dual (seqε sk x) = seqε (transition-dual sk) (transition-dual x)
transition-dual (seq⊗ x) = seq⅋ (transition-dual x)
transition-dual (seq⅋ x) = seq⊗ (transition-dual x)
transition-dual put = get
transition-dual get = put
transition-dual {A = rec A} (rec x) = rec (transition-dual x)
