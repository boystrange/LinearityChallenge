{-# OPTIONS --rewriting --guardedness #-}
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Agda.Builtin.Equality.Rewrite

data PreType : ℕ → Set where
  skip ⊤ 𝟘 ⊥ 𝟙         : ∀{r} → PreType r
  -- var rav              : ∀{r} → Fin n → PreType r
  _⨟_ _&_ _⊕_ _⅋_ _⊗_  : ∀{r} → PreType r → PreType r → PreType r
  inv                  : ∀{r} → Fin r → PreType r
  rec                  : ∀{r} → PreType (suc r) → PreType r

dual : ∀{r} → PreType r → PreType r
dual skip    = skip
dual ⊤       = 𝟘
dual 𝟘       = ⊤
dual ⊥       = 𝟙
dual 𝟙       = ⊥
-- dual (var x) = rav x
-- dual (rav x) = var x
dual (A ⨟ B) = dual (A) ⨟ dual (B)
dual (A & B) = dual (A) ⊕ dual (B)
dual (A ⊕ B) = dual (A) & dual (B)
dual (A ⅋ B) = dual (A) ⊗ dual (B)
dual (A ⊗ B) = dual (A) ⅋ dual (B)
dual (inv x) = inv x
dual (rec A) = rec (dual A)

dual-inv : ∀{r} {A : PreType r} → dual (dual A) ≡ A
dual-inv {_} {skip} = refl
dual-inv {_} {⊤} = refl
dual-inv {_} {𝟘} = refl
dual-inv {_} {⊥} = refl
dual-inv {_} {𝟙} = refl
dual-inv {_} {A ⨟ B} = cong₂ _⨟_ dual-inv dual-inv
dual-inv {_} {A & B} = cong₂ _&_ dual-inv dual-inv
dual-inv {_} {A ⊕ B} = cong₂ _⊕_ dual-inv dual-inv
dual-inv {_} {A ⅋ B} = cong₂ _⅋_ dual-inv dual-inv
dual-inv {_} {A ⊗ B} = cong₂ _⊗_ dual-inv dual-inv
dual-inv {_} {inv x} = refl
dual-inv {_} {rec A} = cong rec dual-inv

{-# REWRITE dual-inv #-}

ext : ∀{m n} → (Fin m → Fin n) → Fin (suc m) → Fin (suc n)
ext ρ zero = zero
ext ρ (suc k) = suc (ρ k)

rename : ∀{r s} → (Fin r → Fin s) → PreType r → PreType s
rename ρ skip = skip
rename ρ ⊤    = ⊤
rename ρ 𝟘    = 𝟘
rename ρ ⊥ = ⊥
rename ρ 𝟙 = 𝟙
-- rename ρ (var x) = var (ρ x)
-- rename ρ (rav x) = rav (ρ x)
rename ρ (A ⨟ B) = rename ρ A ⨟ rename ρ B
rename ρ (A & B) = rename ρ A & rename ρ B
rename ρ (A ⊕ B) = rename ρ A ⊕ rename ρ B
rename ρ (A ⅋ B) = rename ρ A ⅋ rename ρ B
rename ρ (A ⊗ B) = rename ρ A ⊗ rename ρ B
rename ρ (inv x) = inv (ρ x)
rename ρ (rec A) = rec (rename (ext ρ) A)

exts : ∀{r s} → (Fin r → PreType s) → Fin (suc r) → PreType (suc s)
exts σ zero = inv zero
exts σ (suc k) = rename suc (σ k)

subst : ∀{r s} → (Fin r → PreType s) → PreType r → PreType s
subst σ skip = skip
subst σ ⊤ = ⊤
subst σ 𝟘 = 𝟘
subst σ ⊥ = ⊥
subst σ 𝟙 = 𝟙
-- subst σ (var x) = var x
-- subst σ (rav x) = rav x
subst σ (A ⨟ B) = subst σ (A) ⨟ subst σ (B)
subst σ (A & B) = subst σ (A) & subst σ (B)
subst σ (A ⊕ B) = subst σ (A) ⊕ subst σ (B)
subst σ (A ⅋ B) = subst σ (A) ⅋ subst σ (B)
subst σ (A ⊗ B) = subst σ (A) ⊗ subst σ (B)
subst σ (inv x) = σ x
subst σ (rec A) = rec (subst (exts σ) A)

-- -- subst-compose : ∀{m n o} → (Fin m → PreType n) → (Fin n → PreType o) → Fin m → PreType o
-- -- subst-compose σ τ x = subst τ (σ x)

s-just : ∀{r} → PreType r → Fin (suc r) → PreType r
s-just A zero     = A
s-just A (suc x)  = inv x

unfold : ∀{r} → PreType (suc r) → PreType r
unfold A = subst (s-just (rec A)) A

postulate
  extensionality : ∀{A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g

dual-rename : ∀{r s} (ρ : Fin r → Fin s) (A : PreType r) → dual (rename ρ A) ≡ rename ρ (dual A)
dual-rename ρ skip = refl
dual-rename ρ ⊤ = refl
dual-rename ρ 𝟘 = refl
dual-rename ρ ⊥ = refl
dual-rename ρ 𝟙 = refl
dual-rename ρ (A ⨟ B) = cong₂ _⨟_ (dual-rename ρ A) (dual-rename ρ B)
dual-rename ρ (A & B) = cong₂ _⊕_ (dual-rename ρ A) (dual-rename ρ B)
dual-rename ρ (A ⊕ B) = cong₂ _&_ (dual-rename ρ A) (dual-rename ρ B)
dual-rename ρ (A ⅋ B) = cong₂ _⊗_ (dual-rename ρ A) (dual-rename ρ B)
dual-rename ρ (A ⊗ B) = cong₂ _⅋_ (dual-rename ρ A) (dual-rename ρ B)
dual-rename ρ (inv x) = refl
dual-rename ρ (rec A) = cong rec (dual-rename (ext ρ) A)

exts-dual : ∀{r s} (σ : Fin r → PreType s) → exts (dual ∘ σ) ≡ dual ∘ (exts σ)
exts-dual {r} σ = extensionality aux
  where
    aux : (x : Fin (suc r)) → exts (dual ∘ σ) x ≡ dual ((exts σ) x)
    aux zero = refl
    aux (suc x) rewrite dual-rename suc (σ x) = refl

dual-subst : ∀{r s} (σ : Fin r → PreType s) (A : PreType r) → dual (subst σ A) ≡ subst (dual ∘ σ) (dual A)
dual-subst σ skip = refl
dual-subst σ ⊤ = refl
dual-subst σ 𝟘 = refl
dual-subst σ ⊥ = refl
dual-subst σ 𝟙 = refl
dual-subst σ (A ⨟ B) = cong₂ _⨟_ (dual-subst σ A) (dual-subst σ B)
dual-subst σ (A & B) = cong₂ _⊕_ (dual-subst σ A) (dual-subst σ B)
dual-subst σ (A ⊕ B) = cong₂ _&_ (dual-subst σ A) (dual-subst σ B)
dual-subst σ (A ⅋ B) = cong₂ _⊗_ (dual-subst σ A) (dual-subst σ B)
dual-subst σ (A ⊗ B) = cong₂ _⅋_ (dual-subst σ A) (dual-subst σ B)
dual-subst σ (inv zero) = refl
dual-subst σ (inv (suc x)) = refl
dual-subst σ (rec A) rewrite exts-dual σ = cong rec (dual-subst (exts σ) A)

-- {-# REWRITE dual-subst #-}

data Label : Set where
  ε ⊥ 𝟙 ⊤ 𝟘 &L &R ⊕L ⊕R ⅋L ⅋R ⊗L ⊗R : Label
  -- var rav : ∀{n} → Fin n → Label

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
-- dual-label (var x) = rav x
-- dual-label (rav x) = var x

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
-- dual-label-inv {var x} = refl
-- dual-label-inv {rav x} = refl

{-# REWRITE dual-label-inv #-}

dual-label-not-skip : ∀{ℓ} → ℓ ≢ ε → dual-label ℓ ≢ ε
dual-label-not-skip neq eq = contradiction (cong dual-label eq) neq

data _⊨_⇒_ {r} : PreType r → Label → PreType r → Set where
  skip : skip ⊨ ε ⇒ skip
  ⊥    : ⊥ ⊨ ⊥ ⇒ ⊥
  𝟙    : 𝟙 ⊨ 𝟙 ⇒ 𝟙
  ⊤    : ⊤ ⊨ ⊤ ⇒ ⊤
  𝟘    : 𝟘 ⊨ 𝟘 ⇒ 𝟘
  -- var  : ∀{x} → var x ⊨ var x ⇒ var x
  -- rav  : ∀{x} → rav x ⊨ rav x ⇒ rav x
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

only-skip : ∀{r ℓ} {A B C : PreType r} → A ⊨ ℓ ⇒ B → A ⊨ ε ⇒ C → ℓ ≡ ε
only-skip skip skip = refl
only-skip (seql _ _) (seql _ ne) = contradiction refl ne
only-skip (seqr _ _) (seql _ ne) = contradiction refl ne
only-skip (seql x ne) (seqr y _) = contradiction (only-skip x y) ne
only-skip (seqr _ x) (seqr _ y) = only-skip x y
only-skip (rec x) (rec y) = only-skip x y

deterministic : ∀{r ℓ} {A B C : PreType r} → A ⊨ ℓ ⇒ B → A ⊨ ℓ ⇒ C → B ≡ C
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
deterministic (seql x _) (seql y _) = cong₂ _⨟_ (deterministic x y) refl
deterministic (seql x ne) (seqr y _) = contradiction (only-skip x y) ne
deterministic (seqr x _) (seql y ne) = contradiction (only-skip y x) ne
deterministic (seqr _ x) (seqr _ y) = deterministic x y
deterministic (rec x) (rec y) = deterministic x y

dual-s-just : ∀{r} (A : PreType r) → dual ∘ s-just A ≡ s-just (dual A)
dual-s-just {r} A = extensionality aux
  where
    aux : (x : Fin (suc r)) → (dual ∘ s-just A) x ≡ s-just (dual A) x
    aux zero = refl
    aux (suc x) = refl

transition-dual : ∀{r} {A B : PreType r} {ℓ} → A ⊨ ℓ ⇒ B → dual A ⊨ dual-label ℓ ⇒ dual B
transition-dual skip = skip
transition-dual ⊥ = 𝟙
transition-dual 𝟙 = ⊥
transition-dual ⊤ = 𝟘
transition-dual 𝟘 = ⊤
-- transition-dual var = rav
-- transition-dual rav = var
transition-dual &L = ⊕L
transition-dual &R = ⊕R
transition-dual ⊕L = &L
transition-dual ⊕R = &R
transition-dual ⅋L = ⊗L
transition-dual ⅋R = ⊗R
transition-dual ⊗L = ⅋L
transition-dual ⊗R = ⅋R
transition-dual (seqr tr tr') = seqr (transition-dual tr) (transition-dual tr')
transition-dual (seql tr neq) = seql (transition-dual tr) (dual-label-not-skip neq)
transition-dual {A = rec A} (rec tr) with transition-dual tr
... | tr' rewrite dual-subst (s-just (rec A)) A | dual-s-just (rec A) = rec tr'

record Closed {r} (A : PreType r) : Set where
  coinductive
  field
    closed-skip : ∀{ℓ B} → A ⊨ ℓ ⇒ B → ℓ ≢ ε
    closed-cont : ∀{ℓ B} → A ⊨ ℓ ⇒ B → Closed B

open Closed public

Type : Set
Type = PreType 0
