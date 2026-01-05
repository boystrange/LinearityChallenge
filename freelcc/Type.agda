{-# OPTIONS --rewriting --guardedness #-}
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym)
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
rename ρ (A ⨟ B) = rename ρ (A) ⨟ rename ρ (B)
rename ρ (A & B) = rename ρ (A) & rename ρ (B)
rename ρ (A ⊕ B) = rename ρ (A) ⊕ rename ρ (B)
rename ρ (A ⅋ B) = rename ρ (A) ⅋ rename ρ (B)
rename ρ (A ⊗ B) = rename ρ (A) ⊗ rename ρ (B)
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

[_/] : ∀{r} → PreType r → Fin (suc r) → PreType r
[ A /] zero     = A
[ A /] (suc x)  = inv x

unfold : ∀{r} → PreType (suc r) → PreType r
unfold A = subst [ rec A /] A

postulate
  extensionality : ∀{A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g

dual-rename : ∀{r s} {ρ : Fin r → Fin s} (A : PreType r) → dual (rename ρ A) ≡ rename ρ (dual A)
dual-rename skip = refl
dual-rename ⊤ = refl
dual-rename 𝟘 = refl
dual-rename ⊥ = refl
dual-rename 𝟙 = refl
dual-rename (A ⨟ B) = cong₂ _⨟_ (dual-rename A) (dual-rename B)
dual-rename (A & B) = cong₂ _⊕_ (dual-rename A) (dual-rename B)
dual-rename (A ⊕ B) = cong₂ _&_ (dual-rename A) (dual-rename B)
dual-rename (A ⅋ B) = cong₂ _⊗_ (dual-rename A) (dual-rename B)
dual-rename (A ⊗ B) = cong₂ _⅋_ (dual-rename A) (dual-rename B)
dual-rename (inv x) = refl
dual-rename (rec A) = cong rec (dual-rename A)

exts-dual : ∀{r s} {σ : Fin r → PreType s} (x : Fin (suc r)) → exts (dual ∘ σ) x ≡ dual ((exts σ) x)
exts-dual zero = refl
exts-dual {σ = σ} (suc x) rewrite dual-rename {ρ = suc} (σ x) = refl

dual-subst : ∀{r s} (σ : Fin r → PreType s) (A : PreType r) → dual (subst σ A) ≡ subst (dual ∘ σ) (dual A)
dual-subst {_} {_} σ skip = refl
dual-subst {_} {_} σ ⊤ = refl
dual-subst {_} {_} σ 𝟘 = refl
dual-subst {_} {_} σ ⊥ = refl
dual-subst {_} {_} σ 𝟙 = refl
dual-subst {_} {_} σ (A ⨟ B) = cong₂ _⨟_ (dual-subst σ A) (dual-subst σ B)
dual-subst {_} {_} σ (A & B) = cong₂ _⊕_ (dual-subst σ A) (dual-subst σ B)
dual-subst {_} {_} σ (A ⊕ B) = cong₂ _&_ (dual-subst σ A) (dual-subst σ B)
dual-subst {_} {_} σ (A ⅋ B) = cong₂ _⊗_ (dual-subst σ A) (dual-subst σ B)
dual-subst {_} {_} σ (A ⊗ B) = cong₂ _⅋_ (dual-subst σ A) (dual-subst σ B)
dual-subst {_} {_} σ (inv zero) = refl
dual-subst {_} {_} σ (inv (suc x)) = refl
dual-subst {_} {_} σ (rec A) rewrite extensionality {f = exts (dual ∘ σ)} {dual ∘ (exts σ)} exts-dual
  = cong rec (dual-subst (exts σ) A)

-- {-# REWRITE dual-subst #-}

data Skip {r} : PreType r → Set where
  skip : Skip skip
  seq  : ∀{A B} → Skip A → Skip B → Skip (A ⨟ B)
  rec  : ∀{A} → Skip (unfold A) → Skip (rec A)

data Label : Set where
  ⊥ 𝟙 ⊤ 𝟘 &L &R ⊕L ⊕R ⅋L ⅋R ⊗L ⊗R : Label
  -- var rav : ∀{n} → Fin n → Label

dual-label : Label → Label
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

data _⊨_⇒_ {r} : PreType r → Label → PreType r → Set where
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
  skip : ∀{A B C ℓ} → Skip (A) → B ⊨ ℓ ⇒ C → (A ⨟ B) ⊨ ℓ ⇒ C
  seq  : ∀{A B C ℓ} → A ⊨ ℓ ⇒ B → (A ⨟ C) ⊨ ℓ ⇒ (B ⨟ C)
  rec  : ∀{A B ℓ} → unfold A ⊨ ℓ ⇒ B → rec A ⊨ ℓ ⇒ B

record _≲_ {r} (A B : PreType r) : Set where
  coinductive
  field
    ≲skip : Skip A → Skip B
    ≲cont : ∀{ℓ A'} → A ⊨ ℓ ⇒ A' → ∃[ B' ] (B ⊨ ℓ ⇒ B' × A' ≲ B')

open _≲_ public

record _≅_ {r} (A B : PreType r) : Set where
  field
    to : A ≲ B
    from : B ≲ A

open _≅_ public

≲refl : ∀{r} {A : PreType r} → A ≲ A
≲refl .≲skip sk = sk
≲refl .≲cont tr = _ , tr , ≲refl

≲trans : ∀{r} {A B C : PreType r} → A ≲ B → B ≲ C → A ≲ C
≲trans p q .≲skip sk = q .≲skip (p .≲skip sk)
≲trans p q .≲cont tr with p .≲cont tr
... | _ , tr' , p' with q .≲cont tr'
... | _ , tr'' , q' = _ , tr'' , ≲trans p' q'

≲unfold : ∀{r} {A : PreType (suc r)} → rec A ≲ unfold A
≲unfold .≲skip (rec sk) = sk
≲unfold .≲cont (rec tr) = _ , tr , ≲refl

≅refl : ∀{r} {A : PreType r} → A ≅ A
≅refl .to = ≲refl
≅refl .from = ≲refl

≅sym : ∀{r} {A B : PreType r} → A ≅ B → B ≅ A
≅sym p .to = p .from
≅sym p .from = p .to

≅trans : ∀{r} {A B C : PreType r} → A ≅ B → B ≅ C → A ≅ C
≅trans p q .to = ≲trans (p .to) (q .to)
≅trans p q .from = ≲trans (q .from) (p .from)

skip-dual : ∀{r} {A : PreType r} → Skip A → Skip (dual A)
skip-dual skip = skip
skip-dual (seq sk sk') = seq (skip-dual sk) (skip-dual sk')
skip-dual (rec sk) = rec (skip-dual {!!})

lemma'' : ∀{r} {A : PreType r} → [ dual A /] ≡ dual ∘ [ A /]
lemma'' = extensionality aux
  where
    aux : ∀{r} {A : PreType r} (x : Fin (suc r)) → [ dual A /] x ≡ (dual ∘ [ A /]) x
    aux zero = refl
    aux (suc x) = refl

transition-dual : ∀{r} {A B : PreType r} {ℓ} → A ⊨ ℓ ⇒ B → dual A ⊨ dual-label ℓ ⇒ dual B
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
transition-dual (skip sk tr) = skip (skip-dual sk) (transition-dual tr)
transition-dual (seq tr) = seq (transition-dual tr)
transition-dual {A = rec A} {B} (rec {B = C} tr) with transition-dual tr
... | tr' rewrite dual-subst [ rec A /] A | sym (lemma'' {_} {rec A}) = rec tr'

record Complete {r} (A : PreType r) : Set where
  coinductive
  field
    {ℓ}           : Label
    {B}           : PreType r
    complete-tr   : A ⊨ ℓ ⇒ B
    complete-cont : ∀{ℓ B} → A ⊨ ℓ ⇒ B → Complete B

open Complete public

≲dual : ∀{n} {A B : PreType n} → A ≲ B → dual A ≲ dual B
≲dual le .≲skip sk = skip-dual (le .≲skip (skip-dual sk))
≲dual le .≲cont tr with le .≲cont (transition-dual tr)
... | _ , tr' , le' = _ , transition-dual tr' , ≲dual le'

skip-subst : ∀{r s} {A : PreType r} {σ : Fin r → PreType s}→ Skip A → Skip (subst σ A)
skip-subst skip = skip
skip-subst (seq sk sk') = seq (skip-subst sk) (skip-subst sk')
skip-subst (rec sk) = rec {!!}

transition-not-skip : ∀{n} {A B : PreType n} {ℓ} → A ⊨ ℓ ⇒ B → ¬ Skip A
transition-not-skip (skip _ tr) (seq _ sk) = transition-not-skip tr sk
transition-not-skip (seq tr) (seq sk _) = transition-not-skip tr sk
transition-not-skip (rec tr) (rec sk) = transition-not-skip tr {!!}

complete-not-skip : ∀{n} {A : PreType n} → Complete A → ¬ Skip A
complete-not-skip comp sk = transition-not-skip (comp .complete-tr) sk

complete-absorbing-r : ∀{n} {A B : PreType n} → Complete A → A ≲ (A ⨟ B)
complete-absorbing-r comp .≲skip sk = contradiction sk (transition-not-skip (comp .complete-tr))
complete-absorbing-r comp .≲cont tr = _ , seq tr , complete-absorbing-r (comp .complete-cont tr)

complete-absorbing-l : ∀{r} {A B : PreType r} → Complete A → (A ⨟ B) ≲ A
complete-absorbing-l comp .≲skip (seq sk _) = sk
complete-absorbing-l comp .≲cont (skip sk _) = contradiction sk (complete-not-skip comp)
complete-absorbing-l comp .≲cont (seq tr) = _ , tr , complete-absorbing-l (comp .complete-cont tr)

complete-absorbing : ∀{r} {A B : PreType r} → Complete A → A ≅ (A ⨟ B)
complete-absorbing comp .to = complete-absorbing-r comp
complete-absorbing comp .from = complete-absorbing-l comp

Type : Set
Type = PreType 0

-- -- infix  1 ≤begin_
-- -- infixr 2 _≤⟨⟩_ _≤⟨_⟩_
-- -- infix  3 _≤∎

-- -- ≤begin_ : {x y : Type} -> x ≤ y -> x ≤ y
-- -- ≤begin_ p = p

-- -- _≤∎ : (x : Type) -> x ≤ x
-- -- _≤∎ _ = ≤-refl

-- -- _≤⟨_⟩_ : (x : Type) {y z : Type} -> x ≤ y -> y ≤ z -> x ≤ z
-- -- _≤⟨_⟩_ _ = ≤-tran

-- -- lemma-skip : ∀{A} → A :: S → A ≤ skip
-- -- lemma-skip :skip = ≤-refl
-- -- lemma-skip {A ⨟ B} (:seqs x y) = ≤begin
-- --   (A ⨟ B) ≤⟨ ≤-cong (lemma-skip x) (lemma-skip y) ⟩
-- --   (skip ⨟ skip) ≤⟨ ≤-skip ⟩
-- --   skip ≤∎

-- -- lemma-rec : ∀{A B} → (subst [ skip /] A ⨟ B) ≤ subst [ B /] A
-- -- lemma-rec {A} = {!!}
