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

-- -- {-# BUILTIN REWRITE _~_ #-}
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
  rec  : ∀{A} → Skip A → Skip (rec A)

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
  -- rec  : ∀{A B ℓ} → A ⊨ ℓ ⇒ B → rec A ⊨ ℓ ⇒ subst [ rec A /] B
  rec  : ∀{A B ℓ} → subst [ rec A /] A ⊨ ℓ ⇒ B → rec A ⊨ ℓ ⇒ B

record _≲_ {r} (A B : PreType r) : Set where
  coinductive
  field
    ≲skip : Skip A → Skip B
    ≲cont : ∀{ℓ A'} → A ⊨ ℓ ⇒ A' → ∃[ B' ] (B ⊨ ℓ ⇒ B' × A' ≲ B')

open _≲_ public

≲refl : ∀{r} {A : PreType r} → A ≲ A
≲refl .≲skip sk = sk
≲refl .≲cont tr = _ , tr , ≲refl

≲trans : ∀{r} {A B C : PreType r} → A ≲ B → B ≲ C → A ≲ C
≲trans p q .≲skip sk = q .≲skip (p .≲skip sk)
≲trans p q .≲cont tr with p .≲cont tr
... | _ , tr' , p' with q .≲cont tr'
... | _ , tr'' , q' = _ , tr'' , ≲trans p' q'

skip-dual : ∀{r} {A : PreType r} → Skip A → Skip (dual A)
skip-dual skip = skip
skip-dual (seq sk sk') = seq (skip-dual sk) (skip-dual sk')
skip-dual (rec sk) = rec (skip-dual sk)

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

dual-transition : ∀{r} {A B : PreType r} {ℓ} → dual A ⊨ ℓ ⇒ B → A ⊨ dual-label ℓ ⇒ dual B
dual-transition = transition-dual

-- dual-transition {A = ⊤} 𝟘 = ⊤
-- dual-transition {A = 𝟘} ⊤ = 𝟘
-- dual-transition {A = ⊥} 𝟙 = ⊥
-- dual-transition {A = 𝟙} ⊥ = 𝟙
-- dual-transition {A = var x} rav = var
-- dual-transition {A = rav x} var = rav
-- dual-transition {A = x ⨟ x₁} (skip sk tr) = skip {!!} {!!}
-- dual-transition {A = x ⨟ x₁} (seq tr) = {!!}
-- dual-transition {A = x & x₁} ⊕L = {!!}
-- dual-transition {A = x & x₁} ⊕R = {!!}
-- dual-transition {A = x ⊕ x₁} &L = {!!}
-- dual-transition {A = x ⊕ x₁} &R = {!!}
-- dual-transition {A = x ⅋ x₁} tr = {!!}
-- dual-transition {A = x ⊗ x₁} tr = {!!}

-- inv-dual-dual : ∀{n} {A : PreType n 0} → A ≲ dual (dual A)
-- inv-dual-dual .≲skip sk = skip-dual (skip-dual sk)
-- inv-dual-dual .≲cont tr = _ , transition-dual (transition-dual tr) , inv-dual-dual

-- dual-dual-inv : ∀{n} {A : PreType n 0} → dual (dual A) ≲ A
-- dual-dual-inv .≲skip sk = dual-skip (dual-skip sk)
-- dual-dual-inv .≲cont tr = _ , dual-transition (dual-transition tr) , inv-dual-dual

-- -- record Complete {n} (A : PreType n) : Set where
-- --   coinductive
-- --   field
-- --     {ℓ}  : Label
-- --     {B}  : PreType n
-- --     tr   : A ⊨ ℓ ⇒ B
-- --     cont : ∀{ℓ B} → A ⊨ ℓ ⇒ B → Complete B

-- -- open Complete public

≲dual : ∀{n} {A B : PreType n} → A ≲ B → dual A ≲ dual B
≲dual le .≲skip sk = skip-dual (le .≲skip (skip-dual sk))
≲dual le .≲cont tr with le .≲cont (transition-dual tr)
... | _ , tr' , le' = _ , transition-dual tr' , ≲dual le'

-- -- transition-not-skip : ∀{n} {A B : PreType n} {ℓ} → A ⊨ ℓ ⇒ B → ¬ Skip A
-- -- transition-not-skip (skip _ tr) (seq _ sk) = transition-not-skip tr sk
-- -- transition-not-skip (seq tr) (seq sk _) = transition-not-skip tr sk
-- -- transition-not-skip (rec tr) (rec sk) = transition-not-skip tr {!!}

-- -- complete-not-skip : ∀{n} {A : PreType n} → Complete A → ¬ Skip A
-- -- complete-not-skip comp sk = transition-not-skip (comp .tr) sk

-- -- complete-absorbing : ∀{n} {A B : PreType n} → Complete A → A ~ (A ⨟ B)
-- -- complete-absorbing comp .skip-l sk = contradiction sk (transition-not-skip (comp .tr))
-- -- complete-absorbing comp .skip-r (seq sk _) = contradiction sk (complete-not-skip comp)
-- -- complete-absorbing comp .cont-l tr = _ , seq tr , complete-absorbing (comp .cont tr)
-- -- complete-absorbing comp .cont-r (skip sk _) = contradiction sk (complete-not-skip comp)
-- -- complete-absorbing comp .cont-r (seq tr) = _ , tr , complete-absorbing (comp .cont tr)

-- -- data Kind : Set where
-- --   S O : Kind

-- -- data _::_ {n} : PreType n → Kind → Set where
-- --   :skip : skip :: S
-- --   :⊥    : ⊥ :: O
-- --   :𝟙    : 𝟙 :: O
-- --   :⊤    : ⊤ :: O
-- --   :𝟘    : 𝟘 :: O
-- --   :var  : ∀{n} → var n :: O
-- --   :rav  : ∀{n} → rav n :: O
-- --   :&    : ∀{h k A B} → A :: h → B :: k → (A & B) :: O
-- --   :⊕    : ∀{h k A B} → A :: h → B :: k → (A ⊕ B) :: O
-- --   :⅋    : ∀{h k A B} → A :: h → B :: k → (A ⅋ B) :: O
-- --   :⊗    : ∀{h k A B} → A :: h → B :: k → (A ⊗ B) :: O
-- --   :seqo : ∀{k A B} → A :: O → B :: k → (A ⨟ B) :: O
-- --   :seqs : ∀{k A B} → A :: S → B :: k → (A ⨟ B) :: k
-- --   :rec  : ∀{A} → (subst [ rec A /] A) :: O → (rec A) :: O

-- -- Type : Set
-- -- Type = PreType 0

-- -- data HeadNormalForm : Type → Set where
-- --   hnf-skip : HeadNormalForm skip
-- --   hnf-⊥ : HeadNormalForm ⊥
-- --   hnf-𝟙 : HeadNormalForm 𝟙
-- --   hnf-⊤ : HeadNormalForm ⊤
-- --   hnf-𝟘 : HeadNormalForm 𝟘
-- --   hnf-var : ∀{x} → HeadNormalForm (var x)
-- --   hnf-rav : ∀{x} → HeadNormalForm (rav x)
-- --   hnf-&   : ∀{A B} → HeadNormalForm (A & B)
-- --   hnf-⊕   : ∀{A B} → HeadNormalForm (A ⊕ B)
-- --   hnf-⅋   : ∀{A B} → HeadNormalForm (A ⅋ B)
-- --   hnf-⊗   : ∀{A B} → HeadNormalForm (A ⊗ B)

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

-- -- nf : ∀{A κ} → A :: κ → ∃[ B ] HeadNormalForm B × A ≤ B
-- -- nf :skip = _ , hnf-skip , ≤-refl
-- -- nf :⊥ = _ , hnf-⊥ , ≤-refl
-- -- nf :𝟙 = _ , hnf-𝟙 , ≤-refl
-- -- nf :⊤ = _ , hnf-⊤ , ≤-refl
-- -- nf :𝟘 = _ , hnf-𝟘 , ≤-refl
-- -- nf (:& x y) = _ , hnf-& , ≤-refl
-- -- nf (:⊕ x y) = _ , hnf-⊕ , ≤-refl
-- -- nf (:⅋ x y) = _ , hnf-⅋ , ≤-refl
-- -- nf (:⊗ x y) = _ , hnf-⊗ , ≤-refl
-- -- nf (:seqo x y) = {!!}
-- -- nf (:seqs x y) = {!!}
-- -- nf (:rec x) = {!!}

-- -- lemma-rec : ∀{A B} → (subst [ skip /] A ⨟ B) ≤ subst [ B /] A
-- -- lemma-rec {A} = {!!}
