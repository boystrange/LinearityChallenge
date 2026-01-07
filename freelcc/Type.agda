{-# OPTIONS --rewriting --guardedness #-}
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Agda.Builtin.Equality.Rewrite

postulate
  extensionality : ∀{A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g

data PreType (n : ℕ) : ℕ → Set where
  var rav              : ∀{r} → Fin n → PreType n r
  skip ⊤ 𝟘 ⊥ 𝟙         : ∀{r} → PreType n r
  _⨟_ _&_ _⊕_ _⅋_ _⊗_  : ∀{r} → PreType n r → PreType n r → PreType n r
  inv                  : ∀{r} → Fin r → PreType n r
  rec                  : ∀{r} → PreType n (suc r) → PreType n r

dual : ∀{n r} → PreType n r → PreType n r
dual (var x) = rav x
dual (rav x) = var x
dual ⊤       = 𝟘
dual 𝟘       = ⊤
dual ⊥       = 𝟙
dual 𝟙       = ⊥
dual (A & B) = dual A ⊕ dual B
dual (A ⊕ B) = dual A & dual B
dual (A ⅋ B) = dual A ⊗ dual B
dual (A ⊗ B) = dual A ⅋ dual B
dual skip    = skip
dual (A ⨟ B) = dual A ⨟ dual B
dual (inv x) = inv x
dual (rec A) = rec (dual A)

dual-inv : ∀{n r} {A : PreType n r} → dual (dual A) ≡ A
dual-inv {_} {_} {var x} = refl
dual-inv {_} {_} {rav x} = refl
dual-inv {_} {_} {skip} = refl
dual-inv {_} {_} {⊤} = refl
dual-inv {_} {_} {𝟘} = refl
dual-inv {_} {_} {⊥} = refl
dual-inv {_} {_} {𝟙} = refl
dual-inv {_} {_} {A ⨟ B} = cong₂ _⨟_ dual-inv dual-inv
dual-inv {_} {_} {A & B} = cong₂ _&_ dual-inv dual-inv
dual-inv {_} {_} {A ⊕ B} = cong₂ _⊕_ dual-inv dual-inv
dual-inv {_} {_} {A ⅋ B} = cong₂ _⅋_ dual-inv dual-inv
dual-inv {_} {_} {A ⊗ B} = cong₂ _⊗_ dual-inv dual-inv
dual-inv {_} {_} {inv x} = refl
dual-inv {_} {_} {rec A} = cong rec dual-inv

{-# REWRITE dual-inv #-}

ext : ∀{m n} → (Fin m → Fin n) → Fin (suc m) → Fin (suc n)
ext ρ zero = zero
ext ρ (suc k) = suc (ρ k)

rename : ∀{n r s} → (Fin r → Fin s) → PreType n r → PreType n s
rename ρ (var x) = var x
rename ρ (rav x) = rav x
rename ρ skip = skip
rename ρ ⊤    = ⊤
rename ρ 𝟘    = 𝟘
rename ρ ⊥ = ⊥
rename ρ 𝟙 = 𝟙
rename ρ (A ⨟ B) = rename ρ A ⨟ rename ρ B
rename ρ (A & B) = rename ρ A & rename ρ B
rename ρ (A ⊕ B) = rename ρ A ⊕ rename ρ B
rename ρ (A ⅋ B) = rename ρ A ⅋ rename ρ B
rename ρ (A ⊗ B) = rename ρ A ⊗ rename ρ B
rename ρ (inv x) = inv (ρ x)
rename ρ (rec A) = rec (rename (ext ρ) A)

dual-rename : ∀{n r s} (ρ : Fin r → Fin s) (A : PreType n r) → dual (rename ρ A) ≡ rename ρ (dual A)
dual-rename ρ (var x) = refl
dual-rename ρ (rav x) = refl
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

exts : ∀{n r s} → (Fin r → PreType n s) → Fin (suc r) → PreType n (suc s)
exts σ zero = inv zero
exts σ (suc k) = rename suc (σ k)

pexts : ∀{n m r} → (Fin n → PreType m r) → Fin n → PreType m (suc r)
pexts σ = rename suc ∘ σ

dual-exts : ∀{n r s} (σ : Fin r → PreType n s) → exts (dual ∘ σ) ≡ dual ∘ (exts σ)
dual-exts {_} {r} σ = extensionality aux
  where
    aux : (x : Fin (suc r)) → exts (dual ∘ σ) x ≡ dual ((exts σ) x)
    aux zero = refl
    aux (suc x) rewrite dual-rename suc (σ x) = refl

subst : ∀{n m r} → (∀{s} → Fin n → PreType m s) → ∀{s} → (Fin r → PreType m s) → PreType n r → PreType m s
subst σ τ (var x) = σ x
subst σ τ (rav x) = dual (σ x)
subst σ τ skip = skip
subst σ τ ⊤ = ⊤
subst σ τ 𝟘 = 𝟘
subst σ τ ⊥ = ⊥
subst σ τ 𝟙 = 𝟙
subst σ τ (A ⨟ B) = subst σ τ A ⨟ subst σ τ B
subst σ τ (A & B) = subst σ τ A & subst σ τ B
subst σ τ (A ⊕ B) = subst σ τ A ⊕ subst σ τ B
subst σ τ (A ⅋ B) = subst σ τ A ⅋ subst σ τ B
subst σ τ (A ⊗ B) = subst σ τ A ⊗ subst σ τ B
subst σ τ (inv x) = τ x
subst σ τ (rec A) = rec (subst σ (exts τ) A)

dual-subst : ∀{n m r s} (σ : ∀{s} → Fin n → PreType m s) (τ : Fin r → PreType m s) (A : PreType n r) →
             dual (subst σ τ A) ≡ subst σ (dual ∘ τ) (dual A)
dual-subst σ τ (var x) = refl
dual-subst σ τ (rav x) = refl
dual-subst σ τ skip = refl
dual-subst σ τ ⊤ = refl
dual-subst σ τ 𝟘 = refl
dual-subst σ τ ⊥ = refl
dual-subst σ τ 𝟙 = refl
dual-subst σ τ (A ⨟ B) = cong₂ _⨟_ (dual-subst σ τ A) (dual-subst σ τ B)
dual-subst σ τ (A & B) = cong₂ _⊕_ (dual-subst σ τ A) (dual-subst σ τ B)
dual-subst σ τ (A ⊕ B) = cong₂ _&_ (dual-subst σ τ A) (dual-subst σ τ B)
dual-subst σ τ (A ⅋ B) = cong₂ _⊗_ (dual-subst σ τ A) (dual-subst σ τ B)
dual-subst σ τ (A ⊗ B) = cong₂ _⅋_ (dual-subst σ τ A) (dual-subst σ τ B)
dual-subst σ τ (inv x) = refl
dual-subst σ τ (rec A) rewrite dual-exts τ = cong rec (dual-subst σ (exts τ) A)

-- {-# REWRITE dual-subst #-}

s-just : ∀{n r} → PreType n r → Fin (suc r) → PreType n r
s-just A zero     = A
s-just A (suc x)  = inv x

dual-s-just : ∀{n r} (A : PreType n r) → dual ∘ s-just A ≡ s-just (dual A)
dual-s-just {_} {r} A = extensionality aux
  where
    aux : (x : Fin (suc r)) → (dual ∘ s-just A) x ≡ s-just (dual A) x
    aux zero = refl
    aux (suc x) = refl

unfold : ∀{n r} → PreType n (suc r) → PreType n r
unfold A = subst var (s-just (rec A)) A

dual-unfold : ∀{n r} (A : PreType n (suc r)) → dual (unfold A) ≡ unfold (dual A)
dual-unfold A rewrite dual-subst var (s-just (rec A)) A | dual-s-just (rec A) = refl

Type : ℕ → Set
Type n = PreType n 0

exts-inv : ∀{n r} → exts {n} {r} inv ≡ inv
exts-inv {n} {r} = extensionality aux
  where
    aux : (x : Fin (suc r)) → exts {n} inv x ≡ inv x
    aux zero = refl
    aux (suc x) = refl

subst-compose : ∀{m n o r}
                (σ₁ : ∀{u} → Fin m → PreType n u) (σ₂ : ∀{u} → Fin n → PreType o u) →
                (A : PreType m r) →
                subst σ₂ inv (subst σ₁ inv A) ≡ subst (subst σ₂ inv ∘ σ₁) inv A
subst-compose σ₁ σ₂ (var x) = refl
subst-compose σ₁ σ₂ (rav x) = sym (dual-subst σ₂ inv (σ₁ x))
subst-compose σ₁ σ₂ skip = refl
subst-compose σ₁ σ₂ ⊤ = refl
subst-compose σ₁ σ₂ 𝟘 = refl
subst-compose σ₁ σ₂ ⊥ = refl
subst-compose σ₁ σ₂ 𝟙 = refl
subst-compose σ₁ σ₂ (A ⨟ B) = cong₂ _⨟_ (subst-compose σ₁ σ₂ A) (subst-compose σ₁ σ₂ B)
subst-compose σ₁ σ₂ (A & B) = cong₂ _&_ (subst-compose σ₁ σ₂ A) (subst-compose σ₁ σ₂ B)
subst-compose σ₁ σ₂ (A ⊕ B) = cong₂ _⊕_ (subst-compose σ₁ σ₂ A) (subst-compose σ₁ σ₂ B)
subst-compose σ₁ σ₂ (A ⅋ B) = cong₂ _⅋_ (subst-compose σ₁ σ₂ A) (subst-compose σ₁ σ₂ B)
subst-compose σ₁ σ₂ (A ⊗ B) = cong₂ _⊗_ (subst-compose σ₁ σ₂ A) (subst-compose σ₁ σ₂ B)
subst-compose σ₁ σ₂ (inv x) = refl
subst-compose {m} {n} {o} {r} σ₁ σ₂ (rec A)
  rewrite exts-inv {n} {r} | exts-inv {o} {r} =
  cong rec (subst-compose σ₁ σ₂ A)
