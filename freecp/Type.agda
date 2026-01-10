{-# OPTIONS --rewriting --guardedness #-}
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym)
open import Agda.Builtin.Equality.Rewrite

open import Axioms

data PreType (n : ℕ) : ℕ → Set where
  var rav              : ∀{r} → Fin n → PreType n r
  skip ⊤ 𝟘 ⊥ 𝟙         : ∀{r} → PreType n r
  _⨟_ _&_ _⊕_ _⅋_ _⊗_  : ∀{r} → PreType n r → PreType n r → PreType n r
  _⊲_ _⊳_              : ∀{r} → ℕ → PreType n r → PreType n r
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
dual (μ ⊲ A) = μ ⊳ dual A
dual (μ ⊳ A) = μ ⊲ dual A
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
dual-inv {_} {_} {μ ⊲ A} = cong (μ ⊲_) dual-inv
dual-inv {_} {_} {μ ⊳ A} = cong (μ ⊳_) dual-inv
dual-inv {_} {_} {inv x} = refl
dual-inv {_} {_} {rec A} = cong rec dual-inv

{-# REWRITE dual-inv #-}

-- RECURSIVE TYPES

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
rename ρ (μ ⊲ A) = μ ⊲ rename ρ A
rename ρ (μ ⊳ A) = μ ⊳ rename ρ A
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
dual-rename ρ (μ ⊲ A) = cong (μ ⊳_) (dual-rename ρ A)
dual-rename ρ (μ ⊳ A) = cong (μ ⊲_) (dual-rename ρ A)
dual-rename ρ (inv x) = refl
dual-rename ρ (rec A) = cong rec (dual-rename (ext ρ) A)

exts : ∀{n r s} → (Fin r → PreType n s) → Fin (suc r) → PreType n (suc s)
exts σ zero = inv zero
exts σ (suc k) = rename suc (σ k)

dual-exts : ∀{n r s} (σ : Fin r → PreType n s) → exts (dual ∘ σ) ≡ dual ∘ (exts σ)
dual-exts {_} {r} σ = extensionality aux
  where
    aux : (x : Fin (suc r)) → exts (dual ∘ σ) x ≡ dual ((exts σ) x)
    aux zero = refl
    aux (suc x) rewrite dual-rename suc (σ x) = refl

rec-subst : ∀{n r s} → (Fin r → PreType n s) → PreType n r → PreType n s
rec-subst σ (var x) = var x
rec-subst σ (rav x) = rav x
rec-subst σ skip = skip
rec-subst σ ⊤ = ⊤
rec-subst σ 𝟘 = 𝟘
rec-subst σ ⊥ = ⊥
rec-subst σ 𝟙 = 𝟙
rec-subst σ (A ⨟ B) = rec-subst σ A ⨟ rec-subst σ B
rec-subst σ (A & B) = rec-subst σ A & rec-subst σ B
rec-subst σ (A ⊕ B) = rec-subst σ A ⊕ rec-subst σ B
rec-subst σ (A ⅋ B) = rec-subst σ A ⅋ rec-subst σ B
rec-subst σ (A ⊗ B) = rec-subst σ A ⊗ rec-subst σ B
rec-subst σ (μ ⊲ A) = μ ⊲ rec-subst σ A
rec-subst σ (μ ⊳ A) = μ ⊳ rec-subst σ A
rec-subst σ (inv x) = σ x
rec-subst σ (rec A) = rec (rec-subst (exts σ) A)

dual-rec-subst : ∀{n r s} (σ : Fin r → PreType n s) (A : PreType n r) →
                 dual (rec-subst σ A) ≡ rec-subst (dual ∘ σ) (dual A)
dual-rec-subst σ (var x) = refl
dual-rec-subst σ (rav x) = refl
dual-rec-subst σ skip = refl
dual-rec-subst σ ⊤ = refl
dual-rec-subst σ 𝟘 = refl
dual-rec-subst σ ⊥ = refl
dual-rec-subst σ 𝟙 = refl
dual-rec-subst σ (A ⨟ B) = cong₂ _⨟_ (dual-rec-subst σ A) (dual-rec-subst σ B)
dual-rec-subst σ (A & B) = cong₂ _⊕_ (dual-rec-subst σ A) (dual-rec-subst σ B)
dual-rec-subst σ (A ⊕ B) = cong₂ _&_ (dual-rec-subst σ A) (dual-rec-subst σ B)
dual-rec-subst σ (A ⅋ B) = cong₂ _⊗_ (dual-rec-subst σ A) (dual-rec-subst σ B)
dual-rec-subst σ (A ⊗ B) = cong₂ _⅋_ (dual-rec-subst σ A) (dual-rec-subst σ B)
dual-rec-subst σ (μ ⊲ A) = cong (μ ⊳_) (dual-rec-subst σ A)
dual-rec-subst σ (μ ⊳ A) = cong (μ ⊲_) (dual-rec-subst σ A)
dual-rec-subst σ (inv x) = refl
dual-rec-subst σ (rec A) rewrite dual-exts σ = cong rec (dual-rec-subst (exts σ) A)

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
unfold A = rec-subst (s-just (rec A)) A

dual-unfold : ∀{n r} (A : PreType n (suc r)) → dual (unfold A) ≡ unfold (dual A)
dual-unfold A rewrite dual-rec-subst (s-just (rec A)) A | dual-s-just (rec A) = refl

-- POLYMORPHISM

subst : ∀{n m r} → (∀{u} → Fin n → PreType m u) → PreType n r → PreType m r
subst σ (var x) = σ x
subst σ (rav x) = dual (σ x)
subst σ skip = skip
subst σ ⊤ = ⊤
subst σ 𝟘 = 𝟘
subst σ ⊥ = ⊥
subst σ 𝟙 = 𝟙
subst σ (A ⨟ B) = subst σ A ⨟ subst σ B
subst σ (A & B) = subst σ A & subst σ B
subst σ (A ⊕ B) = subst σ A ⊕ subst σ B
subst σ (A ⅋ B) = subst σ A ⅋ subst σ B
subst σ (A ⊗ B) = subst σ A ⊗ subst σ B
subst σ (μ ⊲ A) = μ ⊲ subst σ A
subst σ (μ ⊳ A) = μ ⊳ subst σ A
subst σ (inv x) = inv x
subst σ (rec A) = rec (subst σ A)

dual-subst : ∀{n m r} (σ : ∀{u} → Fin n → PreType m u) (A : PreType n r) →
             dual (subst σ A) ≡ subst σ (dual A)
dual-subst σ (var x) = refl
dual-subst σ (rav x) = refl
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
dual-subst σ (μ ⊲ A) = cong (μ ⊳_) (dual-subst σ A)
dual-subst σ (μ ⊳ A) = cong (μ ⊲_) (dual-subst σ A)
dual-subst σ (inv x) = refl
dual-subst σ (rec A) = cong rec (dual-subst σ A)

Type : ℕ → Set
Type n = PreType n 0

GroundType : Set
GroundType = Type 0

subst-compose : ∀{m n o r}
                (σ₁ : ∀{u} → Fin m → PreType n u) (σ₂ : ∀{u} → Fin n → PreType o u) →
                (A : PreType m r) →
                subst σ₂ (subst σ₁ A) ≡ subst (subst σ₂ ∘ σ₁) A
subst-compose σ₁ σ₂ (var x) = refl
subst-compose σ₁ σ₂ (rav x) = sym (dual-subst σ₂ (σ₁ x))
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
subst-compose σ₁ σ₂ (μ ⊲ A) = cong (μ ⊲_) (subst-compose σ₁ σ₂ A)
subst-compose σ₁ σ₂ (μ ⊳ A) = cong (μ ⊳_) (subst-compose σ₁ σ₂ A)
subst-compose σ₁ σ₂ (inv x) = refl
subst-compose σ₁ σ₂ (rec A) = cong rec (subst-compose σ₁ σ₂ A)
