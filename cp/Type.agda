{-# OPTIONS --rewriting #-}
open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Agda.Builtin.Equality.Rewrite

data PreType : ℕ → Set where
  𝟘 𝟙 ⊥ ⊤          : ∀{n} → PreType n
  var rav          : ∀{n} → Fin n → PreType n
  _&_ _⊕_ _⊗_ _⅋_  : ∀{n} → PreType n → PreType n → PreType n
  `? `!            : ∀{n} → PreType n → PreType n
  `∀ `∃            : ∀{n} → PreType (suc n) → PreType n

dual : ∀{n} → PreType n → PreType n
dual 𝟘        = ⊤
dual 𝟙        = ⊥
dual ⊥        = 𝟙
dual ⊤        = 𝟘
dual (var x)  = rav x
dual (rav x)  = var x
dual (`! A)    = `? (dual A)
dual (`? A)    = `! (dual A)
dual (A & B)  = dual A ⊕ dual B
dual (A ⊕ B)  = dual A & dual B
dual (A ⊗ B)  = dual A ⅋ dual B
dual (A ⅋ B)  = dual A ⊗ dual B
dual (`∀ A)   = `∃ (dual A)
dual (`∃ A)   = `∀ (dual A)

dual-inv : ∀{n} {A : PreType n} → dual (dual A) ≡ A
dual-inv {_} {𝟘} = refl
dual-inv {_} {𝟙} = refl
dual-inv {_} {⊥} = refl
dual-inv {_} {⊤} = refl
dual-inv {_} {var x} = refl
dual-inv {_} {rav x} = refl
dual-inv {_} {`! A} = cong `! dual-inv
dual-inv {_} {`? A} = cong `? dual-inv
dual-inv {_} {A & B} = cong₂ _&_ dual-inv dual-inv
dual-inv {_} {A ⊕ B} = cong₂ _⊕_ dual-inv dual-inv
dual-inv {_} {A ⊗ B} = cong₂ _⊗_ dual-inv dual-inv
dual-inv {_} {A ⅋ B} = cong₂ _⅋_ dual-inv dual-inv
dual-inv {_} {`∀ A} = cong `∀ dual-inv
dual-inv {_} {`∃ A} = cong `∃ dual-inv

{-# REWRITE dual-inv #-}

ext : ∀{m n} → (Fin m → Fin n) → Fin (suc m) → Fin (suc n)
ext ρ zero = zero
ext ρ (suc k) = suc (ρ k)

rename : ∀{m n} → (Fin m → Fin n) → PreType m → PreType n
rename ρ 𝟘 = 𝟘
rename ρ 𝟙 = 𝟙
rename ρ ⊥ = ⊥
rename ρ ⊤ = ⊤
rename ρ (var x) = var (ρ x)
rename ρ (rav x) = rav (ρ x)
rename ρ (`! A) = `! (rename ρ A)
rename ρ (`? A) = `? (rename ρ A)
rename ρ (A & B) = rename ρ A & rename ρ B
rename ρ (A ⊕ B) = rename ρ A ⊕ rename ρ B
rename ρ (A ⊗ B) = rename ρ A ⊗ rename ρ B
rename ρ (A ⅋ B) = rename ρ A ⅋ rename ρ B
rename ρ (`∀ A) = `∀ (rename (ext ρ) A)
rename ρ (`∃ A) = `∃ (rename (ext ρ) A)

exts : ∀{m n} → (Fin m → PreType n) → Fin (suc m) → PreType (suc n)
exts σ zero = var zero
exts σ (suc k) = rename suc (σ k)

subst : ∀{m n} → (Fin m → PreType n) → PreType m → PreType n
subst σ 𝟘 = 𝟘
subst σ 𝟙 = 𝟙
subst σ ⊥ = ⊥
subst σ ⊤ = ⊤
subst σ (var x) = σ x
subst σ (rav x) = dual (σ x)
subst σ (`! A) = `! (subst σ A)
subst σ (`? A) = `? (subst σ A)
subst σ (A & B) = subst σ A & subst σ B
subst σ (A ⊕ B) = subst σ A ⊕ subst σ B
subst σ (A ⊗ B) = subst σ A ⊗ subst σ B
subst σ (A ⅋ B) = subst σ A ⅋ subst σ B
subst σ (`∀ A) = `∀ (subst (exts σ) A)
subst σ (`∃ A) = `∃ (subst (exts σ) A)

make-subst : ∀{n} → PreType n → Fin (suc n) → PreType n
make-subst A zero = A
make-subst A (suc k) = var k

dual-subst : ∀{m n} {σ : Fin m → PreType n} {A : PreType m} → subst σ (dual A) ≡ dual (subst σ A)
dual-subst {_} {_} {σ} {𝟘} = refl
dual-subst {_} {_} {σ} {𝟙} = refl
dual-subst {_} {_} {σ} {⊥} = refl
dual-subst {_} {_} {σ} {⊤} = refl
dual-subst {_} {_} {σ} {var x} = refl
dual-subst {_} {_} {σ} {rav x} = refl
dual-subst {_} {_} {σ} {`! A} = cong `? (dual-subst {σ = σ} {A})
dual-subst {_} {_} {σ} {`? A} = cong `! (dual-subst {σ = σ} {A})
dual-subst {_} {_} {σ} {A & B} = cong₂ _⊕_ (dual-subst {σ = σ} {A}) (dual-subst {σ = σ} {B})
dual-subst {_} {_} {σ} {A ⊕ B} = cong₂ _&_ (dual-subst {σ = σ} {A}) (dual-subst {σ = σ} {B})
dual-subst {_} {_} {σ} {A ⊗ B} = cong₂ _⅋_ (dual-subst {σ = σ} {A}) (dual-subst {σ = σ} {B})
dual-subst {_} {_} {σ} {A ⅋ B} = cong₂ _⊗_ (dual-subst {σ = σ} {A}) (dual-subst {σ = σ} {B})
dual-subst {_} {_} {σ} {`∀ A} = cong `∃ (dual-subst {σ = exts σ} {A})
dual-subst {_} {_} {σ} {`∃ A} = cong `∀ (dual-subst {σ = exts σ} {A})

{-# REWRITE dual-subst #-}

Type : Set
Type = PreType zero
