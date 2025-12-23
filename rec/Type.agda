{-# OPTIONS --rewriting --guardedness #-}
open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Agda.Builtin.Equality.Rewrite

mutual
  data PreType : ℕ → Set where
    ⊤ 𝟘 ⊥ 𝟙          : ∀{n} → PreType n
    var rav          : ∀{n} → Fin n → PreType n
    _&_ _⊕_ _⅋_ _⊗_  : ∀{n} → ∞PreType n → ∞PreType n → PreType n
    `∀ `∃            : ∀{n} → ∞PreType (suc n) → PreType n
    `! `?            : ∀{n} → ∞PreType n → PreType n

  record ∞PreType (n : ℕ) : Set where
    coinductive
    field
      force : PreType n

open ∞PreType public

dual : ∀{n} → PreType n → ∞PreType n
dual ⊤        .force = 𝟘
dual 𝟘        .force = ⊤
dual ⊥        .force = 𝟙
dual 𝟙        .force = ⊥
dual (var x)  .force = rav x
dual (rav x)  .force = var x
dual (A & B)  .force = dual (A .force) ⊕ dual (B .force)
dual (A ⊕ B)  .force = dual (A .force) & dual (B .force)
dual (A ⅋ B)  .force = dual (A .force) ⊗ dual (B .force)
dual (A ⊗ B)  .force = dual (A .force) ⅋ dual (B .force)
dual (`∀ A)   .force = `∃ (dual (A .force))
dual (`∃ A)   .force = `∀ (dual (A .force))
dual (`! A)   .force = `? (dual (A .force))
dual (`? A)   .force = `! (dual (A .force))

mutual
  data _~_ : ∀{n} → PreType n → PreType n → Set where
    s-⊤ : ∀{n} → _~_ {n} ⊤ ⊤
    s-𝟘 : ∀{n} → _~_ {n} 𝟘 𝟘
    s-⊥ : ∀{n} → _~_ {n} ⊥ ⊥
    s-𝟙 : ∀{n} → _~_ {n} 𝟙 𝟙
    s-v : ∀{n x} → _~_ {n} (var x) (var x)
    s-r : ∀{n x} → _~_ {n} (rav x) (rav x)
    s-& : ∀{n A A' B B'} → A .force ∞~ A' .force → B .force ∞~ B' .force → _~_ {n} (A & B) (A' & B')
    s-⊕ : ∀{n A A' B B'} → A .force ∞~ A' .force → B .force ∞~ B' .force → _~_ {n} (A ⊕ B) (A' ⊕ B')
    s-⅋ : ∀{n A A' B B'} → A .force ∞~ A' .force → B .force ∞~ B' .force → _~_ {n} (A ⅋ B) (A' ⅋ B')
    s-⊗ : ∀{n A A' B B'} → A .force ∞~ A' .force → B .force ∞~ B' .force → _~_ {n} (A ⊗ B) (A' ⊗ B')
    s-∀ : ∀{n A B} → A .force ∞~ B .force → _~_ {n} (`∀ A) (`∀ B)
    s-∃ : ∀{n A B} → A .force ∞~ B .force → _~_ {n} (`∃ A) (`∃ B)
    s-! : ∀{n A B} → A .force ∞~ B .force → _~_ {n} (`! A) (`! B)
    s-? : ∀{n A B} → A .force ∞~ B .force → _~_ {n} (`? A) (`? B)

  record _∞~_ {n} (A B : PreType n) : Set where
    coinductive
    field
      force : A ~ B

open _∞~_ public

~-refl : ∀{n} {A : PreType n} → A ∞~ A
~-refl {_} {⊤} .force = s-⊤
~-refl {_} {𝟘} .force = s-𝟘
~-refl {_} {⊥} .force = s-⊥
~-refl {_} {𝟙} .force = s-𝟙
~-refl {_} {var x} .force = s-v
~-refl {_} {rav x} .force = s-r
~-refl {_} {x & x₁} .force = s-& ~-refl ~-refl
~-refl {_} {x ⊕ x₁} .force = s-⊕ ~-refl ~-refl
~-refl {_} {x ⅋ x₁} .force = s-⅋ ~-refl ~-refl
~-refl {_} {x ⊗ x₁} .force = s-⊗ ~-refl ~-refl
~-refl {_} {`∀ x} .force = s-∀ ~-refl
~-refl {_} {`∃ x} .force = s-∃ ~-refl
~-refl {_} {`! x} .force = s-! ~-refl
~-refl {_} {`? x} .force = s-? ~-refl

∞dual-inv : ∀{n} {A : PreType n} → dual (dual A .force) .force ∞~ A
∞dual-inv {_} {⊤} .force = s-⊤
∞dual-inv {_} {𝟘} .force = s-𝟘
∞dual-inv {_} {⊥} .force = s-⊥
∞dual-inv {_} {𝟙} .force = s-𝟙
∞dual-inv {_} {var x} .force = s-v
∞dual-inv {_} {rav x} .force = s-r
∞dual-inv {_} {A & B} .force = s-& ∞dual-inv ∞dual-inv
∞dual-inv {_} {A ⊕ B} .force = s-⊕ ∞dual-inv ∞dual-inv
∞dual-inv {_} {A ⅋ B} .force = s-⅋ ∞dual-inv ∞dual-inv
∞dual-inv {_} {A ⊗ B} .force = s-⊗ ∞dual-inv ∞dual-inv
∞dual-inv {_} {`∀ A} .force = s-∀ ∞dual-inv
∞dual-inv {_} {`∃ A} .force = s-∃ ∞dual-inv
∞dual-inv {_} {`! A} .force = s-! ∞dual-inv
∞dual-inv {_} {`? A} .force = s-? ∞dual-inv

dual-inv : ∀{n} {A : PreType n} → dual (dual A .force) .force ~ A
dual-inv = ∞dual-inv .force

{-# BUILTIN REWRITE _~_ #-}
{-# REWRITE dual-inv #-}

ext : ∀{m n} → (Fin m → Fin n) → Fin (suc m) → Fin (suc n)
ext ρ zero = zero
ext ρ (suc k) = suc (ρ k)

rename : ∀{m n} → (Fin m → Fin n) → PreType m → ∞PreType n
rename ρ ⊤ .force = ⊤
rename ρ 𝟘 .force = 𝟘
rename ρ ⊥ .force = ⊥
rename ρ 𝟙 .force = 𝟙
rename ρ (var x) .force = var (ρ x)
rename ρ (rav x) .force = rav (ρ x)
rename ρ (A & B) .force = rename ρ (A .force) & rename ρ (B .force)
rename ρ (A ⊕ B) .force = rename ρ (A .force) ⊕ rename ρ (B .force)
rename ρ (A ⅋ B) .force = rename ρ (A .force) ⅋ rename ρ (B .force)
rename ρ (A ⊗ B) .force = rename ρ (A .force) ⊗ rename ρ (B .force)
rename ρ (`∀ A) .force = `∀ (rename (ext ρ) (A .force))
rename ρ (`∃ A) .force = `∃ (rename (ext ρ) (A .force))
rename ρ (`! A) .force = `! (rename ρ (A .force))
rename ρ (`? A) .force = `? (rename ρ (A .force))

exts : ∀{m n} → (Fin m → PreType n) → Fin (suc m) → PreType (suc n)
exts σ zero = var zero
exts σ (suc k) = rename suc (σ k) .force

subst : ∀{m n} → (Fin m → PreType n) → PreType m → ∞PreType n
subst σ ⊤ .force = ⊤
subst σ 𝟘 .force = 𝟘
subst σ ⊥ .force = ⊥
subst σ 𝟙 .force = 𝟙
subst σ (var x) .force = σ x
subst σ (rav x) .force = dual (σ x) .force
subst σ (A & B) .force = subst σ (A .force) & subst σ (B .force)
subst σ (A ⊕ B) .force = subst σ (A .force) ⊕ subst σ (B .force)
subst σ (A ⅋ B) .force = subst σ (A .force) ⅋ subst σ (B .force)
subst σ (A ⊗ B) .force = subst σ (A .force) ⊗ subst σ (B .force)
subst σ (`∀ A) .force = `∀ (subst (exts σ) (A .force))
subst σ (`∃ A) .force = `∃ (subst (exts σ) (A .force))
subst σ (`! A) .force = `! (subst σ (A .force))
subst σ (`? A) .force = `? (subst σ (A .force))

[_/] : ∀{n} → PreType n → Fin (suc n) → PreType n
[ A /] zero     = A
[ A /] (suc k)  = var k

∞dual-subst : ∀{m n} {σ : Fin m → PreType n} {A : PreType m} → subst σ (dual A .force) .force ∞~ dual (subst σ A .force) .force
∞dual-subst {_} {_} {σ} {⊤} .force = s-𝟘
∞dual-subst {_} {_} {σ} {𝟘} .force = s-⊤
∞dual-subst {_} {_} {σ} {⊥} .force = s-𝟙
∞dual-subst {_} {_} {σ} {𝟙} .force = s-⊥
∞dual-subst {_} {_} {σ} {var x} .force = ~-refl .force
∞dual-subst {_} {_} {σ} {rav x} .force = ~-refl .force
∞dual-subst {_} {_} {σ} {A & B} .force = s-⊕ (∞dual-subst {σ = σ} {A .force}) (∞dual-subst {σ = σ} {B .force})
∞dual-subst {_} {_} {σ} {A ⊕ B} .force = s-& (∞dual-subst {σ = σ} {A .force}) (∞dual-subst {σ = σ} {B .force})
∞dual-subst {_} {_} {σ} {A ⅋ B} .force = s-⊗ (∞dual-subst {σ = σ} {A .force}) (∞dual-subst {σ = σ} {B .force})
∞dual-subst {_} {_} {σ} {A ⊗ B} .force = s-⅋ (∞dual-subst {σ = σ} {A .force}) (∞dual-subst {σ = σ} {B .force})
∞dual-subst {_} {_} {σ} {`∀ A} .force = s-∃ (∞dual-subst {σ = exts σ} {A .force})
∞dual-subst {_} {_} {σ} {`∃ A} .force = s-∀ (∞dual-subst {σ = exts σ} {A .force})
∞dual-subst {_} {_} {σ} {`! A} .force = s-? (∞dual-subst {σ = σ} {A .force})
∞dual-subst {_} {_} {σ} {`? A} .force = s-! (∞dual-subst {σ = σ} {A .force})

dual-subst : ∀{m n} {σ : Fin m → PreType n} {A : PreType m} → subst σ (dual A .force) .force ~ dual (subst σ A .force) .force
dual-subst {_} {_} {σ} {A} = ∞dual-subst {σ = σ} {A} .force

{-# REWRITE dual-subst #-}

Type : Set
Type = PreType zero
