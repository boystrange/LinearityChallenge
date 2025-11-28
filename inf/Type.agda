{-# OPTIONS --rewriting --guardedness #-}
open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
--open import Agda.Builtin.Equality.Rewrite

data PreType : ℕ -> Set
record ∞PreType (n : ℕ) : Set where
  constructor box_
  coinductive
  field force : PreType n
open ∞PreType public

data PreType where
  𝟘 𝟙 ⊥ ⊤          : ∀{n} → PreType n
  var rav          : ∀{n} → Fin n → PreType n
  _&_ _⊕_ _⊗_ _⅋_  : ∀{n} → ∞PreType n → ∞PreType n → PreType n
  `? `!            : ∀{n} → ∞PreType n → PreType n
  `∀ `∃            : ∀{n} → ∞PreType (suc n) → PreType n

dual : ∀{n} -> PreType n -> ∞PreType n
dual 𝟘 .force = ⊤
dual 𝟙 .force = ⊥
dual ⊥ .force = 𝟙
dual ⊤ .force = 𝟘
dual (var n) .force = rav n
dual (rav n) .force = var n
dual (A & B) .force = dual (A .force) ⊕ dual (B .force)
dual (A ⊕ B) .force = dual (A .force) & dual (B .force)
dual (A ⊗ B) .force = dual (A .force) ⅋ dual (B .force)
dual (A ⅋ B) .force = dual (A .force) ⊗ dual (B .force)
dual (`? A) .force = `! (dual (A .force))
dual (`! A) .force = `? (dual (A .force))
dual (`∀ A) .force = `∃ (dual (A .force))
dual (`∃ A) .force = `∀ (dual (A .force))

data _~_ : ∀{n} -> PreType n -> PreType n -> Set
record ∞Sim {n : ℕ} (A B : PreType n) : Set where
  constructor box_
  coinductive
  field force : A ~ B
open ∞Sim public

data _~_ where
  ~𝟘 : ∀{n} -> _~_ {n} 𝟘 𝟘
  ~𝟙 : ∀{n} -> _~_ {n} 𝟙 𝟙
  ~⊤ : ∀{n} -> _~_ {n} ⊤ ⊤
  ~⊥ : ∀{n} -> _~_ {n} ⊥ ⊥
  ~v : ∀{n k} -> _~_ {n} (var k) (var k)
  ~r : ∀{n k} -> _~_ {n} (rav k) (rav k)
  ~& : ∀{n} {A A' B B' : ∞PreType n} ->
        ∞Sim (A .force) (A' .force) -> ∞Sim (B .force) (B' .force) -> (A & B) ~ (A' & B')
  ~⊕ : ∀{n} {A A' B B' : ∞PreType n} ->
        ∞Sim (A .force) (A' .force) -> ∞Sim (B .force) (B' .force) -> (A ⊕ B) ~ (A' ⊕ B')
  ~⅋ : ∀{n} {A A' B B' : ∞PreType n} ->
        ∞Sim (A .force) (A' .force) -> ∞Sim (B .force) (B' .force) -> (A ⅋ B) ~ (A' ⅋ B')
  ~⊗ : ∀{n} {A A' B B' : ∞PreType n} ->
        ∞Sim (A .force) (A' .force) -> ∞Sim (B .force) (B' .force) -> (A ⊗ B) ~ (A' ⊗ B')
  ~∀ : ∀{n} {A A' : ∞PreType (suc n)} -> ∞Sim (A .force) (A' .force) -> (`∀ A) ~ (`∀ A')
  ~∃ : ∀{n} {A A' : ∞PreType (suc n)} -> ∞Sim (A .force) (A' .force) -> (`∃ A) ~ (`∃ A')
  ~! : ∀{n} {A A' : ∞PreType n} -> ∞Sim (A .force) (A' .force) -> (`! A) ~ (`! A')
  ~? : ∀{n} {A A' : ∞PreType n} -> ∞Sim (A .force) (A' .force) -> (`? A) ~ (`? A')

~refl : ∀{n} {A : PreType n} -> ∞Sim A A
~refl {_} {𝟘} .force = ~𝟘
~refl {_} {𝟙} .force = ~𝟙
~refl {_} {⊥} .force = ~⊥
~refl {_} {⊤} .force = ~⊤
~refl {_} {var x} .force = ~v
~refl {_} {rav x} .force = ~r
~refl {_} {A & B} .force = ~& ~refl ~refl
~refl {_} {A ⊕ B} .force = ~⊕ ~refl ~refl
~refl {_} {A ⊗ B} .force = ~⊗ ~refl ~refl
~refl {_} {A ⅋ B} .force = ~⅋ ~refl ~refl
~refl {_} {`? A} .force = ~? ~refl
~refl {_} {`! A} .force = ~! ~refl
~refl {_} {`∀ A} .force = ~∀ ~refl
~refl {_} {`∃ A} .force = ~∃ ~refl

~sym : ∀{n} {A B : PreType n} -> A ~ B -> ∞Sim B A
~sym ~𝟘 .force = ~𝟘
~sym ~𝟙 .force = ~𝟙
~sym ~⊤ .force = ~⊤
~sym ~⊥ .force = ~⊥
~sym ~v .force = ~v
~sym ~r .force = ~r
~sym (~& p q) .force = ~& (~sym (p .force)) (~sym (q .force))
~sym (~⊕ p q) .force = ~⊕ (~sym (p .force)) (~sym (q .force))
~sym (~⅋ p q) .force = ~⅋ (~sym (p .force)) (~sym (q .force))
~sym (~⊗ p q) .force = ~⊗ (~sym (p .force)) (~sym (q .force))
~sym (~∀ p) .force = ~∀ (~sym (p .force))
~sym (~∃ p) .force = ~∃ (~sym (p .force))
~sym (~! p) .force = ~! (~sym (p .force))
~sym (~? p) .force = ~? (~sym (p .force))

~trans : ∀{n} {A B C : PreType n} -> A ~ B -> B ~ C -> ∞Sim A C
~trans ~𝟘 ~𝟘 .force = ~𝟘
~trans ~𝟙 ~𝟙 .force = ~𝟙
~trans ~⊤ ~⊤ .force = ~⊤
~trans ~⊥ ~⊥ .force = ~⊥
~trans ~v ~v .force = ~v
~trans ~r ~r .force = ~r
~trans (~& p₁ p₂) (~& q₁ q₂) .force = ~& (~trans (p₁ .force) (q₁ .force)) (~trans (p₂ .force) (q₂ .force))
~trans (~⊕ p₁ p₂) (~⊕ q₁ q₂) .force = ~⊕ (~trans (p₁ .force) (q₁ .force)) (~trans (p₂ .force) (q₂ .force))
~trans (~⅋ p₁ p₂) (~⅋ q₁ q₂) .force = ~⅋ (~trans (p₁ .force) (q₁ .force)) (~trans (p₂ .force) (q₂ .force))
~trans (~⊗ p₁ p₂) (~⊗ q₁ q₂) .force = ~⊗ (~trans (p₁ .force) (q₁ .force)) (~trans (p₂ .force) (q₂ .force))
~trans (~∀ p) (~∀ q) .force = ~∀ (~trans (p .force) (q .force))
~trans (~∃ p) (~∃ q) .force = ~∃ (~trans (p .force) (q .force))
~trans (~! p) (~! q) .force = ~! (~trans (p .force) (q .force))
~trans (~? p) (~? q) .force = ~? (~trans (p .force) (q .force))

dual-inv : ∀{n} {A : PreType n} → ∞Sim (dual (dual A .force) .force) A
dual-inv {_} {𝟘} .force = ~𝟘
dual-inv {_} {𝟙} .force = ~𝟙
dual-inv {_} {⊥} .force = ~⊥
dual-inv {_} {⊤} .force = ~⊤
dual-inv {_} {var x} .force = ~v
dual-inv {_} {rav x} .force = ~r
dual-inv {_} {A & B} .force = ~& dual-inv dual-inv
dual-inv {_} {A ⊕ B} .force = ~⊕ dual-inv dual-inv
dual-inv {_} {A ⊗ B} .force = ~⊗ dual-inv dual-inv
dual-inv {_} {A ⅋ B} .force = ~⅋ dual-inv dual-inv
dual-inv {_} {`? A} .force = ~? dual-inv
dual-inv {_} {`! A} .force = ~! dual-inv
dual-inv {_} {`∀ A} .force = ~∀ dual-inv
dual-inv {_} {`∃ A} .force = ~∃ dual-inv

dual-dual-~ : ∀{n} {A : PreType n} → (dual (dual A .force) .force) ~ A
dual-dual-~ {_} {A} = dual-inv .force

{-# BUILTIN REWRITE _~_ #-}
{-# REWRITE dual-dual-~ #-}

ext : ∀{m n} → (Fin m → Fin n) → Fin (suc m) → Fin (suc n)
ext ρ zero = zero
ext ρ (suc k) = suc (ρ k)

rename : ∀{m n} → (Fin m → Fin n) → PreType m → ∞PreType n
rename ρ 𝟘 .force = 𝟘
rename ρ 𝟙 .force = 𝟙
rename ρ ⊥ .force = ⊥
rename ρ ⊤ .force = ⊤
rename ρ (var x) .force = var (ρ x)
rename ρ (rav x) .force = rav (ρ x)
rename ρ (`! A) .force = `! (rename ρ (A .force))
rename ρ (`? A) .force = `? (rename ρ (A .force))
rename ρ (A & B) .force = rename ρ (A .force) & rename ρ (B .force)
rename ρ (A ⊕ B) .force = rename ρ (A .force) ⊕ rename ρ (B .force)
rename ρ (A ⊗ B) .force = rename ρ (A .force) ⊗ rename ρ (B .force)
rename ρ (A ⅋ B) .force = rename ρ (A .force) ⅋ rename ρ (B .force)
rename ρ (`∀ A) .force = `∀ (rename (ext ρ) (A .force))
rename ρ (`∃ A) .force = `∃ (rename (ext ρ) (A .force))

exts : ∀{m n} → (Fin m → ∞PreType n) → Fin (suc m) → ∞PreType (suc n)
exts σ zero = box (var zero)
exts σ (suc k) = rename suc (σ k .force)

subst : ∀{m n} → (Fin m → ∞PreType n) → PreType m → ∞PreType n
subst σ 𝟘 .force = 𝟘
subst σ 𝟙 .force = 𝟙
subst σ ⊥ .force = ⊥
subst σ ⊤ .force = ⊤
subst σ (var x) = σ x
subst σ (rav x) = dual (σ x .force)
subst σ (`! A) .force = `! (subst σ (A .force))
subst σ (`? A) .force = `? (subst σ (A .force))
subst σ (A & B) .force = subst σ (A .force) & subst σ (B .force)
subst σ (A ⊕ B) .force = subst σ (A .force) ⊕ subst σ (B .force)
subst σ (A ⊗ B) .force = subst σ (A .force) ⊗ subst σ (B .force)
subst σ (A ⅋ B) .force = subst σ (A .force) ⅋ subst σ (B .force)
subst σ (`∀ A) .force = `∀ (subst (exts σ) (A .force))
subst σ (`∃ A) .force = `∃ (subst (exts σ) (A .force))

make-subst : ∀{n} → PreType n → Fin (suc n) → ∞PreType n
make-subst A zero .force = A
make-subst A (suc k) .force = var k

dual-subst : ∀{m n} {σ : Fin m → ∞PreType n} {A : PreType m} → ∞Sim (subst σ (dual A .force) .force) (dual (subst σ A .force) .force)
dual-subst {_} {_} {σ} {𝟘} .force = ~⊤
dual-subst {_} {_} {σ} {𝟙} .force = ~⊥
dual-subst {_} {_} {σ} {⊥} .force = ~𝟙
dual-subst {_} {_} {σ} {⊤} .force = ~𝟘
dual-subst {_} {_} {σ} {var x} = ~refl
dual-subst {_} {_} {σ} {rav x} = ~refl
dual-subst {_} {_} {σ} {A & B} .force = ~⊕ (dual-subst {_} {_} {σ} {A .force}) (dual-subst {_} {_} {σ} {B .force})
dual-subst {_} {_} {σ} {A ⊕ B} .force = ~& (dual-subst {_} {_} {σ} {A .force}) (dual-subst {_} {_} {σ} {B .force})
dual-subst {_} {_} {σ} {A ⊗ B} .force = ~⅋ (dual-subst {_} {_} {σ} {A .force}) (dual-subst {_} {_} {σ} {B .force})
dual-subst {_} {_} {σ} {A ⅋ B} .force = ~⊗ (dual-subst {_} {_} {σ} {A .force}) (dual-subst {_} {_} {σ} {B .force})
dual-subst {_} {_} {σ} {`? A} .force = ~! (dual-subst {_} {_} {σ} {A .force})
dual-subst {_} {_} {σ} {`! A} .force = ~? (dual-subst {_} {_} {σ} {A .force})
dual-subst {_} {_} {σ} {`∀ A} .force = ~∃ (dual-subst {_} {_} {exts σ} {A .force})
dual-subst {_} {_} {σ} {`∃ A} .force = ~∀ (dual-subst {_} {_} {exts σ} {A .force})

dual-subst-~ : ∀{m n} {σ : Fin m -> ∞PreType n} {A : PreType m} -> (subst σ (dual A .force) .force) ~ (dual (subst σ A .force) .force)
dual-subst-~ {m} {n} {σ} {A} = dual-subst {m} {n} {σ} {A} .force

{-# REWRITE dual-subst-~ #-}

Type : Set
Type = PreType zero

∞Type : Set
∞Type = ∞PreType zero
