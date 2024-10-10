open import Data.Bool using (Bool; if_then_else_)
open Bool using (true; false)
open import Data.Sum
open import Data.Product using (Σ; _×_; _,_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Nullary using (¬_; contradiction)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Type
open import Context
open import Process

infix 4 _<=_ _<<_

data _<=_ : Type -> Type -> Set where
  sub-0 : ∀{A} -> Zero <= A
  sub-⊤ : ∀{A} -> A <= Top
  sub-1 : One <= One
  sub-⊥ : Bot <= Bot
  sub-& : ∀{A B A' B'} -> A <= A' -> B <= B' -> A & B <= A' & B'
  sub-⊕ : ∀{A B A' B'} -> A <= A' -> B <= B' -> A ⊕ B <= A' ⊕ B'
  sub-⅋ : ∀{A B A' B'} -> A <= A' -> B <= B' -> A ⅋ B <= A' ⅋ B'
  sub-⊗ : ∀{A B A' B'} -> A <= A' -> B <= B' -> A ⊗ B <= A' ⊗ B'

<=-refl : ∀{A} -> A <= A
<=-refl {Zero} = sub-0
<=-refl {One} = sub-1
<=-refl {Bot} = sub-⊥
<=-refl {Top} = sub-⊤
<=-refl {A & B} = sub-& <=-refl <=-refl
<=-refl {A ⊕ B} = sub-⊕ <=-refl <=-refl
<=-refl {A ⊗ B} = sub-⊗ <=-refl <=-refl
<=-refl {A ⅋ B} = sub-⅋ <=-refl <=-refl

data _<<_ : Context -> Context -> Set where
  zero : [] << []
  succ : ∀{A B Γ Δ} -> A <= B -> Γ << Δ -> A :: Γ << B :: Δ

double-split : ∀{Γ Δ₁ Δ₂ A₁ A₂} -> Γ ≃ A₁ , Δ₁ -> Γ ≃ A₂ , Δ₂ -> (A₁ ≡ A₂ × Δ₁ ≡ Δ₂) ⊎
  ∃[ Θ ] Δ₁ ≃ A₂ , Θ × Δ₂ ≃ A₁ , Θ
double-split (split-l p) (split-l q) with +-empty-l p | +-empty-l q
... | refl | refl = inj₁ (refl , refl)
double-split (split-l p) (split-r q) with +-empty-l p
... | refl = inj₂ (_ , q , split-l +-unit-l)
double-split (split-r p) (split-l q) with +-empty-l q
... | refl = inj₂ (_ , split-l +-unit-l , p)
double-split (split-r p) (split-r q) with double-split p q
... | inj₁ (refl , refl) = inj₁ (refl , refl)
... | inj₂ (Θ , p' , q') = inj₂ (_ , split-r p' , split-r q')

make-link : ∀{A A' B B'} -> A <= A' -> B <= B' -> Dual A B -> Process (A' :: B' :: [])
make-link sub-0 sub-⊤ dual-zero-top = fail (split-r (split-l split-e))
make-link sub-⊤ s₂ d = fail (split-l (split-r split-e))
make-link sub-1 sub-⊤ dual-one-bot = fail (split-r (split-l split-e))
make-link sub-1 sub-⊥ dual-one-bot = wait (split-r (split-l split-e)) (close (split-l split-e))
make-link sub-⊥ sub-⊤ dual-bot-one = fail (split-r (split-l split-e))
make-link sub-⊥ sub-1 dual-bot-one = wait (split-l (split-r split-e)) (close (split-l split-e))
make-link (sub-& s₁ s₃) sub-⊤ (dual-with-plus d₁ d₂) = fail (split-r (split-l split-e))
make-link (sub-& s₁ s₃) (sub-⊕ s₂ s₄) (dual-with-plus d₁ d₂) =
  branch (split-l (split-r split-e))
         (select true (split-r (split-l split-e)) (make-link s₂ s₁ (dual-symm d₁)))
         (select false (split-r (split-l split-e)) (make-link s₄ s₃ (dual-symm d₂)))
make-link (sub-⊕ s₁ s₃) sub-⊤ (dual-plus-with d₁ d₂) = fail (split-r (split-l split-e))
make-link (sub-⊕ s₁ s₃) (sub-& s₂ s₄) (dual-plus-with d₁ d₂) =
  branch (split-r (split-l split-e))
         (select true (split-r (split-l split-e)) (make-link s₁ s₂ d₁))
         (select false (split-r (split-l split-e)) (make-link s₃ s₄ d₂))
make-link (sub-⅋ s₁ s₃) sub-⊤ (dual-join-fork d d₁) = fail (split-r (split-l split-e))
make-link (sub-⅋ s₁ s₃) (sub-⊗ s₂ s₄) (dual-join-fork d₁ d₂) =
  join (split-l (split-r split-e))
       (fork (split-r (split-r (split-l split-e))) (split-r (split-l split-e))
             (make-link s₂ s₁ (dual-symm d₁))
             (make-link s₄ s₃ (dual-symm d₂)))
make-link (sub-⊗ s₁ s₃) sub-⊤ (dual-fork-join d d₁) = fail (split-r (split-l split-e))
make-link (sub-⊗ s₁ s₃) (sub-⅋ s₂ s₄) (dual-fork-join d₁ d₂) =
  join (split-r (split-l split-e))
       (fork (split-r (split-r (split-l split-e))) (split-r (split-l split-e))
             (make-link s₁ s₂ d₁)
             (make-link s₃ s₄ d₂))

split<< : ∀{Γ Γ₁ Γ₂ Δ} -> Γ << Δ -> Γ ≃ Γ₁ + Γ₂ ->
          ∃[ Δ₁ ] ∃[ Δ₂ ] Δ ≃ Δ₁ + Δ₂ × Γ₁ << Δ₁ × Γ₂ << Δ₂
split<< zero split-e = [] , [] , split-e , zero , zero
split<< (succ s₁ s₂) (split-l p) with split<< s₂ p
... | Δ₁ , Δ₂ , p' , s₃ , s₄ = _ , _ , split-l p' , succ s₁ s₃ , s₄
split<< (succ s₁ s₂) (split-r p) with split<< s₂ p
... | _ , _ , p' , s₃ , s₄ = _ , _ , split-r p' , s₃ , succ s₁ s₄

split<= : ∀{Γ Γ' A Δ} -> Γ << Δ -> Γ ≃ A , Γ' ->
          ∃[ B ] ∃[ Δ' ] Δ ≃ B , Δ' × A <= B × Γ' << Δ'
split<= s p with split<< s p
... | _ , _ , p' , succ s₁ zero , s₃ = _ , _ , p' , s₁ , s₃

sub-link : ∀{Γ Δ A B} -> Γ << Δ -> Dual A B -> Γ ≃ [ A ] + [ B ] -> Process Δ
sub-link (succ s₁ (succ s₂ zero)) d (split-l (split-r split-e)) = make-link s₁ s₂ d
sub-link (succ s₁ (succ s₂ zero)) d (split-r (split-l split-e)) = make-link s₁ s₂ (dual-symm d)

sub : ∀{Γ Δ} -> Γ << Δ -> Process Γ -> Process Δ
sub s (link d p) = sub-link s d p
sub s (fail p) with split<= s p
... | _ , _ , p' , sub-⊤ , _ = fail p'
sub (succ sub-⊤ zero) (close (split-l split-e)) = fail (split-l split-e)
sub (succ sub-1 zero) (close (split-l split-e)) = close (split-l split-e)
sub s (wait p P) with split<= s p
... | .Top , Δ' , p' , sub-⊤ , s₂ = fail p'
... | .Bot , Δ' , p' , sub-⊥ , s₂ = wait p' (sub s₂ P)
sub s (select false p P) with split<= s p
... | _ , _ , p' , sub-⊤ , s₂ = fail p'
... | _ , _ , p' , sub-⊕ s₁ s₂ , s₃ = select false p' (sub (succ s₂ s₃) P)
sub s (select true p P) with split<= s p
... | _ , _ , p' , sub-⊤ , s₂ = fail p'
... | _ , _ , p' , sub-⊕ s₁ s₂ , s₃ = select true p' (sub (succ s₁ s₃) P)
sub s (branch p P Q) with split<= s p
... | _ , _ , p' , sub-⊤ , s₃ = fail p'
... | _ , _ , p' , sub-& s₁ s₂ , s₃ = branch p' (sub (succ s₁ s₃) P) (sub (succ s₂ s₃) Q)
sub s (fork p q P Q) with split<= s p
... | _ , _ , p' , sub-⊤ , s₃ = fail p'
... | _ , _ , p' , sub-⊗ s₁ s₂ , s₃ with split<< s₃ q
... | _ , _ , q' , s₄ , s₅ = fork p' q' (sub (succ s₁ s₄) P) (sub (succ s₂ s₅) Q)
sub s (join p P) with split<= s p
... | _ , _ , p' , sub-⊤ , s₂ = fail p'
... | _ , _ , p' , sub-⅋ s₁ s₂ , s₃ = join p' (sub (succ s₂ (succ s₁ s₃)) P)
sub s (cut d p P Q) with split<< s p
... | _ , _ , p' , s₁ , s₂ = cut d p' (sub (succ <=-refl s₁) P) (sub (succ <=-refl s₂) Q)
