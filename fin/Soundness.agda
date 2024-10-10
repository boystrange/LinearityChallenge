open import Data.Bool using (Bool; if_then_else_)
open Bool using (true; false)
open import Data.Empty
open import Data.Sum
open import Data.Product using (Σ; _×_; _,_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Nullary using (¬_; contradiction)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Type
open import Context
open import Process
open import Kind

postulate
  cut-elimination : ∀{Γ} (P : Process Γ) -> Σ[ Q ∈ Process Γ ] CutFree Q

weak-soundness : ∀{P : Process [ Zero ]} -> ¬ CutFree P
weak-soundness (link d (split-l ()))
weak-soundness (link d (split-r ()))
weak-soundness (fail (split-r ()))
weak-soundness (wait (split-r ()) cf)
weak-soundness (case (split-r ()) cf cf₁)
weak-soundness (join (split-r ()) cf)
weak-soundness (select x (split-r ()) cf)
weak-soundness (fork (split-r ()) q cf cf₁)

strong-soundness : ¬ (Process [ Zero ])
strong-soundness P with cut-elimination P
... | _ , cf = weak-soundness cf

infix 4 _∈_

data _∈_ : Type -> Context -> Set where
  here : ∀{A Γ} -> A ∈ A :: Γ
  next : ∀{A B Γ} -> A ∈ Γ -> A ∈ B :: Γ

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

in-split : ∀{A Γ Γ₁ Γ₂} -> A ∈ Γ -> Γ ≃ Γ₁ + Γ₂ -> A ∈ Γ₁ ⊎ A ∈ Γ₂
in-split here (split-l p) = inj₁ here
in-split (next x) (split-l p) with in-split x p
... | inj₁ r = inj₁ (next r)
... | inj₂ r = inj₂ r
in-split here (split-r p) = inj₂ here
in-split (next x) (split-r p) with in-split x p
... | inj₁ r = inj₁ r
... | inj₂ r = inj₂ (next r)

split-in : ∀{A Γ Δ} -> Γ ≃ A , Δ -> A ∈ Γ
split-in (split-l p) = here
split-in (split-r p) = next (split-in p)

split-in-l : ∀{Γ Γ₁ Γ₂ A} -> Γ ≃ Γ₁ + Γ₂ -> A ∈ Γ₁ -> A ∈ Γ
split-in-l (split-l p) here = here
split-in-l (split-r p) here = next (split-in-l p here)
split-in-l (split-l p) (next q) = next (split-in-l p q)
split-in-l (split-r p) (next q) = next (split-in-l p (next q))

split-in-r : ∀{Γ Γ₁ Γ₂ A} -> Γ ≃ Γ₁ + Γ₂ -> A ∈ Γ₂ -> A ∈ Γ
split-in-r p q = split-in-l (+-comm p) q

data IsTop : Type -> Set where
  refl   : IsTop Top
  plus-l : ∀{A B} -> IsTop A -> IsTop (A ⊕ B)
  plus-r : ∀{A B} -> IsTop B -> IsTop (A ⊕ B)
  with-b : ∀{A B} -> IsTop A -> IsTop B -> IsTop (A & B)
  fork-l : ∀{A B} -> IsTop A -> IsTop (A ⊗ B)
  fork-r : ∀{A B} -> IsTop B -> IsTop (A ⊗ B)
  join-l : ∀{A B} -> IsTop A -> IsTop (A ⅋ B)
  join-r : ∀{A B} -> IsTop B -> IsTop (A ⅋ B)

data IsZero : Type -> Set where
  refl   : IsZero Zero
  plus-b : ∀{A B} -> IsZero A -> IsZero B -> IsZero (A ⊕ B)
  with-l : ∀{A B} -> IsZero A -> IsZero (A & B)
  with-r : ∀{A B} -> IsZero B -> IsZero (A & B)
  fork-l : ∀{A B} -> IsZero A -> IsZero (A ⊗ B)
  fork-r : ∀{A B} -> IsZero B -> IsZero (A ⊗ B)
  join-l : ∀{A B} -> IsZero A -> IsZero (A ⅋ B)
  join-r : ∀{A B} -> IsZero B -> IsZero (A ⅋ B)

dual-top : ∀{A B} -> Dual A B -> IsTop A -> IsZero B
dual-top d At = {!!}

dual-zero : ∀{A B} -> Dual A B -> IsZero A -> IsTop B
dual-zero dual-zero-top refl = refl
dual-zero (dual-plus-with d e) (plus-b Az Bz) = with-b (dual-zero d Az) (dual-zero e Bz)
dual-zero (dual-with-plus d e) (with-l Az) = plus-l (dual-zero d Az)
dual-zero (dual-with-plus d e) (with-r Az) = plus-r (dual-zero e Az)
dual-zero (dual-fork-join d e) (fork-l iz) = join-l (dual-zero d iz)
dual-zero (dual-fork-join d e) (fork-r iz) = join-r (dual-zero e iz)
dual-zero (dual-join-fork d e) (join-l iz) = fork-l (dual-zero d iz)
dual-zero (dual-join-fork d e) (join-r iz) = fork-r (dual-zero e iz)

top-top : ∀{A B} -> Dual A B -> ¬ (IsTop A × IsTop B)
top-top d p = {!!}

zero : ∀{Γ A} -> Process Γ -> IsZero A -> A ∈ Γ -> ∃[ B ] B ∈ Γ × IsTop B
zero (link d (split-l (split-r split-e))) Az here = _ , next here , dual-zero d Az
zero (link d (split-l (split-r split-e))) Az (next here) = _ , here , dual-zero (dual-symm d) Az
zero (link d (split-r (split-l split-e))) Az here = {!!} , {!!} , {!!}
zero (link d (split-r (split-l split-e))) Az (next here) = {!!} , {!!} , {!!}
zero (fail p) Az Ain = _ , split-in-l p here , refl
zero (close (split-l split-e)) () here
zero (close (split-l split-e)) At (next ())
zero (wait p P) Az Ain = {!!}
zero (select x p P) Az Ain = {!!}
zero (branch p P Q) Az Ain = {!!}
zero (fork p q P Q) Az Ain with in-split Ain p
zero (fork p q P Q) (fork-l Az) Ain | inj₁ here with zero P Az here
... | B , here , Bt = _ , split-in-l p here , fork-l Bt
... | B , next Bin , Bt = B , split-in-r p (split-in-l q Bin) , Bt
zero (fork p q P Q) (fork-r Az) Ain | inj₁ here with zero Q Az here
... | B , here , Bt = _ , split-in-l p here , fork-r Bt
... | B , next Bin , Bt = B , split-in-r p (split-in-r q Bin) , Bt
zero (fork p q P Q) Az Ain | inj₂ Ain' with in-split Ain' q
zero (fork p q P Q) Az Ain | inj₂ Ain' | inj₁ Ain₁ with zero P Az (next Ain₁)
... | B , here , Bt = _ , split-in-l p here , fork-l Bt
... | B , next Bin , Bt = B , split-in-r p (split-in-l q Bin) , Bt
zero (fork p q P Q) Az Ain | inj₂ Ain' | inj₂ Ain₂ with zero Q Az (next Ain₂)
... | B , here , Bt = _ , split-in-l p here , fork-r Bt
... | B , next Bin , Bt = B , split-in-r p (split-in-r q Bin) , Bt
zero (join p P) Az Ain with in-split Ain p
zero (join p P) (join-l Az) Ain | inj₁ here with zero P Az (next here)
... | B , here , Bt = _ , split-in-l p here , join-r Bt
... | B , next here , Bt = _ , split-in-l p here , join-l Bt
... | B , next (next Bin) , Bt = B , split-in-r p Bin , Bt
zero (join p P) (join-r Az) Ain | inj₁ here with zero P Az here
... | B , here , Bt = _ , Ain , join-r Bt
... | B , next here , Bt = _ , Ain , join-l Bt
... | B , next (next Bin) , Bt = B , split-in-r p Bin , Bt
zero (join p P) (join-r Az) Ain | inj₁ (next ())
zero (join p P) Az Ain | inj₂ Ain' with zero P Az (next (next Ain'))
... | B , here , Bt = _ , split-in-l p here , join-r Bt
... | B , next here , Bt = _ , split-in-l p here , join-l Bt
... | B , next (next Bin) , Bt = B , split-in-r p Bin , Bt
zero (cut d p P Q) Az Ain with in-split Ain p
zero (cut d p P Q) Az Ain | inj₁ Ain₁ with zero P Az (next Ain₁)
... | B , next Bin , Bt = B , split-in-l p Bin , Bt
... | B , here , Bt with zero Q (dual-top d Bt) here
... | C , next Cin , Ct = C , split-in-r p Cin , Ct
... | C , here , Ct = contradiction (Bt , Ct) (top-top d)
zero (cut d p P Q) Az Ain | inj₂ Ain₂ with zero Q Az (next Ain₂)
... | B , next Bin , Bt = B , split-in-r p Bin , Bt
... | B , here , Bt with zero P (dual-top (dual-symm d) Bt) here
... | C , next Cin , Ct = C , split-in-l p Cin , Ct
... | C , here , Ct = contradiction (Ct , Bt) (top-top d)

-- zero (link dual-zero-top (split-l (split-r split-e))) here = _ , next here , refl
-- zero (link dual-top-zero (split-l (split-r split-e))) (next here) = _ , here , refl
-- zero (link dual-top-zero (split-r (split-l split-e))) here = _ , next here , refl
-- zero (link dual-zero-top (split-r (split-l split-e))) (next here) = _ , here , refl
-- zero (fail p) x = {!!}
-- zero (close p) x = {!!}
-- zero (wait p P) x = {!!}
-- zero (select b p P) x with in-split x p
-- ... | inj₁ (next ())
-- zero (select false p P) x | inj₂ r with zero P (next r)
-- ... | A , here , t = _ , split-in-l p here , plus-r t
-- ... | A , next y , t = _ , split-in-r p y , t
-- zero (select true p P) x | inj₂ r = {!!}
-- zero (branch p P Q) x with in-split x p
-- ... | inj₁ (next ())
-- ... | inj₂ y with zero P (next y) | zero Q (next y)
-- ... | A , here , at | B , here , bt = _ , split-in-l p here , with-b at bt
-- ... | A , here , at | B , next b , bt = _ , split-in-r p b , bt
-- ... | A , next a , at | B , b , bt = _ , split-in-r p a , at
-- zero (fork p q P Q) x = {!!}
-- zero (join p P) x = {!!}
-- zero (cut d p P Q) x with in-split x p
-- zero (cut d p P Q) x | inj₁ y with zero P (next y)
-- ... | A , next a , at = A , split-in-l p a , at
-- ... | A , here , t = {!!}
-- zero (cut d p P Q) x | inj₂ y = {!!}
