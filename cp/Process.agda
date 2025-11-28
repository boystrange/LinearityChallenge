{-# OPTIONS --rewriting #-}
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)

open import Type
open import Context
open import Permutations

data Process : Context → Set where
   link      : ∀{Γ A} (p : Γ ≃ [ A ] + [ dual A ]) → Process Γ
   fail      : ∀{Γ Δ} (p : Γ ≃ ⊤ , Δ) → Process Γ
   close     : Process  [ 𝟙 ]
   wait      : ∀{Γ Δ} (p : Γ ≃ ⊥ , Δ) → Process Δ → Process Γ
   select    : ∀{A B Γ Δ} (x : Bool) (p : Γ ≃ A ⊕ B , Δ) →
               Process ((if x then A else B) ∷ Δ) → Process Γ
   case      : ∀{A B Γ Δ} (p : Γ ≃ A & B , Δ) →
               Process (A ∷ Δ) → Process (B ∷ Δ) → Process Γ
   fork      : ∀{A B Γ Δ Γ₁ Γ₂} (p : Γ ≃ A ⊗ B , Δ) (q : Δ ≃ Γ₁ + Γ₂) →
               Process (A ∷ Γ₁) → Process (B ∷ Γ₂) → Process Γ
   join      : ∀{A B Γ Δ} (p : Γ ≃ A ⅋ B , Δ) →
               Process (B ∷ A ∷ Δ) → Process Γ
   server    : ∀{A Γ Δ} (p : Γ ≃ `! A , Δ) (un : Un Δ) →
               Process (A ∷ Δ) → Process Γ
   client    : ∀{A Γ Δ} (p : Γ ≃ `? A , Δ) → Process (A ∷ Δ) → Process Γ
   weaken    : ∀{A Γ Δ} (p : Γ ≃ `? A , Δ) → Process Δ → Process Γ
   contract  : ∀{A Γ Δ} (p : Γ ≃ `? A , Δ) → Process (`? A ∷ `? A ∷ Δ) → Process Γ
   ex        : ∀{A B Γ Δ} (p : Γ ≃ `∃ A , Δ) ->
               Process (subst (make-subst B) A ∷ Δ) -> Process Γ
   all       : ∀{A Γ Δ} (p : Γ ≃ `∀ A , Δ) ->
               ((B : Type) -> Process (subst (make-subst B) A ∷ Δ)) -> Process Γ
   cut       : ∀{A Γ Γ₁ Γ₂} (p : Γ ≃ Γ₁ + Γ₂) →
               Process (A ∷ Γ₁) → Process (dual A ∷ Γ₂) → Process Γ

#process : ∀{Γ Δ} → Γ # Δ → Process Γ → Process Δ
#process π (link p) with #one+ π p
... | Δ′ , q , π′ with #singleton-inv π′
... | refl = link q
#process π close with #singleton-inv π
... | refl = close
#process π (fail p) with #one+ π p
... | Δ′ , q , π′ = fail q
#process π (wait p P) with #one+ π p
... | Δ′ , q , π′ = wait q (#process π′ P)
#process π (select x p P) with #one+ π p
... | Δ′ , q , π′ = select x q (#process (#next π′) P)
#process π (case p P Q) with #one+ π p
... | Δ′ , q , π′ = case q (#process (#next π′) P) (#process (#next π′) Q)
#process π (fork p q P Q) with #one+ π p
... | Δ′ , p′ , π′ with #split π′ q
... | Δ₁ , Δ₂ , q′ , π₁ , π₂ = fork p′ q′ (#process (#next π₁) P) (#process (#next π₂) Q)
#process π (join p P) with #one+ π p
... | Δ′ , q , π′ = join q (#process (#next (#next π′)) P)
#process π (cut p P Q) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = cut q (#process (#next π₁) P) (#process (#next π₂) Q)
#process π (server p un P) with #one+ π p
... | Δ′ , q , π′ = server q (#un π′ un) (#process (#next π′) P)
#process π (client p P) with #one+ π p
... | Δ′ , q , π′ = client q (#process (#next π′) P)
#process π (weaken p P) with #one+ π p
... | Δ′ , q , π′ = weaken q (#process π′ P)
#process π (contract p P) with #one+ π p
... | Δ′ , q , π′ = contract q (#process (#next (#next π′)) P)
#process π (all p P) with #one+ π p
... | Δ' , q , π' = all q λ B → #process (#next π') (P B)
#process π (ex p P) with #one+ π p
... | Δ' , q , π' = ex q (#process (#next π') P)
