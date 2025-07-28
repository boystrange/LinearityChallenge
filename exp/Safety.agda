open import Data.Sum
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_; contradiction)
open import Data.List.Base using ([]; _∷_; [_])

open import Type
open import Context
open import Process
open import Congruence
open import Reduction
open import DeadlockFreedom

Action : ∀{Γ} → Process Γ → Set
Action P = Input P ⊎ Output P ⊎ Client P ⊎ Server P

data ActionCut {Γ} : Process Γ → Set where
  action-cut :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A ∷ Γ₁)} {Q : Process (B ∷ Γ₂)} →
    Action P → Action Q → ActionCut (cut d p P Q)

data ReductionContext (Δ : Context) : Context → Set where
  hole  : ReductionContext Δ Δ
  cut-l : ∀{Γ Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) →
          ReductionContext Δ (A ∷ Γ₁) → Process (B ∷ Γ₂) →
          ReductionContext Δ Γ
  cut-r : ∀{Γ Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) →
          Process (A ∷ Γ₁) → ReductionContext Δ (B ∷ Γ₂) →
          ReductionContext Δ Γ

_⟦_⟧ : ∀{Γ Δ} → ReductionContext Δ Γ → Process Δ → Process Γ
hole ⟦ P ⟧ = P
cut-l d p C Q ⟦ P ⟧ = cut d p (C ⟦ P ⟧) Q
cut-r d p Q C ⟦ P ⟧ = cut d p Q (C ⟦ P ⟧)

TypeSafe : ∀{Γ} → Process Γ → Set
TypeSafe {Γ} P =
  ∀{Δ} {C : ReductionContext Δ Γ} {Q : Process Δ} →
  ActionCut Q → P ⊒ (C ⟦ Q ⟧) → Reducible Q

action-⊒ : ∀{Γ} {P Q : Process Γ} → P ⊒ Q → Action P → Action Q
action-⊒ (s-comm d p) (inj₂ (inj₂ (inj₁ ())))
action-⊒ s-refl Pa = Pa
action-⊒ (s-tran pc pc′) Pa = action-⊒ pc′ (action-⊒ pc Pa)

action-cut-⊒ : ∀{Γ} {P Q : Process Γ} → P ⊒ Q → ActionCut P → ActionCut Q
action-cut-⊒ (s-fail .d .p q)    (action-cut d p (inj₂ (inj₂ (inj₁ ()))) Qa)
action-cut-⊒ (s-comm .d .p) (action-cut d p Pa Qa) = action-cut (dual-symm d) (+-comm p) Qa Pa
action-cut-⊒ s-refl ac = ac
action-cut-⊒ (s-tran pc pc′) ac = action-cut-⊒ pc′ (action-cut-⊒ pc ac)
action-cut-⊒ (s-cong .d .p pc qc) (action-cut d p Pa Qa) = action-cut d p (action-⊒ pc Pa) (action-⊒ qc Qa)

action-cut-¬thread : ∀{Γ} {P : Process Γ} → ActionCut P → ¬ Thread P
action-cut-¬thread (action-cut d p Pa Qa) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ ()))))))
action-cut-¬thread (action-cut d p Pa Qa) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ ()))))))

action-cut-¬observable : ∀{Γ} {P : Process Γ} → ActionCut P → ¬ Observable P
action-cut-¬observable ac (R , Rcong , Rt) = action-cut-¬thread (action-cut-⊒ Rcong ac) Rt

type-safety : ∀{Γ} (P : Process Γ) → TypeSafe P
type-safety P {_} {_} {Q} ac pc with live Q
... | inj₁ obs = contradiction obs (action-cut-¬observable ac)
... | inj₂ red = red
