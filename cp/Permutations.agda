{-# OPTIONS --rewriting #-}
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)

open import Type
open import Context

data _#_ : Context → Context → Set where
  #refl  : ∀{Γ} → Γ # Γ
  #here  : ∀{A B Γ} → (A ∷ B ∷ Γ) # (B ∷ A ∷ Γ)
  #next  : ∀{A Γ Δ} → Γ # Δ → (A ∷ Γ) # (A ∷ Δ)
  #tran  : ∀{Γ Δ Θ} → Γ # Δ → Δ # Θ → Γ # Θ

#sym : ∀{Γ Δ} → Γ # Δ → Δ # Γ
#sym #refl = #refl
#sym #here = #here
#sym (#next π) = #next (#sym π)
#sym (#tran π π′) = #tran (#sym π′) (#sym π)

#empty-inv : ∀{Γ} → [] # Γ → Γ ≡ []
#empty-inv #refl = refl
#empty-inv (#tran π π′) rewrite #empty-inv π | #empty-inv π′ = refl

#singleton-inv : ∀{A Γ} → [ A ] # Γ → Γ ≡ [ A ]
#singleton-inv {Γ = Γ} #refl = refl
#singleton-inv {Γ = Γ} (#next π) rewrite #empty-inv π = refl
#singleton-inv {Γ = Γ} (#tran π π′) rewrite #singleton-inv π | #singleton-inv π′ = refl

#rot : ∀{A B C Γ} → (A ∷ B ∷ C ∷ Γ) # (C ∷ A ∷ B ∷ Γ)
#rot = #tran (#next #here) #here

#cons : ∀{A Γ Δ} → Γ ≃ A , Δ → (A ∷ Δ) # Γ
#cons (split-l p) with +-empty-l p
... | refl = #refl
#cons (split-r p) = #tran #here (#next (#cons p))

#split : ∀{Γ Γ₁ Γ₂ Δ} → Γ # Δ → Γ ≃ Γ₁ + Γ₂ → ∃[ Δ₁ ] ∃[ Δ₂ ] (Δ ≃ Δ₁ + Δ₂ × Γ₁ # Δ₁ × Γ₂ # Δ₂)
#split #refl p = _ , _ , p , #refl , #refl
#split (#next π) (split-l p) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = _ ∷ Δ₁ , Δ₂ , split-l q , #next π₁ , π₂
#split (#next π) (split-r p) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = Δ₁ , _ ∷ Δ₂ , split-r q , π₁ , #next π₂
#split #here (split-l (split-l p)) = _ , _ , split-l (split-l p) , #here , #refl
#split #here (split-l (split-r p)) = _ , _ , split-r (split-l p) , #refl , #refl
#split #here (split-r (split-l p)) = _ , _ , split-l (split-r p) , #refl , #refl
#split #here (split-r (split-r p)) = _ , _ , split-r (split-r p) , #refl , #here
#split (#tran π π′) p with #split π p
... | Θ₁ , Θ₂ , p′ , π₁ , π₂ with #split π′ p′
... | Δ₁ , Δ₂ , q , π₁′ , π₂′ = Δ₁ , Δ₂ , q , #tran π₁ π₁′ , #tran π₂ π₂′

#one+ : ∀{A Γ Γ′ Δ} → Γ # Δ → Γ ≃ A , Γ′ → ∃[ Δ′ ] (Δ ≃ A , Δ′ × Γ′ # Δ′)
#one+ π p with #split π p
... | _ , _ , q , π₁ , π₂ rewrite #singleton-inv π₁ = _ , q , π₂

#shift : ∀{A Γ Δ} → (Γ ++ A ∷ Δ) # (A ∷ Γ ++ Δ)
#shift {_} {[]} = #refl
#shift {_} {B ∷ Γ} = #tran (#next #shift) #here

+++# : ∀{Γ Γ₁ Γ₂} → Γ ≃ Γ₁ + Γ₂ → (Γ₁ ++ Γ₂) # Γ
+++# split-e = #refl
+++# (split-l p) = #next (+++# p)
+++# (split-r p) = #tran #shift (#next (+++# p))

#left : ∀{Γ Δ Θ} → Γ # Δ → (Θ ++ Γ) # (Θ ++ Δ)
#left {Θ = []} π = π
#left {Θ = _ ∷ Θ} π = #next (#left π)

#un : ∀{Γ Δ} → Γ # Δ → Un Γ → Un Δ
#un #refl un = un
#un (#next π) (un-∷ un) = un-∷ (#un π un)
#un #here (un-∷ (un-∷ un)) = un-∷ (un-∷ un)
#un (#tran π π′) un = #un π′ (#un π un)

#un+ : ∀{Γ Γ₁ Γ₂} → Γ ≃ Γ₁ + Γ₂ → Un Γ₁ → Un Γ₂ → Un Γ
#un+ split-e un-[] un-[] = un-[]
#un+ (split-l p) (un-∷ un₁) un₂ = un-∷ (#un+ p un₁ un₂)
#un+ (split-r p) un₁ (un-∷ un₂) = un-∷ (#un+ p un₁ un₂)
