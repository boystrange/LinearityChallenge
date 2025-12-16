{-# OPTIONS --rewriting #-}
open import Data.Sum
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)

open import Type
open import Context
open import Permutations

data Process : Context → Set where
  link      : ∀{A Γ} → Γ ≃ [ A ] + [ dual A ] → Process Γ
  fail      : ∀{Γ Δ} → Γ ∋ ⊤ ⊳ Δ → Process Γ
  wait      : ∀{Γ Δ} → Γ ∋ ⊥ ⊳ Δ → Process Δ → Process Γ
  close     : Process [ 𝟙 ]
  case      : ∀{A B Γ Δ} → Γ ∋ A & B ⊳ Δ →
              Process (A ∷ Δ) → Process (B ∷ Δ) → Process Γ
  select    : ∀{A B Γ Δ} → Γ ∋ A ⊕ B ⊳ Δ → Process (A ∷ Δ) ⊎ Process (B ∷ Δ) → Process Γ
  join      : ∀{A B Γ Δ} → Γ ∋ A ⅋ B ⊳ Δ → Process (B ∷ A ∷ Δ) → Process Γ
  fork      : ∀{A B Γ Δ Γ₁ Γ₂} → Γ ∋ A ⊗ B ⊳ Δ → Δ ≃ Γ₁ + Γ₂ →
              Process (A ∷ Γ₁) → Process (B ∷ Γ₂) → Process Γ
  all       : ∀{A Γ Δ} → Γ ∋ `∀ A ⊳ Δ →
              ((X : Type) → Process (subst [ X /_] A ∷ Δ)) → Process Γ
  ex        : ∀{A B Γ Δ} → Γ ∋ `∃ A ⊳ Δ → Process (subst [ B /_] A ∷ Δ) → Process Γ
  server    : ∀{A Γ Δ} → Γ ∋ `! A ⊳ Δ → Un Δ → Process (A ∷ Δ) → Process Γ
  client    : ∀{A Γ Δ} → Γ ∋ `? A ⊳ Δ → Process (A ∷ Δ) → Process Γ
  weaken    : ∀{A Γ Δ} → Γ ∋ `? A ⊳ Δ → Process Δ → Process Γ
  contract  : ∀{A Γ Δ} → Γ ∋ `? A ⊳ Δ → Process (`? A ∷ `? A ∷ Δ) → Process Γ
  cut       : ∀{A Γ Γ₁ Γ₂} → Γ ≃ Γ₁ + Γ₂ →
              Process (A ∷ Γ₁) → Process (dual A ∷ Γ₂) → Process Γ

↭process : ∀{Γ Δ} → Γ ↭ Δ → Process Γ → Process Δ
↭process π (link p) with ↭solo π p
... | _ , q , π' rewrite ↭solo-inv π' = link q
↭process π (fail p) with ↭solo π p
... | _ , q , π' = fail q
↭process π (wait p P) with ↭solo π p
... | _ , q , π' = wait q (↭process π' P)
↭process π close rewrite ↭solo-inv π = close
↭process π (case p P Q) with ↭solo π p
... | _ , q , π' = case q (↭process (prep π') P) (↭process (prep π') Q)
↭process π (select p (inj₁ P)) with ↭solo π p
... | _ , q , π' = select q (inj₁ (↭process (prep π') P))
↭process π (select p (inj₂ P)) with ↭solo π p
... | _ , q , π' = select q (inj₂ (↭process (prep π') P))
↭process π (join p P) with ↭solo π p
... | _ , q , π' = join q (↭process (prep (prep π')) P)
↭process π (fork p q P Q) with ↭solo π p
... | _ , p' , π' with ↭split π' q
... | Δ₁ , Δ₂ , q' , π₁ , π₂ = fork p' q' (↭process (prep π₁) P) (↭process (prep π₂) Q)
↭process π (all p P) with ↭solo π p
... | _ , q , π' = all q λ B → ↭process (prep π') (P B)
↭process π (ex p P) with ↭solo π p
... | _ , q , π' = ex q (↭process (prep π') P)
↭process π (server p un P) with ↭solo π p
... | _ , q , π' = server q (↭un π' un) (↭process (prep π') P)
↭process π (client p P) with ↭solo π p
... | _ , q , π' = client q (↭process (prep π') P)
↭process π (weaken p P) with ↭solo π p
... | _ , q , π' = weaken q (↭process π' P)
↭process π (contract p P) with ↭solo π p
... | _ , q , π' = contract q (↭process (prep (prep π')) P)
↭process π (cut p P Q) with ↭split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = cut q (↭process (prep π₁) P) (↭process (prep π₂) Q)
