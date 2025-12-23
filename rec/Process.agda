{-# OPTIONS --rewriting #-}
open import Data.Unit using (tt)
open import Data.Sum
open import Data.Product using (_,_)
open import Data.List.Base using (List; []; _∷_; [_])
open import Relation.Unary hiding (_∈_)

open import Type
open import Context
open import Permutations

ProcContext : Set
ProcContext = List Context

data _∈_ (Γ : Context) : ProcContext → Set where
  here : ∀{Σ} → Γ ∈ (Γ ∷ Σ)
  next : ∀{Δ Σ} → Γ ∈ Σ → Γ ∈ (Δ ∷ Σ)

data Ch (A : Type) : Context → Set where
  ch : Ch A [ A ]

data PreProc : ProcContext → Context → Set where
  call     : ∀{Δ Σ} → Δ ∈ Σ → ∀[ Δ ↭_ ⇒ PreProc Σ ]
  rec      : ∀{Δ Σ} → PreProc (Δ ∷ Σ) Δ → ∀[ Δ ↭_ ⇒ PreProc Σ ]
  link     : ∀{A Σ} → ∀[ Ch A ∗ Ch (dual A) ⇒ PreProc Σ ]
  fail     : ∀{Σ} → ∀[ Ch ⊤ ∗ U ⇒ PreProc Σ ]
  wait     : ∀{Σ} → ∀[ Ch ⊥ ∗ PreProc Σ ⇒ PreProc Σ ]
  close    : ∀{Σ} → ∀[ Ch 𝟙 ⇒ PreProc Σ ]
  case     : ∀{A B Σ} → ∀[ Ch (A & B) ∗ ((A ∷_) ⊢ PreProc Σ ∩ (B ∷_) ⊢ PreProc Σ) ⇒ PreProc Σ ]
  select   : ∀{A B Σ} → ∀[ Ch (A ⊕ B) ∗ ((A ∷_) ⊢ PreProc Σ ∪ (B ∷_) ⊢ PreProc Σ) ⇒ PreProc Σ ]
  join     : ∀{A B Σ} → ∀[ Ch (A ⅋ B) ∗ ((A ∷_) ⊢ (B ∷_) ⊢ PreProc Σ) ⇒ PreProc Σ ]
  fork     : ∀{A B Σ} → ∀[ Ch (A ⊗ B) ∗ ((A ∷_) ⊢ PreProc Σ) ∗ ((B ∷_) ⊢ PreProc Σ) ⇒ PreProc Σ ]
  all      : ∀{A Σ} → ∀[ Ch (`∀ A) ∗ ⋂[ X ∶ Type ] ((subst [ X /] A ∷_) ⊢ PreProc Σ) ⇒ PreProc Σ ]
  ex       : ∀{A B Σ} → ∀[ Ch (`∃ A) ∗ ((subst [ B /] A ∷_) ⊢ PreProc Σ) ⇒ PreProc Σ ]
  server   : ∀{A Σ} → ∀[ Ch (`! A) ∗ (Un ∩ ((A ∷_) ⊢ PreProc Σ)) ⇒ PreProc Σ ]
  client   : ∀{A Σ} → ∀[ Ch (`? A) ∗ ((A ∷_) ⊢ PreProc Σ) ⇒ PreProc Σ ]
  weaken   : ∀{A Σ} → ∀[ Ch (`? A) ∗ PreProc Σ ⇒ PreProc Σ ]
  contract : ∀{A Σ} → ∀[ Ch (`? A) ∗ ((`? A ∷_) ⊢ (`? A ∷_) ⊢ PreProc Σ) ⇒ PreProc Σ ]
  cut      : ∀{A Σ} → ∀[ ((A ∷_) ⊢ PreProc Σ) ∗ ((dual A ∷_) ⊢ PreProc Σ) ⇒ PreProc Σ ]

ProcEnv : ProcContext → Set
ProcEnv Σ = ∀{Γ} → Γ ∈ Σ → PreProc Σ Γ

↭proc : ∀{Γ Δ Σ} → Γ ↭ Δ → PreProc Σ Γ → PreProc Σ Δ
↭proc π (call x π') = call x (trans π' π)
↭proc π (rec P π') = rec P (trans π' π)
↭proc π (link (ch ⟨ p ⟩ ch)) with ↭solo π p
... | _ , q , π' rewrite ↭solo-inv π' = link (ch ⟨ q ⟩ ch)
↭proc π (fail (ch ⟨ p ⟩ tt)) with ↭solo π p
... | _ , q , π' = fail (ch ⟨ q ⟩ tt)
↭proc π (wait (ch ⟨ p ⟩ P)) with ↭solo π p
... | _ , q , π' = wait (ch ⟨ q ⟩ ↭proc π' P)
↭proc π (close ch) rewrite ↭solo-inv π = close ch
↭proc π (case (ch ⟨ p ⟩ (P , Q))) with ↭solo π p
... | _ , q , π' = case (ch ⟨ q ⟩ (↭proc (prep π') P , ↭proc (prep π') Q))
↭proc π (select (ch ⟨ p ⟩ inj₁ P)) with ↭solo π p
... | _ , q , π' = select (ch ⟨ q ⟩ inj₁ (↭proc (prep π') P))
↭proc π (select (ch ⟨ p ⟩ inj₂ P)) with ↭solo π p
... | _ , q , π' = select (ch ⟨ q ⟩ inj₂ (↭proc (prep π') P))
↭proc π (join (ch ⟨ p ⟩ P)) with ↭solo π p
... | _ , q , π' = join (ch ⟨ q ⟩ ↭proc (prep (prep π')) P)
↭proc π (fork (ch ⟨ p ⟩ (P ⟨ q ⟩ Q))) with ↭solo π p
... | _ , p' , π' with ↭split π' q
... | Δ₁ , Δ₂ , q' , π₁ , π₂ = fork (ch ⟨ p' ⟩ (↭proc (prep π₁) P ⟨ q' ⟩ ↭proc (prep π₂) Q))
↭proc π (all (ch ⟨ p ⟩ F)) with ↭solo π p
... | _ , q , π' = all (ch ⟨ q ⟩ λ X → ↭proc (prep π') (F X))
↭proc π (ex (ch ⟨ p ⟩ P)) with ↭solo π p
... | _ , q , π' = ex (ch ⟨ q ⟩ ↭proc (prep π') P)
↭proc π (server (ch ⟨ p ⟩ (un , P))) with ↭solo π p
... | _ , q , π' = server (ch ⟨ q ⟩ (↭un π' un , ↭proc (prep π') P))
↭proc π (client (ch ⟨ p ⟩ P)) with ↭solo π p
... | _ , q , π' = client (ch ⟨ q ⟩ ↭proc (prep π') P)
↭proc π (weaken (ch ⟨ p ⟩ P)) with ↭solo π p
... | _ , q , π' = weaken (ch ⟨ q ⟩ ↭proc π' P)
↭proc π (contract (ch ⟨ p ⟩ P)) with ↭solo π p
... | _ , q , π' = contract (ch ⟨ q ⟩ ↭proc (prep (prep π')) P)
↭proc π (cut (P ⟨ p ⟩ Q)) with ↭split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = cut (↭proc (prep π₁) P ⟨ q ⟩ ↭proc (prep π₂) Q)

Ext : ∀{Γ Σ Σ'} → (∀{Δ} → Δ ∈ Σ → Δ ∈ Σ') → ∀{Δ} → Δ ∈ (Γ ∷ Σ) → Δ ∈ (Γ ∷ Σ')
Ext ρ here = here
Ext ρ (next x) = next (ρ x)

Rename : ∀{Γ Σ Σ'} → (∀{Δ} → Δ ∈ Σ → Δ ∈ Σ') → PreProc Σ Γ → PreProc Σ' Γ
Rename ρ (call x π) = call (ρ x) π
Rename ρ (rec P π) = rec (Rename (Ext ρ) P) π
Rename ρ (link x) = link x
Rename ρ (fail x) = fail x
Rename ρ (wait (ch ⟨ σ ⟩ P)) = wait (ch ⟨ σ ⟩ Rename ρ P)
Rename ρ (close ch) = close ch
Rename ρ (case (ch ⟨ p ⟩ (P , Q))) = case (ch ⟨ p ⟩ (Rename ρ P , Rename ρ Q))
Rename ρ (select (ch ⟨ p ⟩ inj₁ P)) = select (ch ⟨ p ⟩ inj₁ (Rename ρ P))
Rename ρ (select (ch ⟨ p ⟩ inj₂ P)) = select (ch ⟨ p ⟩ inj₂ (Rename ρ P))
Rename ρ (join (ch ⟨ p ⟩ P)) = join (ch ⟨ p ⟩ Rename ρ P)
Rename ρ (fork (ch ⟨ p ⟩ (P ⟨ q ⟩ Q))) = fork (ch ⟨ p ⟩ (Rename ρ P ⟨ q ⟩ Rename ρ Q))
Rename ρ (all (ch ⟨ σ ⟩ F)) = all (ch ⟨ σ ⟩ λ X → Rename ρ (F X))
Rename ρ (ex (ch ⟨ p ⟩ P)) = ex (ch ⟨ p ⟩ Rename ρ P)
Rename ρ (server (ch ⟨ p ⟩ (un , P))) = server (ch ⟨ p ⟩ (un , Rename ρ P))
Rename ρ (client (ch ⟨ p ⟩ P)) = client (ch ⟨ p ⟩ Rename ρ P)
Rename ρ (weaken (ch ⟨ p ⟩ P)) = weaken (ch ⟨ p ⟩ Rename ρ P)
Rename ρ (contract (ch ⟨ p ⟩ P)) = contract (ch ⟨ p ⟩ Rename ρ P)
Rename ρ (cut (P ⟨ σ ⟩ Q)) = cut (Rename ρ P ⟨ σ ⟩ Rename ρ Q)

Exts : ∀{Γ Σ Σ'} → (∀{Δ} → Δ ∈ Σ → PreProc Σ' Δ) → ∀{Δ} → Δ ∈ (Γ ∷ Σ) → PreProc (Γ ∷ Σ') Δ
Exts σ here = call here refl
Exts σ (next x) = Rename next (σ x)

Subst : ∀{Γ Σ Σ'} → (∀{Δ} → Δ ∈ Σ → PreProc Σ' Δ) → PreProc Σ Γ → PreProc Σ' Γ
Subst σ (call x π) = ↭proc π (σ x)
Subst σ (rec P π) = rec (Subst (Exts σ) P) π
Subst σ (link x) = link x
Subst σ (fail x) = fail x
Subst σ (wait (ch ⟨ p ⟩ P)) = wait (ch ⟨ p ⟩ Subst σ P)
Subst σ (close ch) = close ch
Subst σ (case (ch ⟨ p ⟩ (P , Q))) = case (ch ⟨ p ⟩ (Subst σ P , Subst σ Q))
Subst σ (select (ch ⟨ p ⟩ inj₁ P)) = select (ch ⟨ p ⟩ inj₁ (Subst σ P))
Subst σ (select (ch ⟨ p ⟩ inj₂ P)) = select (ch ⟨ p ⟩ inj₂ (Subst σ P))
Subst σ (join (ch ⟨ p ⟩ P)) = join (ch ⟨ p ⟩ Subst σ P)
Subst σ (fork (ch ⟨ p ⟩ (P ⟨ q ⟩ Q))) = fork (ch ⟨ p ⟩ (Subst σ P ⟨ q ⟩ Subst σ Q))
Subst σ (all (ch ⟨ p ⟩ F)) = all (ch ⟨ p ⟩ λ X → Subst σ (F X))
Subst σ (ex (ch ⟨ p ⟩ P)) = ex (ch ⟨ p ⟩ Subst σ P)
Subst σ (server (ch ⟨ p ⟩ (un , P))) = server (ch ⟨ p ⟩ (un , Subst σ P))
Subst σ (client (ch ⟨ p ⟩ P)) = client (ch ⟨ p ⟩ Subst σ P)
Subst σ (weaken (ch ⟨ p ⟩ P)) = weaken (ch ⟨ p ⟩ Subst σ P)
Subst σ (contract (ch ⟨ p ⟩ P)) = contract (ch ⟨ p ⟩ Subst σ P)
Subst σ (cut (P ⟨ p ⟩ Q)) = cut (Subst σ P ⟨ p ⟩ Subst σ Q)

Sing : ∀{Γ Σ} → PreProc Σ Γ → ∀{Δ} → Δ ∈ (Γ ∷ Σ) → PreProc Σ Δ
Sing P here = P
Sing P (next x) = call x refl

Unfold : ∀{Δ Σ} → PreProc (Δ ∷ Σ) Δ → PreProc Σ Δ
Unfold P = Subst (Sing (rec P refl)) P

Proc : Context → Set
Proc = PreProc []
