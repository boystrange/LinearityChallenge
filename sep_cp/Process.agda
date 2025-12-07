{-# OPTIONS --rewriting #-}
open import Data.Unit using (tt)
open import Data.Sum
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Type
open import Context
open import Permutations

record _∗_ (P Q : Pred Context _) (Γ : Context) : Set where
  constructor _⟨_⟩_
  field
    {Δ Θ} : Context
    px    : P Δ
    p     : Γ ≃ Δ + Θ
    qx    : Q Θ

infixr 50 _∗_

data Ch (A : Type) : Context → Set where
  ch : Ch A [ A ]

data Process : Context → Set where
  link     : ∀{A} → ∀[ Ch A ∗ Ch (dual A) ⇒ Process ]
  fail     : ∀[ Ch ⊤ ∗ U ⇒ Process ]
  wait     : ∀[ Ch ⊥ ∗ Process ⇒ Process ]
  close    : ∀[ Ch 𝟙 ⇒ Process ]
  case     : ∀{A B} → ∀[ Ch (A & B) ∗ ((A ∷_) ⊢ Process ∩ (B ∷_) ⊢ Process) ⇒ Process ]
  select   : ∀{A B} → ∀[ Ch (A ⊕ B) ∗ ((A ∷_) ⊢ Process ∪ (B ∷_) ⊢ Process) ⇒ Process ]
  join     : ∀{A B} → ∀[ Ch (A ⅋ B) ∗ ((A ∷_) ⊢ (B ∷_) ⊢ Process) ⇒ Process ]
  fork     : ∀{A B} → ∀[ Ch (A ⊗ B) ∗ ((A ∷_) ⊢ Process) ∗ ((B ∷_) ⊢ Process) ⇒ Process ]
  all      : ∀{A} → ∀[ Ch (`∀ A) ∗ (⋂[ X ∶ Type ] ((subst [ X /_] A ∷_) ⊢ Process)) ⇒ Process ]
  ex       : ∀{A B} → ∀[ Ch (`∃ A) ∗ ((subst [ B /_] A ∷_) ⊢ Process) ⇒ Process ]
  server   : ∀{A} → ∀[ Ch (`! A) ∗ (Un ∩ ((A ∷_) ⊢ Process)) ⇒ Process ]
  client   : ∀{A} → ∀[ Ch (`? A) ∗ ((A ∷_) ⊢ Process) ⇒ Process ]
  weaken   : ∀{A} → ∀[ Ch (`? A) ∗ Process ⇒ Process ]
  contract : ∀{A} → ∀[ Ch (`? A) ∗ ((`? A ∷_) ⊢ (`? A ∷_) ⊢ Process) ⇒ Process ]
  cut      : ∀{A} → ∀[ ((A ∷_) ⊢ Process) ∗ ((dual A ∷_) ⊢ Process) ⇒ Process ]

↭process : ∀{Γ Δ} → Γ ↭ Δ → Process Γ → Process Δ
↭process π (link (ch ⟨ p ⟩ ch)) with ↭solo π p
... | _ , q , π' rewrite ↭solo-inv π' = link (ch ⟨ q ⟩ ch)
↭process π (fail (ch ⟨ p ⟩ tt)) with ↭solo π p
... | _ , q , π' = fail (ch ⟨ q ⟩ tt)
↭process π (wait (ch ⟨ p ⟩ P)) with ↭solo π p
... | _ , q , π' = wait (ch ⟨ q ⟩ ↭process π' P)
↭process π (close ch) rewrite ↭solo-inv π = close ch
↭process π (case (ch ⟨ p ⟩ (P , Q))) with ↭solo π p
... | _ , q , π' = case (ch ⟨ q ⟩ (↭process (prep π') P , ↭process (prep π') Q))
↭process π (select (ch ⟨ p ⟩ inj₁ P)) with ↭solo π p
... | _ , q , π' = select (ch ⟨ q ⟩ inj₁ (↭process (prep π') P))
↭process π (select (ch ⟨ p ⟩ inj₂ P)) with ↭solo π p
... | _ , q , π' = select (ch ⟨ q ⟩ inj₂ (↭process (prep π') P))
↭process π (join (ch ⟨ p ⟩ P)) with ↭solo π p
... | _ , q , π' = join (ch ⟨ q ⟩ ↭process (prep (prep π')) P)
↭process π (fork (ch ⟨ p ⟩ (P ⟨ q ⟩ Q))) with ↭solo π p
... | Δ' , p' , π' with ↭split π' q
... | Δ₁ , Δ₂ , q' , π₁ , π₂ = fork (ch ⟨ p' ⟩ (↭process (prep π₁) P ⟨ q' ⟩ ↭process (prep π₂) Q))
↭process π (all (ch ⟨ p ⟩ F)) with ↭solo π p
... | Δ' , q , π' = all (ch ⟨ q ⟩ λ X → ↭process (prep π') (F X))
↭process π (ex (ch ⟨ p ⟩ P)) with ↭solo π p
... | Δ' , q , π' = ex (ch ⟨ q ⟩ ↭process (prep π') P)
↭process π (server (ch ⟨ p ⟩ (un , P))) with ↭solo π p
... | Δ' , q , π' = server (ch ⟨ q ⟩ (↭un π' un , ↭process (prep π') P))
↭process π (client (ch ⟨ p ⟩ P)) with ↭solo π p
... | Δ' , q , π' = client (ch ⟨ q ⟩ ↭process (prep π') P)
↭process π (weaken (ch ⟨ p ⟩ P)) with ↭solo π p
... | Δ' , q , π' = weaken (ch ⟨ q ⟩ ↭process π' P)
↭process π (contract (ch ⟨ p ⟩ P)) with ↭solo π p
... | Δ' , q , π' = contract (ch ⟨ q ⟩ ↭process (prep (prep π')) P)
↭process π (cut (P ⟨ p ⟩ Q)) with ↭split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = cut (↭process (prep π₁) P ⟨ q ⟩ ↭process (prep π₂) Q)
