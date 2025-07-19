open import Data.Bool using (Bool; if_then_else_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Product using (Σ; _×_; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.List.Base using ([]; _∷_; [_])
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; prep; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (++⁺ˡ; shift; ↭-empty-inv; ↭-singleton-inv)

open import Type
open import Context

data Process : Context -> Set where
   link :
     ∀{Γ A B} (d : Dual A B) (p : Γ ≃ [ A ] + [ B ]) -> Process Γ
   fail :
     ∀{Γ Δ} (p : Γ ≃ ⊤ , Δ) -> Process Γ
   close : Process [ 𝟙 ]
   wait :
     ∀{Γ Δ} (p : Γ ≃ ⊥ , Δ) -> Process Δ -> Process Γ
   select :
     ∀{Γ Δ A B} (x : Bool) (p : Γ ≃ A ⊕ B , Δ) ->
     Process ((if x then A else B) ∷ Δ) -> Process Γ
   case :
     ∀{Γ Δ A B} (p : Γ ≃ A & B , Δ) ->
     Process (A ∷ Δ) -> Process (B ∷ Δ) -> Process Γ
   fork :
     ∀{Γ Δ Γ₁ Γ₂ A B} (p : Γ ≃ A ⊗ B , Δ) (q : Δ ≃ Γ₁ + Γ₂) ->
     Process (A ∷ Γ₁) -> Process (B ∷ Γ₂) -> Process Γ
   join :
     ∀{Γ Δ A B} (p : Γ ≃ A ⅋ B , Δ) -> Process (B ∷ A ∷ Δ) -> Process Γ
   server :
     ∀{Γ Δ A} (p : Γ ≃ ¡ A , Δ) (un : Un Δ) -> Process (A ∷ Δ) -> Process Γ
   client :
     ∀{Γ Δ A} (p : Γ ≃ ¿ A , Δ) -> Process (A ∷ Δ) -> Process Γ
   weaken :
     ∀{Γ Δ A} (p : Γ ≃ ¿ A , Δ) -> Process Δ -> Process Γ
   contract :
     ∀{Γ Δ A} (p : Γ ≃ ¿ A , Δ) -> Process (¿ A ∷ ¿ A ∷ Δ) -> Process Γ
   cut :
     ∀{Γ Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) ->
     Process (A ∷ Γ₁) -> Process (B ∷ Γ₂) -> Process Γ

#process : ∀{Γ Δ} -> Γ # Δ -> Process Γ -> Process Δ
#process π (link d p) with #one+ π p
... | Δ' , q , π' with #singleton-inv π'
... | refl = link d q
#process π close with #singleton-inv π
... | refl = close
#process π (fail p) with #one+ π p
... | Δ' , q , π' = fail q
#process π (wait p P) with #one+ π p
... | Δ' , q , π' = wait q (#process π' P)
#process π (select x p P) with #one+ π p
... | Δ' , q , π' = select x q (#process (#next π') P)
#process π (case p P Q) with #one+ π p
... | Δ' , q , π' = case q (#process (#next π') P) (#process (#next π') Q)
#process π (fork p q P Q) with #one+ π p
... | Δ' , p' , π' with #split π' q
... | Δ₁ , Δ₂ , q' , π₁ , π₂ = fork p' q' (#process (#next π₁) P) (#process (#next π₂) Q)
#process π (join p P) with #one+ π p
... | Δ' , q , π' = join q (#process (#next (#next π')) P)
#process π (cut d p P Q) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = cut d q (#process (#next π₁) P) (#process (#next π₂) Q)
#process π (server p un P) with #one+ π p
... | Δ' , q , π' = server q (#un π' un) (#process (#next π') P)
#process π (client p P) with #one+ π p
... | Δ' , q , π' = client q (#process (#next π') P)
#process π (weaken p P) with #one+ π p
... | Δ' , q , π' = weaken q (#process π' P)
#process π (contract p P) with #one+ π p
... | Δ' , q , π' = contract q (#process (#next (#next π')) P)
