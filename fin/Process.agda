-- MIT License

-- Copyright (c) 2024 Luca Padovani & Claudia Raffaelli

-- Permission is hereby granted, free of charge, to any person
-- obtaining a copy of this software and associated documentation
-- files (the "Software"), to deal in the Software without
-- restriction, including without limitation the rights to use,
-- copy, modify, merge, publish, distribute, sublicense, and/or sell
-- copies of the Software, and to permit persons to whom the
-- Software is furnished to do so, subject to the following
-- conditions:

-- The above copyright notice and this permission notice shall be
-- included in all copies or substantial portions of the Software.

-- THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
-- EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
-- OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
-- NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
-- HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
-- WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
-- FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
-- OTHER DEALINGS IN THE SOFTWARE.

module Process where

open import Data.Bool using (Bool; if_then_else_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product using (Σ; _×_; _,_; ∃; Σ-syntax; ∃-syntax)

open import Type
open import Context

data Process (Γ : Context) : Set where
   Close : Γ ≃ [ One ] + [] -> Process Γ
   Link  : ∀{A B}
           (d : Dual A B)
           (p : Γ ≃ [ A ] + [ B ])
           -> Process Γ
   Fail  : ∀{Δ}
           (p : Γ ≃ [ Top ] + Δ)
           -> Process Γ
   Wait  : ∀{Δ}
           (p : Γ ≃ [ Bot ] + Δ)
           -> Process Δ
           -> Process Γ
   Select : ∀{Δ A B}
            (x : Bool)
            (p : Γ ≃ [ A ⊕ B ] + Δ)
            -> Process ((if x then A else B) :: Δ)
            -> Process Γ
   Case  : ∀{Δ A B}
           (p : Γ ≃ [ A & B ] + Δ)
           -> Process (A :: Δ)
           -> Process (B :: Δ)
           -> Process Γ
   Fork  : ∀{Δ Γ₁ Γ₂ A B}
           (p : Γ ≃ [ A ⊗ B ] + Δ)
           (q : Δ ≃ Γ₁ + Γ₂)
           -> Process (A :: Γ₁)
           -> Process (B :: Γ₂)
           -> Process Γ
   Join  : ∀{Δ A B}
           (p : Γ ≃ [ A ⅋ B ] + Δ)
           -> Process (B :: A :: Δ)
           -> Process Γ
   Cut   : ∀{Γ₁ Γ₂ A B}
           (d : Dual A B)
           (p : Γ ≃ Γ₁ + Γ₂)
           -> Process (A :: Γ₁)
           -> Process (B :: Γ₂)
           -> Process Γ

#process : ∀{Γ Δ} -> Γ # Δ -> Process Γ -> Process Δ
#process π (Link d p) with #one+ π p
... | Δ' , q , π' with #one π'
... | refl = Link d q
#process π (Close p) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ with #one π₁ | #nil π₂
... | refl | refl = Close q
#process π (Fail p) with #one+ π p
... | Δ' , q , π' = Fail q
#process π (Wait p P) with #one+ π p
... | Δ' , q , π' = Wait q (#process π' P)
#process π (Select x p P) with #one+ π p
... | Δ' , q , π' = Select x q (#process (#next π') P)
#process π (Case p P Q) with #one+ π p
... | Δ' , q , π' = Case q (#process (#next π') P) (#process (#next π') Q)
#process π (Fork p q P Q) with #one+ π p
... | Δ' , p' , π' with #split π' q
... | Δ₁ , Δ₂ , q' , π₁ , π₂ = Fork p' q' (#process (#next π₁) P) (#process (#next π₂) Q)
#process π (Join p P) with #one+ π p
... | Δ' , q , π' = Join q (#process (#next (#next π')) P)
#process π (Cut d p P Q) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = Cut d q (#process (#next π₁) P) (#process (#next π₂) Q)
