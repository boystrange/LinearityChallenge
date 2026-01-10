{-# OPTIONS --rewriting --guardedness #-}
open import Relation.Binary.PropositionalEquality using (_≡_)

postulate
  extensionality : ∀{A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
