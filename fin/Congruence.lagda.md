# Structural Pre-Congruence

In this module we define a structural precongruence relation for
processes.

## Imports

```agda
open import Data.Bool using (Bool; if_then_else_)
open Bool using (true; false)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

open import Type
open import Context
open import Process
```

## Definition of Structural Pre-Congruence

```agda
data _⊒_ : ∀{Γ} -> Process Γ -> Process Γ -> Set where
  s-comm :
    ∀{Γ Γ₁ Γ₂ A B P Q} (d : Dual A B) (d' : Dual B A)
    (p : Γ ≃ Γ₁ + Γ₂) (p' : Γ ≃ Γ₂ + Γ₁) ->
    cut d p P Q ⊒ cut d' p' Q P

  s-assoc-r :
    ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A A' B B'}
    {P : Process (A :: Γ₁)}
    {Q : Process (B :: A' :: Δ₁)}
    {R : Process (B' :: Δ₂)}
    (d : Dual A A') (e : Dual B B')
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₂ ≃ Δ₁ + Δ₂)
    (p' : Δ ≃ Γ₁ + Δ₁) (q' : Γ ≃ Δ + Δ₂) ->
    cut d p P (cut e (split-l q) Q R) ⊒
    cut e q' (cut d (split-r p') P (#process #here Q)) R

  s-link :
    ∀{Γ A B}
    (d : Dual A B) (p : Γ ≃ [ A ] + [ B ]) ->
    link d p ⊒ link (dual-symm d) (+-comm p)

  s-fail :
    ∀{Γ Γ₁ Γ₂ Δ A B P} (d : Dual A B)
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ Top , Δ) ->
    let _ , _ , q' = +-assoc-l p q in
    cut d p (fail (split-r q)) P ⊒ fail q'

  s-wait :
    ∀{Γ Γ₁ Γ₂ Δ A B}
    {P : Process (A :: Δ)} {Q : Process (B :: Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ Bot , Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    cut d p (wait (split-r q) P) Q ⊒ wait q' (cut d p' P Q)

  s-select-l :
    ∀{Γ Γ₁ Γ₂ Δ A B C D}
    {P : Process (C :: A :: Δ)}
    {Q : Process (B :: Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ C ⊕ D , Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    cut d p (select true (split-r q) P) Q ⊒
    select true q' (cut d (split-l p') (#process #here P) Q)

  s-select-r :
    ∀{Γ Γ₁ Γ₂ Δ A B C D}
    {P : Process (D :: A :: Δ)}
    {Q : Process (B :: Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ C ⊕ D , Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    cut d p (select false (split-r q) P) Q ⊒
    select false q' (cut d (split-l p') (#process #here P) Q)

  s-case :
    ∀{Γ A B A₁ A₂ Γ₁ Γ₂ Δ}
    {P : Process (A₁ :: A :: Δ)}
    {Q : Process (A₂ :: A :: Δ)}
    {R : Process (B :: Γ₂)}
    (d : Dual A B)
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ A₁ & A₂ , Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    cut d p (case (split-r q) P Q) R ⊒
    case q' (cut d (split-l p') (#process #here P) R)
            (cut d (split-l p') (#process #here Q) R)

  s-fork-l :
    ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A B C D}
    {P : Process (C :: A :: Δ₁)}
    {Q : Process (D :: Δ₂)}
    {R : Process (B :: Γ₂)}
    (d : Dual A B)
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ C ⊗ D , Δ) (r : Δ ≃ Δ₁ + Δ₂) ->
    let _ , p' , q' = +-assoc-l p q in
    let _ , p'' , r' = +-assoc-l p' r in
    let _ , q'' , r'' = +-assoc-r r' (+-comm p'') in
    cut d p (fork (split-r q) (split-l r) P Q) R ⊒
    fork q' r'' (cut d (split-l q'') (#process #here P) R) Q

  s-fork-r :
    ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A B C D}
    {P : Process (C :: Δ₁)}
    {Q : Process (D :: A :: Δ₂)}
    {R : Process (B :: Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ C ⊗ D , Δ)
    (r : Δ ≃ Δ₁ + Δ₂) ->
    let _ , p' , q' = +-assoc-l p q in
    let _ , p'' , r' = +-assoc-l p' r in
    cut d p (fork (split-r q) (split-r r) P Q) R ⊒
    fork q' r' P (cut d (split-l p'') (#process #here Q) R)

  s-join :
    ∀{Γ Γ₁ Γ₂ Δ A B C D}
    {P : Process (D :: C :: A :: Δ)}
    {Q : Process (B :: Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ C ⅋ D , Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    cut d p (join (split-r q) P) Q ⊒
    join q' (cut d (split-l (split-l p')) (#process #rot P) Q)

  s-refl : ∀{Γ} {P : Process Γ} -> P ⊒ P
  s-tran : ∀{Γ} {P Q R : Process Γ} -> P ⊒ Q -> Q ⊒ R -> P ⊒ R
  s-cong-l :
    ∀{Γ Γ₁ Γ₂ A A'}
    {P Q : Process (A :: Γ₁)}
    {R : Process (A' :: Γ₂)}
    (d : Dual A A')
    (p : Γ ≃ Γ₁ + Γ₂) -> P ⊒ Q -> cut d p P R ⊒ cut d p Q R
```

## Equational Reasoning for ⊒

```agda
infix  1 ⊒begin_
infixr 2 _⊒⟨⟩_ _⊒⟨_⟩_
infix  3 _⊒end

⊒begin_ : {Γ : Context} {P Q : Process Γ} -> P ⊒ Q -> P ⊒ Q
⊒begin_ p = p

_⊒end : {Γ : Context} (P : Process Γ) -> P ⊒ P
_⊒end _ = s-refl

_⊒⟨_⟩_ : {Γ : Context} (P : Process Γ) {Q R : Process Γ} -> P ⊒ Q -> Q ⊒ R -> P ⊒ R
_⊒⟨_⟩_ _ = s-tran

_⊒⟨⟩_ : {Γ : Context} (P : Process Γ) {Q : Process Γ} -> P ⊒ Q -> P ⊒ Q
_ ⊒⟨⟩ p = p
```

## Properties of Structural Pre-Congruence

We prove a few derivable properties about `⊒`. First, that
associativity of cuts also works in the opposite direction.

```agda
s-assoc-l : ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A A' B B'}
            {P : Process (B :: Δ₁)}
            {Q : Process (B' :: A :: Δ₂)}
            {R : Process (A' :: Γ₂)}
            (d : Dual A A') (e : Dual B B')
            (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ Δ₁ + Δ₂)
            (p' : Δ ≃ Δ₂ + Γ₂) (q' : Γ ≃ Δ₁ + Δ) ->
            cut d p (cut e (split-r q) P Q) R ⊒
            cut e q' P (cut d (split-l p') (#process #here Q) R)
s-assoc-l {P = P} {Q = Q} {R = R} d e p q p' q' =
  ⊒begin
    cut d p (cut e (split-r q) P Q) R ⊒⟨ s-cong-l d p
                                          (s-comm e (dual-symm e) (split-r q) (split-l (+-comm q))) ⟩
    cut d p (cut (dual-symm e) (split-l (+-comm q)) Q P) R ⊒⟨ s-comm d (dual-symm d) p (+-comm p) ⟩
    cut (dual-symm d) (+-comm p) R (cut (dual-symm e) (split-l (+-comm q)) Q P) ⊒⟨ s-assoc-r (dual-symm d) (dual-symm e) (+-comm p) (+-comm q)
                                                                                    (+-comm p') (+-comm q') ⟩
    cut (dual-symm e) (+-comm q') (cut (dual-symm d) (split-r (+-comm p')) R (#process #here Q)) P ⊒⟨ s-cong-l (dual-symm e) (+-comm q')
                                                                                                       (s-comm (dual-symm d) d (split-r (+-comm p')) (split-l p')) ⟩
    cut (dual-symm e) (+-comm q') (cut d (split-l p') (#process #here Q) R) P ⊒⟨ s-comm (dual-symm e) e (+-comm q') q' ⟩
    cut e q' P (cut d (split-l p') (#process #here Q) R)
  ⊒end
```

Then we prove that `⊒` is a congruence on the *right* of cuts and,
therefore, that can be applied to both processes in a cut
simultaneously.

```agda
s-cong-r :
  ∀{Γ Γ₁ Γ₂ A B}
  {P : Process (A :: Γ₁)}
  {Q Q' : Process (B :: Γ₂)}
  (d : Dual A B)
  (p : Γ ≃ Γ₁ + Γ₂) ->
  Q ⊒ Q' -> cut d p P Q ⊒ cut d p P Q'
s-cong-r {P = P} {Q} {Q'} d p pcong =
  ⊒begin
    cut d p P Q                       ⊒⟨ s-comm d (dual-symm d) p (+-comm p) ⟩
    cut (dual-symm d) (+-comm p) Q P  ⊒⟨ s-cong-l (dual-symm d) (+-comm p) pcong ⟩
    cut (dual-symm d) (+-comm p) Q' P ⊒⟨ s-comm (dual-symm d) d (+-comm p) p ⟩
    cut d p P Q'
  ⊒end

s-cong-2 :
  ∀{Γ Γ₁ Γ₂ A B}
  {P P' : Process (A :: Γ₁)}
  {Q Q' : Process (B :: Γ₂)}
  (d : Dual A B)
  (p : Γ ≃ Γ₁ + Γ₂) ->
  P ⊒ P' -> Q ⊒ Q' -> cut d p P Q ⊒ cut d p P' Q'
s-cong-2 {P = P} {P'} {Q} {Q'} d p Pc Qc =
  ⊒begin
    cut d p P Q   ⊒⟨ s-cong-l d p Pc ⟩
    cut d p P' Q  ⊒⟨ s-cong-r d p Qc ⟩
    cut d p P' Q'
  ⊒end
```
