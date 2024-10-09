# Types

This module defines types and proves their main properties.

```agda
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

module Type where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong₂)
```

Types are propositions of multiplicative additive linear logic. The constructors
`Zero`, `One`, `Bot` and `Top` respectively represent the constants
$\mathbb{0}$, $\mathbb{1}$, $⊥$ and $⊤$. The remaining constructors represent
the binary connectives.

```agda
data Type : Set where
  Zero One Bot Top : Type
  _&_ _⊕_ _⊗_ _⅋_ : Type -> Type -> Type
```

Duality is the standard relation between a type and its dual, which represents
the complementary protocol. A relation `Dual A B` means that $A = B^⊥$.

```agda
data Dual : Type -> Type -> Set where
  dual-zero-top : Dual Zero Top
  dual-top-zero : Dual Top Zero
  dual-one-bot  : Dual One Bot
  dual-bot-one  : Dual Bot One
  dual-with-plus : ∀{A B A' B'} -> Dual A A' -> Dual B B' -> Dual (A & B) (A' ⊕ B')
  dual-plus-with : ∀{A B A' B'} -> Dual A A' -> Dual B B' -> Dual (A ⊕ B) (A' & B')
  dual-fork-join : ∀{A B A' B'} -> Dual A A' -> Dual B B' -> Dual (A ⊗ B) (A' ⅋ B')
  dual-join-fork : ∀{A B A' B'} -> Dual A A' -> Dual B B' -> Dual (A ⅋ B) (A' ⊗ B')
```

It is straightforward to prove that duality is a symmetric relation.

```agda
dual-symm : ∀{A B} -> Dual A B -> Dual B A
dual-symm dual-zero-top = dual-top-zero
dual-symm dual-top-zero = dual-zero-top
dual-symm dual-one-bot = dual-bot-one
dual-symm dual-bot-one = dual-one-bot
dual-symm (dual-with-plus p q) = dual-plus-with (dual-symm p) (dual-symm q)
dual-symm (dual-plus-with p q) = dual-with-plus (dual-symm p) (dual-symm q)
dual-symm (dual-fork-join p q) = dual-join-fork (dual-symm p) (dual-symm q)
dual-symm (dual-join-fork p q) = dual-fork-join (dual-symm p) (dual-symm q)
```

It is also easy to prove that duality is an injective function.

```agda
dual-fun-r : ∀{A B C} -> Dual A B -> Dual A C -> B ≡ C
dual-fun-r dual-zero-top dual-zero-top = refl
dual-fun-r dual-top-zero dual-top-zero = refl
dual-fun-r dual-one-bot dual-one-bot = refl
dual-fun-r dual-bot-one dual-bot-one = refl
dual-fun-r (dual-with-plus p p') (dual-with-plus q q') = cong₂ _⊕_ (dual-fun-r p q) (dual-fun-r p' q')
dual-fun-r (dual-plus-with p p') (dual-plus-with q q') = cong₂ _&_ (dual-fun-r p q) (dual-fun-r p' q')
dual-fun-r (dual-fork-join p p') (dual-fork-join q q') = cong₂ _⅋_ (dual-fun-r p q) (dual-fun-r p' q')
dual-fun-r (dual-join-fork p p') (dual-join-fork q q') = cong₂ _⊗_ (dual-fun-r p q) (dual-fun-r p' q')

dual-fun-l : ∀{A B C} -> Dual B A -> Dual C A -> B ≡ C
dual-fun-l d e = dual-fun-r (dual-symm d) (dual-symm e)
```
-->
