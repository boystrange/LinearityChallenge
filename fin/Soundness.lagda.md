# Soundness

This modules proves soundness of the type system, namely that
neither the empty context nor the context that contains only 0 are
provable.

## Imports

```agda
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)

open import Type
open import Context
open import Process
open import CutElimination
```

## Proofs

```agda
not-zero : ¬ (Process [ Zero ])
not-zero P with cut-elimination P
... | _ , link _ (split-l ())
... | _ , link _ (split-r ())
... | _ , fail (split-r ())
... | _ , wait (split-r ()) _
... | _ , case (split-r ()) _ _
... | _ , join (split-r ()) _
... | _ , select _ (split-r ()) _
... | _ , fork (split-r ()) _ _ _

not-empty : ¬ (Process [])
not-empty P with cut-elimination P
... | _ , link _ ()
... | _ , fail ()
... | _ , wait () _
... | _ , case () _ _
... | _ , join () _
... | _ , select _ () _
... | _ , fork () _ _ _
```
