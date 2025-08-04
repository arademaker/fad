import VersoManual
import Fad.Basic

open Verso.Genre Manual
open Fad

#doc (Manual) "Functional Programming" =>
%%%
tag := "functional-programming"
%%%


# Básico
%%%
tag := "basic"
%%%

Lean is a complete programming language. In this Chapter, our goal will not be to present the language—a task we leave to FPinLean—but rather to present the basic concepts that will allow us to study various algorithms in a purely functional way.

Our goal here is therefore not to teach Lean, but to use Lean to study some algorithms implemented in a functional way. Lean will allow us not only to implement the algorithms elegantly, but to 'reason' about these algorithms, proving properties about them and the equivalence between some versions of each algorithm that we present.


```savedLean
def map₁ {a b : Type} (f : a → b) (xs : List a) : List b :=
 match xs with
 | [] => []
 | (x :: xs) => f x :: map₁ f xs

def map₂ {a b : Type} : (a → b) → List a → List b
| _, [] => []
| f, (x :: xs) => f x :: map₂ f xs

def map₃ {a b : Type} (f : a → b) : List a → List b
| [] => []
| (x :: xs) => f x :: map₃ f xs

example : map₃ (· * 10) [1,2,3] = [10,20,30] := rfl
```
