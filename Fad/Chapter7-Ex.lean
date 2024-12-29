import Fad.Chapter6
import Fad.Chapter7

namespace Chapter7

/- # Exercicio 7.1 -/

def minimumBy {α : Type} (cmp : α → α → Ordering) : List α → Option α
  | []      => none
  | x :: xs =>
    some (xs.foldr (λ y r => cond (cmp y r = Ordering.lt) y r) x)

def minWith₁ {α β : Type} [Ord β] (f : α → β) (xs : List α) : Option α :=
  let helper (x y : α) : Ordering := compare (f x) (f y)
  minimumBy helper xs

def minWith₂ {α β : Type} [Ord β] (f : α → β) (xs : List α) : Option α :=
  let tuple (x : α) : β × α := (f x, x)
  let cmp (x y : β × α) := compare x.1 y.1
  minimumBy cmp (xs.map tuple) >>= (λ pair => some pair.2)

instance : Ord Float where
  compare x y :=
    if x < y then Ordering.lt
    else if x == y then Ordering.eq
    else Ordering.gt


/- # Exercicio 7.2 -/

def minsWith {α β : Type} [Ord β] (f : α → β) (xs : List α) : List α :=
  let step (x : α) (ys : List α) : List α :=
    match ys with
    | [] => [x]
    | y :: ys =>
      match compare (f x) (f y) with
      | Ordering.lt => [x]
      | Ordering.eq => x :: y :: ys
      | Ordering.gt => y :: ys
  xs.foldr step []

def minsWith' {α β : Type} [Ord β] (f : α → β) (xs : List α) : List α :=
  let step (x : β × α) (ys : List (β × α)) :=
    match ys with
    | [] => [x]
    | y :: ys =>
      match compare (x.fst) (y.fst) with
      | Ordering.lt => [x]
      | Ordering.eq => x :: y :: ys
      | Ordering.gt => y :: ys
  xs.map tuple |>.foldr step [] |>.map (·.snd)
    where tuple x := (f x, x)


/- # Exercicio 7.4 -/

def interleave {α : Type} : List α → List α → List (List α)
| xs, []            => [xs]
| [], ys            => [ys]
| x :: xs, y :: ys  =>
  let l := interleave xs (y :: ys) |>.map (x :: ·)
  let r := interleave (x :: xs) ys |>.map (y :: ·)
  l ++ r

def cp {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
 Chapter1.concatMap (λ x ↦ ys.map (λ y ↦ (x, y))) xs

def perms₁ {α : Type} : List α → List (List α)
| []  => [[]]
| [x] => [[x]]
| xs  =>
  let p := List.splitInTwo (Subtype.mk xs rfl)
  let yss := perms p.1
  let zss := perms p.2
  Chapter1.concatMap (Function.uncurry interleave) (cp yss zss)


/- # Exercicio 7.5 -/

open Chapter6 (minimum)

example (x : Nat)
  : minimum ([].map (x :: ·)) ≠ x :: (minimum []) := by
  rw [List.map]
  rw [minimum]
  rw [Chapter6.foldr1]
  exact List.ne_cons_self


/- # Exercicio 7.10  -/

def pick₁ : List Nat → Option (Nat × List Nat)
| []       => none
| [x]      => some (x, [])
| x :: xs  =>
  match pick₁ xs with
  | none => none
  | some (y, ys) =>
    if x ≤ y then some (x, xs) else some (y, x :: ys)
