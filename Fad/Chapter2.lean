import Fad.Chapter1
import Fad.«Chapter1-Ex»
import Lean
import Cslib.Algorithms.Lean.TimeM

namespace Chapter2

open Chapter1 (dropWhile)
open Cslib.Algorithms.Lean
open TimeM

-- # 2.0 Complexity

def fib : Nat → Nat
  | 0     => 1
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

def fibFast (n : Nat) : Nat :=
  (loop n).2
where
  loop : Nat → Nat × Nat
  | 0   => (0, 1)
  | n+1 => let p := loop n; (p.2, p.1 + p.2)

/-
#eval fibFast 100
#reduce fib 100 -- try eval
#print fib
-/

example : fibFast 4 = 5 := by
  unfold fibFast
  unfold fibFast.loop
  unfold fibFast.loop
  unfold fibFast.loop
  unfold fibFast.loop
  unfold fibFast.loop
  rfl


-- # 2.2 Estimating running times

def append' {a} : List a → List a → TimeM Nat (List a)
  | [], ys => pure ys
  | x :: xs, ys => do
      ✓ return x :: (← append' xs ys)

def concat₁' {a} : List (List a) → TimeM Nat (List a) :=
  List.foldr (fun xs tys => do
    let ys ← tys
    ✓[xs.length] return xs ++ ys) (pure [])

def concat₂' {a} : List (List a) → TimeM Nat (List a) :=
  List.foldl (fun txs ys => do
    let xs ← txs
    ✓[xs.length] return xs ++ ys) (pure [])

/- an alternative approach is to redefine concat₂ recursive, not depend on
foldl. it could be eventually easier to the proofs below. -/
def concat₂'' {a} : List (List a) → TimeM Nat (List a) → TimeM Nat (List a)
 | [], t => t
 | xs :: xss, t =>  do
   let res ← t
   concat₂'' xss (do ✓[res.length] return res ++ xs)


private lemma concat₁_step {a : Type*}
  (xs : List a) (xss' : List (List a)) :
  (concat₁' (xs :: xss')).time = (concat₁' xss').time + xs.length := by
  simp [concat₁', List.foldr]

/- if `xss` is a list of length `m` consisting of lists each of length `n`, then
`concat₁` is `Θ(m * n)` -/
theorem concat₁_time (xss : List (List a))
  (n : Nat) (h : ∀ xs ∈ xss, xs.length = n)
  : (concat₁' xss).time = xss.length * n := by
  induction xss with
  | nil => simp [concat₁', List.foldr]
  | cons xs xss' ih =>
    have h₁ : xs.length = n := h xs List.mem_cons_self
    have h₂ : ∀ ys ∈ xss', ys.length = n := by
      intro ys hys
      exact h ys (List.mem_cons_of_mem xs hys)
    rw [concat₁_step, ih h₂, h₁, List.length_cons]
    ring

private lemma concat₂_foldl_tb {a}
  (xss : List (List a)) (n k : Nat)
  (h : ∀ xs ∈ xss, xs.length = n)
  (acc : TimeM Nat (List a))
  (hacc : acc.ret.length = k * n)
  : (List.foldl (fun txs ys => do
       let xs ← txs
       tick xs.length
       pure (xs ++ ys)) acc xss).time
      ≤ acc.time + (k + xss.length) * n * xss.length := by
  induction xss generalizing k acc with
  | nil => simp
  | cons ys xss' ih =>
    simp only [List.foldl, List.length_cons]
    have hys : ys.length = n := h ys List.mem_cons_self
    have hxss' : ∀ zs ∈ xss', zs.length = n :=
      fun zs hzs => h zs (List.mem_cons_of_mem ys hzs)
    set acc' : TimeM Nat (List a) := do let xs ← acc; tick xs.length; pure (xs ++ ys)
    have hacc'_time : acc'.time = acc.time + k * n := by simp [acc', hacc]
    have hacc'_len : acc'.ret.length = (k + 1) * n := by
      simp [acc', List.length_append, hacc, hys]; ring
    have ih' := ih (h := hxss') (k := k + 1) (acc := acc') (hacc := hacc'_len)
    nlinarith [Nat.zero_le xss'.length, Nat.zero_le k, Nat.zero_le n]

/- if `xss` is a list of length `m` consisting of lists each of length `n`, then
`concat₂` is `O(m^2 * n)` but also Θ(m2 n) ?? -/
theorem concat₂_time (xss : List (List a))
  (n : Nat) (h : ∀ xs ∈ xss, xs.length = n)
  : (concat₂' xss).time ≤ xss.length ^ 2 * n := by
  have h1 := concat₂_foldl_tb xss n 0 h (pure []) (by simp)
  unfold concat₂'
  simp at *
  linarith [Nat.pow_two xss.length]


-- # 2.4 Amortised running times

def build (p : a → a → Bool) : List a → List a :=
 List.foldr insert []
 where
  insert x xs := x :: dropWhile (p x) xs

example : build (· = ·) [4,4,2,1,1] = [4, 2, 1] := by
 unfold build
 unfold List.foldr
 unfold List.foldr
 unfold List.foldr
 unfold List.foldr
 unfold List.foldr
 unfold build.insert
 rw [dropWhile]
 rw [dropWhile]
 rw [dropWhile]
 simp
 rfl


/- primeiro argumento evita lista infinita -/
def iterate : Nat → (a → a) → a → List a
 | 0, _, x => [x]
 | Nat.succ n, f, x => x :: iterate n f (f x)

def bits (n : Nat) : List (List Bool) :=
  iterate n inc []
 where
   inc : List Bool → List Bool
   | [] => [true]
   | (false :: bs) => true :: bs
   | (true :: bs) => false :: inc bs


def init₀ : List α → List α
| []      => panic! "no elements"
| [_]     => []
| x :: xs => x :: init₀ xs

def init₁ : List α → Option (List α)
| []      => none
| [_]     => some []
| x :: xs =>
   match init₁ xs with
   | none => none
   | some ys => some (x :: ys)

def init₂ : List α → Option (List α)
| []      => none
| [_]     => some []
| x :: xs => init₂ xs >>= (fun ys => pure (x :: ys))

def prune (p : List a → Bool) (xs : List a) : List a :=
 List.foldr cut [] xs
  where
    cut x xs := Chapter1.until' done init₀ (x :: xs)
    done (xs : List a) := xs.isEmpty ∨ p xs

def ordered : List Nat → Bool
 | [] => true
 | [_] => true
 | x :: y :: xs => x ≤ y ∧ ordered (y :: xs)

-- #eval prune ordered [3,7,8,2,3]

end Chapter2
