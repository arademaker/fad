import Lean.Data
import Fad.Chapter1
import Fad.«Chapter1-Ex»

namespace Chapter9

def picks {a : Type} : List a → List (a × List a) -- 1 ou 7
| []      => []
| x :: xs =>
  (x, xs) :: ((picks xs).map (λ p => (p.1, x :: p.2)))

def wrap {α : Type} (a : α) : List α := [a] -- 1-Ex

partial def until' (p: a → Bool) (f: a → a) (x : a) : a := -- 1
  if p x then x
  else until' p f (f x)

def foldr1 {a : Type} [Inhabited a] (f : a → a → a) : List a → a -- 7
  | []    => default
  | x::xs => xs.foldr f x

def minWith {a b : Type} [LE b] [Inhabited a] -- 7
  [DecidableRel (α := b) (· ≤ ·)]
  (f : a → b) (as : List a) : a :=
  let smaller f x y := cond (f x ≤ f y) x y
  foldr1 (smaller f) as

/- 9.1 Graphs and spanning trees -/

abbrev Vertex := Nat
abbrev Weight := Int
abbrev Edge   := (Vertex × Vertex × Weight)
abbrev Graph  := (List Vertex × List Edge)

def nodes (g : Graph) : List Vertex := g.1
def edges (g : Graph) : List Edge := g.2
def souce  (e : Edge) : Vertex := e.1
def target (e : Edge) : Vertex := e.2.1
def weight (e : Edge) : Weight := e.2.2

abbrev AdjArray := Lean.AssocList Vertex (List (Vertex × Weight))

abbrev Tree   := Graph
abbrev Forest := List Tree

def cost (t : Tree) : Int :=
  (edges t).map weight |>.sum

/- 9.2 Kruskal’s algorithm -/

abbrev State  := Forest × List Edge

def extract (s : State) : Tree :=
  s.1.head!

def done (s : State) : Bool :=
  s.1.length = 1

def start (g : Graph) : State :=
  (nodes g |>.map (fun v => ([v], [])), edges g)

def find (ts : Forest) (v : Vertex) : Tree :=
  (ts.find? (fun t => (nodes t).contains v)).get!

def safeEdge (e : Edge) (ts : Forest) : Bool :=
  find ts (souce e) ≠ find ts (target e)

def add (e : Edge) (ts : Forest) : Forest :=
  let t1 := find ts (souce e)
  let t2 := find ts (target e)
  let rest := ts.filter (fun t => t ≠ t1 ∧ t ≠ t2)
  ((t1.1 ++ t2.1), e :: (t1.2 ++ t2.2)) :: rest

def steps : State → List State
| (ts, es) =>
  picks es
  |>.filterMap (fun (e, es') =>
    if safeEdge e ts then
      some (add e ts, es')
    else
      none)

def spats (g : Graph) : List Tree :=
  (until' (fun ss => ss.all done) (fun ss => List.flatMap steps ss)) (wrap (start g))
  |>.map extract

def MCC (g : Graph) : Tree :=
  minWith cost (spats g)

def gstep (s : State) : State :=
  match s with
  | (_, []) => s
  | (ts, e :: es) =>
    let t1 := find ts (souce e)
    let t2 := find ts (target e)
    let rest := ts.filter (fun t => t ≠ t1 ∧ t ≠ t2)
    let ts' := ((t1.1 ++ t2.1), e :: (t1.2 ++ t2.2)) :: rest
    if t1 ≠ t2 then
      (ts', es)
    else
      gstep (ts, es)

end Chapter9

