import Lean.Data
import Fad.Chapter1
import Fad.«Chapter1-Ex»
import Fad.«Chapter5-Ex»
import Fad.Chapter7

namespace Chapter9

namespace SpanningTrees

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

end SpanningTrees

open SpanningTrees
open Chapter1 (wrap apply)
open Chapter5 (sortOn₃)

/- 9.2 Kruskal’s algorithm -/

abbrev State  := Forest × List Edge

def extract (s : State) : Tree :=
  s.1.head!

def done (s : State) : Bool :=
  s.1.length = 1

def start₀ (g : Graph) : State :=
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
  Chapter7.picks es
  |>.filterMap (fun (e, es') =>
    if safeEdge e ts then
      some (add e ts, es')
    else
      none)

def spats (g : Graph) : List Tree :=
  (Chapter1.until' (fun ss => ss.all done) (fun ss => List.flatMap steps ss)) (wrap (start₀ g))
  |>.map extract

def MCC (g : Graph) : Tree :=
 Chapter7.minWith cost (spats g)

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

def start₁ (g : Graph) : State :=
  (nodes g |>.map (fun v => ([v], [])), sortOn₃ weight (edges g))

def kruskal₁ (g : Graph) : Tree :=
  Chapter1.until' done gstep (start₁ g) |> extract

def kruskal₂ (g : Graph) : Tree :=
  let n := (nodes g).length
  extract (apply (n - 1) gstep (start₁ g))

end Chapter9
