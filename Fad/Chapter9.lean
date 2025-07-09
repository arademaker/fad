import Lean.Data
import Fad.Chapter1
import Fad.Chapter3
import Fad.Chapter7

namespace Chapter9

/- 9.1 Graphs and spanning trees -/

abbrev Vertex := Nat
abbrev Weight := Int
abbrev Edge   := (Vertex × Vertex × Weight)
abbrev Graph  := (List Vertex × List Edge)

def nodes (g : Graph) : List Vertex := g.1
def edges (g : Graph) : List Edge := g.2
def source  (e : Edge) : Vertex := e.1
def target (e : Edge) : Vertex := e.2.1
def weight (e : Edge) : Weight := e.2.2

abbrev AdjArray := Lean.AssocList Vertex (List (Vertex × Weight))

abbrev Tree   := Graph
abbrev Forest := List Tree

def cost (t : Tree) : Int :=
  (edges t).map weight |>.sum


--#eval cost ([1,2,3,4],[(1,2,5), (2,3,5), (3,4,10)])


/- # Section 9.4 Prim’s algorithm -/

namespace primsalgorithm

open Chapter1 (concatMap apply)
open Chapter3 (accumArray)
open Chapter7 (minWith picks)

abbrev State := (Tree × List Edge)

def add (e: Edge) (t: Tree) : Tree :=
  let (vs, es) := t

  cond (vs.contains (source e)) (target e :: vs, e :: es) (source e :: vs, e::es)


def safeEdge (e: Edge) (t: Tree) : Bool :=
  (nodes t).contains (source e) ≠ (nodes t).contains (target e)


def steps (s: State) : List State :=
  let (t,es) := s
  (picks es).filterMap fun (e, es') => cond (safeEdge e t) (some (add e t, es')) none


def spats (g : Graph) : List Tree :=
  let start : State :=
    match nodes g with
     | []     => (([], []), [])
     | v :: _ => (([v], []), edges g)

  let done : State → Bool :=
    fun (t, _) => (nodes t).length == (nodes g).length

  let rec helper (ss : List State) (fuel: Nat): List Tree :=
    match fuel with
      | 0        => panic! "Never here"
      | fuel + 1 => cond (ss.all done) (ss.map Prod.fst) (helper (concatMap steps ss) fuel)
        termination_by fuel

  helper [start] g.1.length



def mcst : Graph → Tree :=
  minWith cost ∘ spats

def gstep : State → State
  | (t, [])      => (t, [])
  | (t, e :: es) =>

    let keep (e: Edge) (s: State) : State :=
      let (t', es') := s
      (t', e :: es')

    cond (safeEdge e t) (add e t, es) (keep e (gstep (t, es)))



def prim (g : Graph) : Tree :=
  let start : State :=
    match nodes g with
    | []     => (([], []), [])
    | v :: _ => (([v], []), edges g)

  let done : State → Bool :=
    fun (t, _) => (nodes t).length == (nodes g).length

  let rec helper (s : State) (fuel : Nat) : State :=
    match fuel with
    | 0        => panic! "Never Here"
    | fuel + 1 => cond (done s) s (helper (gstep s) fuel)
    termination_by fuel

  (helper start g.1.length).1

def prim' (g : Graph) : Tree :=
  let start : State :=
    match nodes g with
    | []     => (([], []), [])
    | v :: _ => (([v], []), edges g)

  let n := (nodes g).length

(apply (n-1) gstep (start)).1




#eval prim ([1,2,3,4],[(1, 2, 1), (1, 3, 2), (2, 3, 5), (3,4,20), (3,4,50)])
#eval prim' ([1,2,3,4],[(1, 2, 1), (1, 3, 2), (2, 3, 5), (3,4,20), (3,4,50)])


abbrev Links := Std.HashMap Vertex (Vertex × Weight)
abbrev StatePrim' := Links × List Vertex

def parent (ls : Links) (v : Vertex) : Vertex :=
  (ls.get! v).1

def weight' (ls: Links) (v : Vertex) : Weight :=
  (ls.get! v).2

abbrev Weights := Std.HashMap (Vertex × Vertex) Weight



end primsalgorithm

end Chapter9
