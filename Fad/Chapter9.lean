import Lean.Data

namespace Chapter9

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



/- 9.4 Prim’s algorithm -/

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
      | fuel + 1 => cond (ss.all done) (ss.map Prod.fst) (helper (concatMap steps ss) fuel) termination_by fuel

  helper [start] g.1.length


--#eval spats ([1,2,3,4],[(1,2,1), (2,3,2), (3,4,5)])


def gstep : State → State
  | (t, [])      => (t, [])
  | (t, e :: es) =>

    let keep (e: Edge) (s: State) : State :=
      let (t', es') := s
      (t', e :: es')

    cond (safeEdge e t) (add e t, es) (keep e (gstep (t, es)))

end Chapter9
