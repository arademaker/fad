import Lean.Data
import Fad.Chapter7
import Fad.Chapter1

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



/- 9.4 Prim’s algorithm -/

open Chapter7 (minWith picks)
open Chapter1 (concatMap apply)

--Adicionei um Prim ao final dos elementos tratados nesse tópico, para evitar conflitos com outras funções que no livro são definidas pelo mesmo nome.

abbrev StatePrim := (Tree × List Edge)

def addPrim (e: Edge) (t: Tree) : Tree :=
  let (vs, es) := t
  cond (vs.contains (source e)) (target e :: vs, e :: es) (source e :: vs, e::es)


def safeEdgePrim (e: Edge) (t: Tree) : Bool :=
  (nodes t).contains (source e) ≠ (nodes t).contains (target e)


def stepsPrim (s: StatePrim) : List StatePrim :=
  let (t,es) := s
  (picks es).filterMap fun (e, es') => cond (safeEdgePrim e t) (some (addPrim e t, es')) none


def spatsPrim (g : Graph) : List Tree :=
  let start : StatePrim :=
    match nodes g with
     | []     => (([], []), [])
     | v :: _ => (([v], []), edges g)

  let done : StatePrim → Bool :=
    fun (t, _) => (nodes t).length == (nodes g).length

  let rec helper (ss : List StatePrim) (fuel: Nat): List Tree :=
    match fuel with
      | 0        => panic! "Never here"
      | fuel + 1 => cond (ss.all done) (ss.map Prod.fst) (helper (concatMap stepsPrim ss) fuel)
        termination_by fuel

  helper [start] g.1.length


--#eval spats ([1,2,3,4],[(1,2,1), (2,3,2), (3,4,5)])

def mcstPrim : Graph → Tree :=
  minWith cost ∘ spatsPrim

def gstepPrim : StatePrim → StatePrim
  | (t, [])      => (t, [])
  | (t, e :: es) =>
    let keep (e: Edge) (s: StatePrim) : StatePrim :=
      let (t', es') := s
      (t', e :: es')
    cond (safeEdgePrim e t) (addPrim e t, es) (keep e (gstepPrim (t, es)))



def prim (g : Graph) : Tree :=
  let start : StatePrim :=
    match nodes g with
    | []     => (([], []), [])
    | v :: _ => (([v], []), edges g)

  let done : StatePrim → Bool :=
    fun (t, _) => (nodes t).length == (nodes g).length

  let rec helper (s : StatePrim) (fuel : Nat) : StatePrim :=
    match fuel with
    | 0        => panic! "Never Here"
    | fuel + 1 => cond (done s) s (helper (gstepPrim s) fuel)
    termination_by fuel

  (helper start g.1.length).1

def prim' (g : Graph) : Tree :=
  let start : StatePrim :=
    match nodes g with
    | []     => (([], []), [])
    | v :: _ => (([v], []), edges g)
  let n := (nodes g).length
(apply (n-1) gstepPrim (start)).1

--#eval prim ([1,2,3,4],[(1, 2, 1), (1, 3, 2), (2, 3, 5), (3,4,20), (3,4,50)])
--#eval prim' ([1,2,3,4],[(1, 2, 1), (1, 3, 2), (2, 3, 5), (3,4,20), (3,4,50)])

abbrev Links := Std.HashMap Vertex (Vertex × Weight)
abbrev StatePrim' := Links × List Vertex

def parentPrim (ls : Links) (v : Vertex) : Vertex :=
  (ls.get! v).1

def weightPrim (ls: Links) (v : Vertex) : Weight :=
  (ls.get! v).2

abbrev Weights := Std.HashMap (Vertex × Vertex) Weight

end Chapter9
