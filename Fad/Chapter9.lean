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


--#eval cost ([1,2,3,4],[(1,2,5), (2,3,5), (3,4,10)])


end Chapter9
