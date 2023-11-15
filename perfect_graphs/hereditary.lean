--yes you don't need a lot of these, no i will not take them out
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Finset.Pairwise
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Subgraph
set_option autoImplicit false

namespace PerfectGraphs

open SimpleGraph
open Subgraph


def isEmpty {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ¬ G.Adj u v

--identical other than working for subgraphs, not currently using this but may be useful to have around
def isEmpty' {V : Type} {G : SimpleGraph V} (H : Subgraph G): Prop :=
  ∀ u v : V, ¬ H.Adj u v

def isComplete {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ¬ G.Adj u v

--this doesn't work
def isBipartite {V: Type}(U' : V)(G : SimpleGraph V) : Prop :=
  ∀ u v: V, G.Adj u v → v ⊂ U ∧ u.isRight ∨ v.isRight ∧ u.isLeft
  --goal: pass in two sets of elements of type V, no edges between vertices in same set, any edge is between vertex of different sets (could combine), all vertices are in one of the two sets

--copied from subgraph_example
def PGIsInduced {V : Type} (H : SimpleGraph V) (H' : Subgraph H) : Prop :=
  ∀ {v w : V}, v ∈ H'.verts → w ∈ H'.verts → H.Adj v w → H'.Adj v w


--coe is defined in Subgraph but for whatever reason was not being recognised for me - this definition is copied and pasted from the source code with a few minor adjustments to the types passed in
def coe {V : Type}{G : SimpleGraph V}(G' : Subgraph G) : SimpleGraph G'.verts where
  Adj v w := G'.Adj v w
  symm _ _ h := G'.symm h
  loopless v h := loopless G v (G'.adj_sub h)

--statement of empty graphs being a hereditary property
--I'm working on a proof!!
--note the use of isEmpty' here and coe(H') in complete
example {V : Type} (H : SimpleGraph V)(H' : Subgraph H)(h1: isEmpty H)(h2 : PGIsInduced H H') : isEmpty' H'  := by
  unfold isEmpty'
  sorry

--statement of complete graphs being a hereditary property
example {V : Type} (H : SimpleGraph V)(H' : Subgraph H)(h1: isComplete H)(h2 : PGIsInduced H H') : isComplete (coe H')  := by
  sorry

end PerfectGraphs
