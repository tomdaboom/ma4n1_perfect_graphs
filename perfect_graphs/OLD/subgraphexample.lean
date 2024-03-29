import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
--import Mathlib.Combinatorics.SimpleGraph.Basic
--import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Subgraph
--import Mathlib.Combinatorics.SimpleGraph.chromaticNumber
import Mathlib.Data.Fintype.Basic



inductive color : Type
| red : color
| blue : color
| green : color

-- open color



namespace PerfectGraphs

#check SimpleGraph (Fin 5)





-- lemma Symm : Symmetric AdjExample := by
-- dsmip at *




def G : SimpleGraph (Fin 5) where
  Adj x y  :=
    --  notice that I removed the `if .. then .. else ..` since it was not necessary
    x = 0 ∧ y = 1 ∨ x = 1 ∧ y = 0 ∨ x = 2 ∧ y = 3 ∨ x = 3 ∧ y = 2
  symm a b h := by
    --  `aesop` is a "search" tactic: among other things, it splits all cases and tries
    --  various finishing tactics.
    aesop
  loopless a b := by
    aesop

def G' : SimpleGraph (Fin 5) where
  Adj x y  :=
    --  notice that I removed the `if .. then .. else ..` since it was not necessary
    x = 0 ∧ y = 1 ∨ x = 1 ∧ y = 0 
  symm a b h := by
    --  `aesop` is a "search" tactic: among other things, it splits all cases and tries
    --  various finishing tactics.
    aesop
  loopless a b := by
    aesop

open SimpleGraph
def G'' : Subgraph G where
 verts := {0,1}
 Adj x y := x = 0 ∧ y = 1 ∨ x = 1 ∧ y = 0 
 adj_sub  := by 
  intros v w h 
    unfold Adj at ⊢ h v w

  
  aesop
  edge_vert := by aesop
  symm Symmetric Adj := by aesop_graph

#check (G'' : Subgraph G)
#check G''.Subgraph.IsInduced G

open SimpleGraph
theorem subg : G' ≤ G := by
  unfold G; unfold G';
  aesop_graph




theorem indsub : G.Subgraph.IsInduced G' := by
  unfold G; unfold G';
 


#align simple_graph.to_subgraph SimpleGraph.toSubgraph


def exampleColoringFunction (v : Fin 5) : Bool :=
  v=0 ∨  v=2


lemma valid_coloring : ∀ {v w : Fin 5}, G.Adj v w → exampleColoringFunction v ≠ exampleColoringFunction w :=
  by
    intros v w h
    unfold G at h
    unfold SimpleGraph.Adj at h
    unfold exampleColoringFunction
    aesop












def exampleGraph.Coloring : (exampleGraph).Coloring Bool :=
  SimpleGraph.Coloring.mk exampleColoringFunction valid_coloring

#check exampleGraph.Coloring