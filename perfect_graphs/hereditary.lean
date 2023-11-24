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

#check (G: emptyGraph V) --emptyGraph is not a type!!

def isEmpty {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ¬ G.Adj u v

--identical other than working for subgraphs, not currently using this but may be useful to have around
def isEmpty' {V : Type} {G : SimpleGraph V} (H : Subgraph G): Prop :=
  ∀ u v : V, ¬ H.Adj u v

def isComplete {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, G.Adj u v

def isComplete' {V : Type} {G : SimpleGraph V} (H : Subgraph G): Prop :=
  ∀ u v : V, H.Adj u v



--this is not how i wanna do the two parts
def set X := X → Prop

#check set X

def isBipartite {V: Type}(U' : V)(G : SimpleGraph V) : Prop :=
  ∀ u v: V, G.Adj u v → v ⊂ U ∧ u.isRight ∨ v.isRight ∧ u.isLeft
  --goal: pass in two sets of elements of type V, no edges between vertices in same set, any edge is between vertex of different sets (could combine), all vertices are in one of the two sets

--yea this won't work because we'd need to define the two partite sets
def isBipartite' {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, G.Adj u v → v.isLeft ∧ u.isRight ∨ v.isRight ∧ u.isLeft
  --v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft


def PGIsInduced {V : Type} (H : SimpleGraph V) (H' : Subgraph H) : Prop :=
  ∀ {v w : V}, v ∈ H'.verts → w ∈ H'.verts → H.Adj v w → H'.Adj v w




--statement of empty graphs being a hereditary property
--I'm working on a proof
example {V : Type} (H : SimpleGraph V)(H' : Subgraph H)(h1: isEmpty H)(h2 : PGIsInduced H H') : isEmpty' H'  := by
  unfold isEmpty'
  unfold isEmpty at h1
  unfold PGIsInduced at h2 --unfold all defns
  intros v w --for vertices
  --intro f --for new goal : False
  
  

  --there are some applys here, no simps or exacts





  --contrapose h2
  --unfold PGIsInduced
  --simp only [not_forall, exists_prop, exists_and_left]

  --contrapose h1
  --unfold isEmpty
  --contrapose h2
  --unfold PGIsInduced
  --apply of_not_not at h1

  --contrapose h2
  --unfold PGIsInduced
  --aesop


  sorry

example {V : Type} (G : SimpleGraph V)(H : Subgraph G)(h1: isComplete G)(h2 : PGIsInduced G H) : isComplete' H  := by
  unfold isComplete'
  unfold isComplete at h1
  unfold PGIsInduced at h2 --unfold all defns
  intros v w --for vertices
  apply adj_sub
  sorry









--ORPHANED CODE
-- this already exists
def subToSimple {V : Type} {G : SimpleGraph V} (H : Subgraph G): SimpleGraph V where
  Adj u v  := H.Adj u v
  symm a b h := by symm
  loopless a b := by
    aesop

--this is not required!! this already exists!!!
def isSubgraph {V: Type}(G H : SimpleGraph V) : Prop :=
   ∀ u v : V, H.Adj u v → G.Adj u v ∧ ¬ G.Adj u v → ¬ H.Adj u v


def cycle (n : ℕ) : (SimpleGraph (Fin n)) :=
  SimpleGraph.fromRel (λ x y => (x-y : ℕ) = 1)

example : (cycle 5).Adj 1 2 := by
  unfold cycle SimpleGraph.fromRel --SimpleGraph.Adj
  simp only


end PerfectGraphs
