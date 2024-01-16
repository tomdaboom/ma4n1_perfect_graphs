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

--CLIQUES

def hasNClique {V : Type} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ t, G.IsNClique n t

noncomputable def CliqueNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sSup { n : ℕ | hasNClique G n }

theorem equivCliqueNumber {V : Type} (G : SimpleGraph V) (k : ℕ) (NClique : hasNClique G k) (notNPlusOneClique : ¬ hasNClique G (k+1)) : CliqueNumber G = k := by
  sorry



--SUBGRAPHS

def isInducedSubgraph {V : Type} (H : SimpleGraph V) (H' : Subgraph H) : Prop :=
  ∀ {v w : V}, v ∈ H'.verts → w ∈ H'.verts → H.Adj v w → H'.Adj v w





#check Fin 5

def isInducedSimpleGraph {V : Type} (H : SimpleGraph V) (H' : SimpleGraph V) : Prop :=
  ∀ {v w : V}, (H.Adj v w → H'.Adj v w) ∨ (H'.neighborSet v = ∅) ∨ (H'.neighborSet w = ∅)




--coe is defined in Subgraph but for whatever reason was not being recognised for me - this definition is copied and pasted from the source code with a few minor adjustments to the types passed in
def coe {V : Type}{G : SimpleGraph V}(H : Subgraph G) : SimpleGraph H.verts where
  Adj v w := H.Adj v w
  symm _ _ h := H.symm h
  loopless v h := loopless G v (H.adj_sub h)



--PERFECT DEFINITION
def isPerfect {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ H : Subgraph G, isInducedSubgraph G H → (coe H).chromaticNumber = CliqueNumber (coe H)




--DEALING WITH CYCLES - CURRENTLY IN PROGRESS
def cycle (n : ℕ) : (SimpleGraph (Fin n)) :=
  SimpleGraph.fromRel (λ x y => (x-y : ℕ) = 1)



def hasNCycle' {m : ℕ} (G : SimpleGraph (Fin m)) (n : ℕ) : Prop :=
  isInducedSubgraph G (G.toSubgraph (cycle m))

def hasNCycle {V : Type} (G : SimpleGraph V) (n : ℕ) : Prop :=
  isInducedSubgraph G (G.toSubgraph (cycle n))

def hasOddHole {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ n : ℕ, hasNCycle G (2*n+5) --odd cycle of length ≥ 5, using that 0 ∈ ℕ in Lean

--STRONG PERFECT GRAPH THEOREM
theorem strongPerfectGraphTheorem {V : Type} (G : SimpleGraph V) : isPerfect G ↔ ¬ hasOddHole G ∧ ¬ hasOddHole Gᶜ := by
  sorry

--WEAK PERFECT GRAPH THEOREM
--Prove one direction using SPGT
theorem weakPerfectGraphTheoremForward {V : Type} (G : SimpleGraph V): isPerfect G → isPerfect (compl G):= by
  intro h
  rw [@strongPerfectGraphTheorem]
  rw [@strongPerfectGraphTheorem] at h
  refine And.symm ?_
  rw[compl_compl]
  apply h

--Prove other direction using Gᶜᶜ = G
theorem weakPerfectGraphTheoremBackward {V : Type} (G : SimpleGraph V): isPerfect (compl G) → isPerfect (G):= by
   intro h
   apply (weakPerfectGraphTheoremForward Gᶜ) at h
   rw [compl_compl] at h
   apply h

--Unify both directions into the Weak Perfect Graph Theorem
theorem weakPerfectGraphTheorem {V : Type} (G : SimpleGraph V) : isPerfect G ↔  isPerfect (compl G)
:= by
  refine Iff.symm ((fun {a b} => iff_def.mpr) {
    left := by apply weakPerfectGraphTheoremBackward
    right := by apply weakPerfectGraphTheoremForward
  })
