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

--dealing with cliques

def hasNClique {V : Type} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ t, G.IsNClique n t

noncomputable def CliqueNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sSup { n : ℕ | hasNClique G n }

theorem equivCliqueNumber {V : Type} (G : SimpleGraph V) (k : ℕ) (NClique : hasNClique G k) (notNPlusOneClique : ¬ hasNClique G (k+1)) : CliqueNumber G = k := by
  sorry



--dealing with subgraphs

def PGIsInduced {V : Type} (H : SimpleGraph V) (H' : Subgraph H) : Prop :=
  ∀ {v w : V}, v ∈ H'.verts → w ∈ H'.verts → H.Adj v w → H'.Adj v w

--coe is defined in Subgraph but for whatever reason was not being recognised for me - this definition is copied and pasted from the source code with a few minor adjustments to the types passed in
def coe {V : Type}{G : SimpleGraph V}(G' : Subgraph G) : SimpleGraph G'.verts where
  Adj v w := G'.Adj v w
  symm _ _ h := G'.symm h
  loopless v h := loopless G v (G'.adj_sub h)



--perfect definition
def isPerfect {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ H : Subgraph G, PGIsInduced G H → (coe H).chromaticNumber = CliqueNumber (coe H)



--WPGT
theorem weakPerfectGraphTheoremForward {V : Type} (G : SimpleGraph V): isPerfect G → isPerfect (compl G):= by
  sorry



theorem weakPerfectGraphTheoremBackward {V : Type} (G : SimpleGraph V): isPerfect (compl G) → isPerfect (G):= by
   -- by_contra this is contradiction

   intro h

   apply (weakPerfectGraphTheoremForward Gᶜ) at h
   --apply (weakPerfectGraphTheoremForward Gᶜ)

   --apply (weakPerfectGraphTheoremForward Gᶜ).compl_compl
   --apply (weakPerfectGraphTheoremForward ?_).compl_compl
   sorry

  --contrapose
  --by_contra
  --apply not_imp at x✝
  --apply not_not

theorem weakPerfectGraphTheorem {V : Type} (G : SimpleGraph V) : isPerfect G ↔  isPerfect (compl G)
:= by
  refine Iff.symm ((fun {a b} => iff_def.mpr) {
    left := by apply weakPerfectGraphTheoremBackward
    right := by apply weakPerfectGraphTheoremForward
  })



--dealing with cycles
def cycle (n : ℕ) : (SimpleGraph (Fin n)) :=
  SimpleGraph.fromRel (λ x y => (x-y : ℕ) = 1)

def hasNCycle {V : Type} (G : SimpleGraph V) (n : ℕ) : Prop :=
  PGIsInduced G (cycle n).toSubgraph

def hasOddHole {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ n : ℕ, hasNCycle G (2*n+5) --odd cycle of length ≥ 5, using that 0 ∈ ℕ in Lean

--SPGT
theorem strongPerfectGraphTheorem {V : Type} (G : SimpleGraph V) : isPerfect G ↔ ¬ hasOddHole G ∧ ¬ hasOddHole Gᶜ := by
  sorry
