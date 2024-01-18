import Mathlib
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
--import Mathlib.Combinatorics.SimpleGraph.chromaticNumber
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Aesop.Check
import Mathlib.Logic.Basic
import Aesop.Tree.Data
set_option trace.aesop true



namespace PerfectGraphs
open SimpleGraph
open Subgraph
open Fintype

--------------------------------------------------------------------------
--SECTION: CHROMATIC NUMBER
--TBD: Tom proof
theorem chromaticNumberAltDef {V : Type} (G : SimpleGraph V) (k : ℕ) (colorable : G.Colorable k) (notColorable : ¬ G.Colorable (k-1)) : G.chromaticNumber = k := by
    sorry

--------------------------------------------------------------------------
--SECTION: CLIQUE NUMBER
def hasNClique {V : Type} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ t, G.IsNClique n t

noncomputable def CliqueNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sSup { n : ℕ | hasNClique G n }

--TBD: Dan proof (potentially)
theorem equivCliqueNumber {V : Type} (G : SimpleGraph V) (k : ℕ) (NClique : hasNClique G k) (notNPlusOneClique : ¬ hasNClique G (k+1)) : CliqueNumber G = k := by
  unfold CliqueNumber
  refine IsGreatest.csSup_eq ?H
  unfold hasNClique
  unfold hasNClique at NClique
  unfold hasNClique at notNPlusOneClique
  unfold IsGreatest
  refine (and_iff_right NClique).mpr ?H.a
  unfold upperBounds
  aesop
  sorry

--------------------------------------------------------------------------
--SECTION: PERFECT DEFINITIONS
--TBD: standardise subgraph letters eg H H' vs G H
def isInducedSubgraph {V : Type} (H : SimpleGraph V) (H' : Subgraph H) : Prop :=
  ∀ {v w : V}, v ∈ H'.verts → w ∈ H'.verts → H.Adj v w → H'.Adj v w

def isPerfect {V : Type} (G : SimpleGraph V) : Prop :=
  (∀ H : Subgraph G, isInducedSubgraph G H → (H.coe).chromaticNumber = CliqueNumber (H.coe) ∨ (H.verts = ∅))


theorem emptyVertsClique (G : SimpleGraph Empty) : CliqueNumber G = 0 := by
 apply equivCliqueNumber
 ·unfold hasNClique
  use ∅
  aesop
 ·norm_num
  unfold hasNClique
  rw [@not_exists]
  intro t
  intro f
  rw [@isNClique_iff] at f
  cases f with
  | intro f1 f2 =>
  rw [@Finset.card_eq_one] at f2
  aesop

theorem emptyVertsChrom (G : SimpleGraph Empty) : G.chromaticNumber = 0 := by
  rw [@chromaticNumber_eq_zero_of_isempty]

theorem minperfEmptyVerts (G : SimpleGraph Empty) : G.chromaticNumber = CliqueNumber G := by
  rw [emptyVertsChrom]
  rw [emptyVertsClique]

/- These three theorems above, combined with the fact that the graph on no vertices has no subgraphs,
 justify our inclusion of the "∨ H.verts = ∅" clause in our definition of a perfect graph. -/


--------------------------------------------------------------------------
--SECTION: COMPLETE GRAPHS

--TBD: is this used?
lemma coeAdj  {V : Type} {G : SimpleGraph V}(H : Subgraph G)(u v : H.verts): SimpleGraph.Adj (Subgraph.coe H) u v ↔ Subgraph.Adj (H) u v := by
  exact Iff.rfl

def isComplete {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ¬ u = v -> G.Adj u v

--TBD: rename
theorem edgeInGraphInInducedSubgraph' {V : Type}(G : SimpleGraph V)(H : Subgraph G)(h: isInducedSubgraph G H): ∀ u v : H.verts , G.Adj u v → H.Adj u v
:= by
  intro v w
  rw[isInducedSubgraph] at h
  apply h
  simp only [Subtype.coe_prop]
  exact Subtype.mem w

--essentially a rewritten version of PGIsInducedSubgraph, but useful for proofs
 lemma edgeInGraphInInducedSubgraph {V : Type}(G : SimpleGraph V)(H : Subgraph G)(h: isInducedSubgraph G H): ∀ u v : H.verts , ( ¬u = v → G.Adj u v) → ( ¬u = v → H.Adj u v)
:= by
  intro v w
  rw[isInducedSubgraph] at h
  exact fun a a_1 => edgeInGraphInInducedSubgraph' G H h v w (a a_1)

theorem completeHereditary {V : Type} (G : SimpleGraph V)(H : Subgraph G)(h1: isInducedSubgraph G H): isComplete G → isComplete H.coe  := by
  unfold isComplete
  intros h2 u v --for vertices
  unfold isInducedSubgraph at h1
  rw [coeAdj]
  intro h3
  apply edgeInGraphInInducedSubgraph G H h1 u v (fun uv => h2 u v ?_) h3
  intro huv
  apply uv
  exact SetCoe.ext huv


lemma equivIsComplete {V : Type}
  /- [finV : Fintype V] [nemp : Nonempty V] -/
  (G : SimpleGraph V) (h : isComplete G)
  : G = (completeGraph V) := by
  unfold completeGraph
  unfold isComplete at h
  aesop

--TBD: fix? also rename
theorem CompleteN' {V : Type} [h' : Fintype V] [h : Nonempty V] [deq : DecidableEq V] : CliqueNumber (completeGraph V) = (Finset.univ (α := V)).card := by
  apply equivCliqueNumber
  unfold hasNClique
  · use Finset.univ
    apply IsNClique.mk
    unfold IsClique
    unfold completeGraph
    aesop_graph
    rfl

  · unfold hasNClique
    rw [@not_exists]
    intro S
    rw [@isNClique_iff]
    intro f
    cases f with
    | intro fl fr =>
    -- have sizeofZMod := ZMod.card n
    have subset_of_univ := Finset.subset_univ S
    have S'' := Finset.card_le_card subset_of_univ
    rw [fr] at S''
    contrapose! S''
    norm_num

theorem completeChiN {V : Type} [h' : Fintype V] : SimpleGraph.chromaticNumber (completeGraph V) = (Finset.univ (α := V)).card:= by
  simp only [completeGraph_eq_top]
  rw [@chromaticNumber_top]
  rfl

theorem CompleteIsPerfect' {V : Type}  [finV : Fintype V]  [nemp : Nonempty V] [deq : DecidableEq V]  : isPerfect (completeGraph V) := by
  classical
  unfold isPerfect
  intro H
  intro induced
  have compG2 : isComplete (completeGraph V) := by unfold isComplete; unfold completeGraph; aesop;
  have complete_is := completeHereditary (completeGraph V)
  have completeH := complete_is H
  have completeH2 := completeH induced compG2
  have H_is_complete_G := equivIsComplete H.coe completeH2
  rw [H_is_complete_G]
  by_cases h234 : Nonempty H.verts
  · left
    rw [CompleteN']
    rw [completeChiN]
  · right
    rw [@Set.not_nonempty_iff_eq_empty'] at h234
    exact h234
--------------------------------------------------------------------------
--SECTION: EMPTY GRAPHS
def isEmpty {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ¬ G.Adj u v


--essentially a rewritten version of adj_sub, but useful for proofs
lemma edgeNotInGraphNotInSubgraph {V : Type}(G : SimpleGraph V)(H : Subgraph G): ∀ u v : V, ¬ G.Adj u v → ¬ H.Adj u v
:= by
  intro u v
  contrapose
  rw[not_not,not_not]
  apply adj_sub

theorem emptyHereditary {V : Type} (G : SimpleGraph V)(H : Subgraph G): isEmpty G → isEmpty H.coe  := by
  unfold isEmpty
  intros h u v
  rw [coeAdj]
  exact edgeNotInGraphNotInSubgraph G H u v (h u v)

theorem equivIsEmpty {V : Type}
  /- [finV : Fintype V] [nemp : Nonempty V] -/
  (G : SimpleGraph V) (h : isEmpty G)
  : G = (emptyGraph V) := by
  unfold emptyGraph
  unfold isEmpty at h
  aesop

theorem EmptyOne' {V : Type}[h : Nonempty V] [DecidableEq V]  : CliqueNumber (emptyGraph V) = 1 := by
  apply equivCliqueNumber
  unfold hasNClique
  · use {h.some}
    apply IsNClique.mk
    unfold IsClique
    norm_num
    norm_num
  · norm_num
    unfold hasNClique
    rw [@not_exists]
    intro S
    rw [@isNClique_iff]
    intro f
    cases f with
    | intro fl fr =>
    revert fl
    unfold IsClique
    intro fl
    unfold Set.Pairwise at fl
    aesop
    rw [@Finset.card_eq_two] at fr
    cases fr with
    | intro x fr =>
    cases fr with
    | intro y fr =>
    cases fr with
    | intro fr1 fr2 =>
    aesop

theorem emptyChiOne {V : Type} [Nonempty V] : SimpleGraph.chromaticNumber (emptyGraph V) = 1 := by
  simp only [emptyGraph_eq_bot]
  exact SimpleGraph.chromaticNumber_bot

theorem EmptyIsPerfect' {V : Type} [nemp : Nonempty V] [deq : DecidableEq V]  : isPerfect (emptyGraph V) := by
  unfold isPerfect
  intro H
  intro induced
  have emptyG2 : isEmpty (emptyGraph V) := by unfold isEmpty; unfold emptyGraph; aesop;
  have empty_is := emptyHereditary (emptyGraph V)
  have emptyH := empty_is H
  have emptyH2 := emptyH emptyG2
  have H_is_empty_G := equivIsEmpty H.coe emptyH2
  rw [H_is_empty_G]
  by_cases h234 : Nonempty H.verts
  left
  rw [EmptyOne']
  rw [emptyChiOne]
  rfl
  right
  rw [@Set.not_nonempty_iff_eq_empty'] at h234
  exact h234

  
end PerfectGraphs
