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
--------------------------------------------------------------------------

--Note: this will sometimes be referred to as chi(G) or just chi if context is clear

--TBD: Tom proof
--Align the definition of chromatic number to a computable one
theorem chromaticNumberAltDef {V : Type} (G : SimpleGraph V) (k : ℕ) (colorable : G.Colorable k) (notColorable : ¬ G.Colorable (k-1)) : G.chromaticNumber = k := by
    sorry

--------------------------------------------------------------------------
--SECTION: CLIQUE NUMBER
--------------------------------------------------------------------------

--Note: this will sometimes be referred to as omega(G) or just omega if context is clear

--Can induce an n clique
def hasNClique {V : Type} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ t, G.IsNClique n t

--Non-computable definition of clique number
noncomputable def CliqueNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sSup { n : ℕ | hasNClique G n }

--Lemmas towards computable definition of clique number
lemma cliqueNumberInductionLemma
  {V : Type} (G : SimpleGraph V) [DecidableEq V]
  (n: ℕ) (n_bound : n ≥ 1)
  : hasNClique G n → hasNClique G (n-1) := by
  unfold hasNClique
  intros h
  aesop
  rw [@isNClique_iff] at h_1
  cases h_1 with
  | intro clique card =>
  have w_nonempty : Nonempty w := by
    simp only [nonempty_subtype]
    rw [@Nat.le_antisymm_iff] at card
    cases card with
    | intro lower upper =>
    have one_le_w := le_trans' upper n_bound
    exact Multiset.card_pos_iff_exists_mem.mp one_le_w
  simp only [nonempty_subtype] at w_nonempty
  have elem_of_w := w_nonempty.choose_spec
  have subset_of_w := w \ { Exists.choose w_nonempty }
  use w \ { Exists.choose w_nonempty }
  apply IsNClique.mk
  unfold IsClique
  unfold Set.Pairwise
  aesop_graph
  rw [← card]
  apply Finset.card_sdiff
  exact Finset.singleton_subset_iff.mpr elem_of_w

lemma cNcontra {V : Type} (G : SimpleGraph V) [DecidableEq V]
  (n: ℕ) (n_bound : n ≥ 1) : ¬ hasNClique G (n)  -> ¬ hasNClique G (n + 1):= by
  intros h
  contrapose! h
  refine id ?a
  have k := cliqueNumberInductionLemma G (n+1) (by exact Nat.le_add_left 1 n) h
  norm_num at k
  exact k

lemma cNcontraInduct {V : Type} (G : SimpleGraph V) [DecidableEq V]
  (n a : ℕ) (n_bound : n ≥ 1) : ¬ hasNClique G (n)  -> ¬ hasNClique G (n + a) := by
  induction a with
  | zero      => simp only [Nat.zero_eq, add_zero, imp_self]
  | succ a ih =>
    intros noNclique
    have nonaclique := ih noNclique
    rw [Nat.succ_eq_add_one, <- add_assoc]
    exact cNcontra G (n+a) (by exact le_add_right n_bound) nonaclique

--Computable definition of Clique Number
theorem equivCliqueNumber
  {V : Type} (G : SimpleGraph V) [DecidableEq V] (k : ℕ) (k_bound : k ≥ 1)
  (NClique : hasNClique G k)
  (notNPlusOneClique : ¬ hasNClique G (k+1)) : CliqueNumber G = k
  := by
  unfold CliqueNumber
  refine IsGreatest.csSup_eq ?H
  unfold IsGreatest
  aesop
  unfold upperBounds
  simp only [Set.mem_setOf_eq]
  intros a
  have z := λ b : ℕ => cNcontraInduct G (k+1) b (by exact Nat.le_add_left 1 k) notNPlusOneClique
  intro hasAclique
  rw [← @Nat.lt_add_one_iff]
  contrapose! hasAclique
  have isAp : ∃ p, k + 1 + p = a := by exact Nat.le.dest hasAclique
  have b_rw := isAp.choose_spec
  have j := z (isAp.choose)
  rw [← b_rw]
  exact j

--------------------------------------------------------------------------
--SECTION: PERFECT DEFINITIONS
--------------------------------------------------------------------------

--TBD: standardise subgraph letters eg H H' vs G H
--Can a subgraph be induced from the graph it's a subgraph of
def isInducedSubgraph {V : Type} (G : SimpleGraph V) (H : Subgraph G) : Prop :=
  ∀ {u v: V}, u ∈ H.verts → v ∈ H.verts → G.Adj u v → H.Adj u v

--Standard definition of perfect
--The H.verts = ∅ case prevents logical error (see comment at the end of this section)
def isPerfect {V : Type} (G : SimpleGraph V) : Prop :=
  G.chromaticNumber = CliqueNumber G ∧ (∀ H : Subgraph G, isInducedSubgraph G H → (H.coe).chromaticNumber = CliqueNumber (H.coe) ∨ (H.verts = ∅))

--We'll now work with the graph on no vertices
--Note: the graph has the "Empty" type vertex set, but is *not* empty itself (by definition of empty graphs)

--Prove the clique number of the graph on no vertices is 0
theorem emptyVertsClique (G : SimpleGraph Empty) : CliqueNumber G = 0 := by
 apply equivCliqueNumber
 --Has 0 clique
 ·unfold hasNClique
  use ∅
  aesop
  --Doesn't have 1 clique
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

--Prove the chromatic number of the graph on no vertices is 0 by rewriting an exisiting theorem
theorem emptyVertsChrom (G : SimpleGraph Empty) : G.chromaticNumber = 0 := by
  rw [@chromaticNumber_eq_zero_of_isempty]

--A graph on no vertices has its chromatic number equal to its clique number (both 0)
theorem minperfEmptyVerts (G : SimpleGraph Empty) : G.chromaticNumber = CliqueNumber G := by
  rw [emptyVertsChrom]
  rw [emptyVertsClique]
  rfl

/- These three theorems above, combined with the fact that the graph on no vertices has no subgraphs,
 justify our inclusion of the "∨ H.verts = ∅" clause in our definition of a perfect graph. -/


--------------------------------------------------------------------------
--SECTION: EMPTY GRAPHS
--------------------------------------------------------------------------

--Adjacency in the coercion of a subgraph into a graph type is the same as adjacency in the subgraph
lemma coeAdj  {V : Type} {G : SimpleGraph V}(H : Subgraph G)(u v : H.verts): SimpleGraph.Adj (Subgraph.coe H) u v ↔ Subgraph.Adj (H) u v := by
  exact Iff.rfl

--A graph is empty if it has no edges, so no two vertices are adjacent
def isEmpty {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ¬ G.Adj u v


--Essentially a rewritten version of adj_sub, but useful for proofs
lemma edgeNotInGraphNotInSubgraph {V : Type}(G : SimpleGraph V)(H : Subgraph G): ∀ u v : V, ¬ G.Adj u v → ¬ H.Adj u v
:= by
  intro u v
  contrapose
  rw[not_not,not_not]
  apply adj_sub

--The class of empty graphs is a hereditary class
--Which is to say any subgraph of an empty graph is also empty
theorem emptyHereditary {V : Type} (G : SimpleGraph V)(H : Subgraph G): isEmpty G → isEmpty H.coe  := by
  unfold isEmpty
  intros h u v
  rw [coeAdj]
  exact edgeNotInGraphNotInSubgraph G H u v (h u v)

--Aligns isEmpty definition with the empty graph type
--The former is more useful in statements of theorems etc, the latter more useful for the clique number proof
theorem equivIsEmpty {V : Type}
  /- [finV : Fintype V] [nemp : Nonempty V] -/
  (G : SimpleGraph V) (h : isEmpty G)
  : G = (emptyGraph V) := by
  unfold emptyGraph
  unfold isEmpty at h
  aesop

--The clique number of an empty graph is 1
--TBD: fix
theorem EmptyCliqueOne {V : Type}[h : Nonempty V] [DecidableEq V]  : CliqueNumber (emptyGraph V) = 1 := by
  apply equivCliqueNumber
  unfold hasNClique
  --There is a 1 clique
  · use {h.some}
    apply IsNClique.mk
    unfold IsClique
    norm_num
    norm_num
  --There isn't a 2 clique
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

--Chromatic number of an empty graph is 1
theorem emptyChiOne {V : Type} [Nonempty V] : SimpleGraph.chromaticNumber (emptyGraph V) = 1 := by
  simp only [emptyGraph_eq_bot]
  exact SimpleGraph.chromaticNumber_bot

--Proving an empty graph is perfect, using its hereditary property
theorem EmptyIsPerfect {V : Type} [nemp : Nonempty V] [deq : DecidableEq V]  : isPerfect (emptyGraph V) := by
  unfold isPerfect
  apply And.intro
  rw [EmptyCliqueOne]
  rw [emptyChiOne]
  rfl
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
  rw [EmptyCliqueOne]
  rw [emptyChiOne]
  rfl
  right
  rw [@Set.not_nonempty_iff_eq_empty'] at h234
  exact h234


--------------------------------------------------------------------------
--SECTION: COMPLETE GRAPHS
--------------------------------------------------------------------------

--A graph is complete if any two distinct vertices are adjacent
def isComplete {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ¬ u = v -> G.Adj u v

--If an edge uv exists in a graph and the vertices u and v both exist in the subgraph, then uv is also an edge in the subgraph
lemma edgeInGraphInInducedSubgraph {V : Type}(G : SimpleGraph V)(H : Subgraph G)(h: isInducedSubgraph G H): ∀ u v : H.verts , G.Adj u v → H.Adj u v
:= by
  intro v w
  rw[isInducedSubgraph] at h
  apply h
  simp only [Subtype.coe_prop]
  exact Subtype.mem w


--Very similar to lemma above but adds in a u ≠ v clause, which allows synergy with the perfect graph definition
 lemma distinctEdgeInGraphInInducedSubgraph {V : Type}(G : SimpleGraph V)(H : Subgraph G)(h: isInducedSubgraph G H): ∀ u v : H.verts , ( ¬u = v → G.Adj u v) → ( ¬u = v → H.Adj u v)
:= by
  intro u v
  rw[isInducedSubgraph] at h
  exact fun a a_1 => edgeInGraphInInducedSubgraph G H h u v (a a_1)

--The class of complete graphs is a hereditary class
theorem completeHereditary {V : Type} (G : SimpleGraph V)(H : Subgraph G)(h1: isInducedSubgraph G H): isComplete G → isComplete H.coe  := by
  unfold isComplete
  intros h2 u v --for vertices
  unfold isInducedSubgraph at h1
  rw [coeAdj]
  intro h3
  apply distinctEdgeInGraphInInducedSubgraph G H h1 u v (fun uv => h2 u v ?_) h3
  intro huv
  apply uv
  exact SetCoe.ext huv

--Aligns the isComplete definition with the CompleteGraph type
lemma equivIsComplete {V : Type}
  /- [finV : Fintype V] [nemp : Nonempty V] -/
  (G : SimpleGraph V) (h : isComplete G)
  : G = (completeGraph V) := by
  unfold completeGraph
  unfold isComplete at h
  aesop

--TBD: fix?
--Proves the clique number of a complete graph on n vertices is n
theorem CompleteCliqueN {V : Type} [h' : Fintype V] [h : Nonempty V] [deq : DecidableEq V] : CliqueNumber (completeGraph V) = (Finset.univ (α := V)).card := by
  apply equivCliqueNumber
  unfold hasNClique
  --Has n clique
  · use Finset.univ
    apply IsNClique.mk
    unfold IsClique
    unfold completeGraph
    aesop_graph
    rfl
--Doesn't have (n+1) clique
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

--Prove the chromatic number of a complete graph on n vertices is n
theorem completeChiN {V : Type} [h' : Fintype V] : SimpleGraph.chromaticNumber (completeGraph V) = (Finset.univ (α := V)).card:= by
  simp only [completeGraph_eq_top]
  rw [@chromaticNumber_top]
  rfl

--Prove a complete graph is perfect, using its hereditary property
theorem CompleteIsPerfect {V : Type}  [finV : Fintype V]  [nemp : Nonempty V] [deq : DecidableEq V]  : isPerfect (completeGraph V) := by
  classical
  unfold isPerfect
  apply And.intro
  rw [CompleteCliqueN]
  rw [completeChiN]
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
    rw [CompleteCliqueN]
    rw [completeChiN]
  · right
    rw [@Set.not_nonempty_iff_eq_empty'] at h234
    exact h234

--------------------------------------------------------------------------
--SECTION: CYCLES
--------------------------------------------------------------------------

--Use Z mod n to define cycles using the relations between vertices
def cycle (n : ℕ) : (SimpleGraph (ZMod n)) :=
  SimpleGraph.fromRel (λ x y => x-y = 1)

--The following lemmas are used in the proof of
--a cycle's clique number being 2 and/or its chromatic number being 3

--Rewrites two elements of Z mod n with a difference of 1
lemma minuseqrewrite {n : ℕ} {u v: ZMod n} : (u - v = 1) → (u = 1 + v) := by
  intros vminuseq
  rw [← vminuseq]
  simp only [sub_add_cancel]

--Uses transitivity to find elements with a difference of 2 in Z mod n
lemma one_one_to_two {n : ℕ} {x y z : ZMod n} : (x - y = 1) → (z - x = 1) → (z - y = 2) := by
  intros xminy zminx
  have yplusone := minuseqrewrite xminy
  rw [yplusone] at zminx
  rw [add_comm] at zminx
  rw[sub_add_eq_sub_sub] at zminx
  rw [<- one_add_one_eq_two]
  rw [← zminx]
  exact eq_add_of_sub_eq (congrArg (HSub.hSub (z - y)) zminx)

--Similar to one_one_to_two but with the "smaller" element first
lemma one_one_to_minus_two {n : ℕ} {x y z : ZMod n} : (x - y = 1) → (z - x = 1) → (y - z = -2) := by
  intros xminy zminx
  have yplusone := minuseqrewrite xminy
  rw [yplusone] at zminx
  rw [add_comm] at zminx
  rw[sub_add_eq_sub_sub] at zminx
  rw [<- one_add_one_eq_two]
  rw [neg_add]
  rw [@eq_add_neg_iff_add_eq]
  rw [← @eq_neg_add_iff_add_eq]
  rw [@neg_sub]
  symm
  rwa [<- sub_eq_add_neg]

--If n ≥ 4 then it is certainly > 1
--This is required due to how "Fact" is used in the non-triviality of Z mod n
lemma four_gt_one (n : ℕ) (h : Fact (4 ≤ n)) : Fact (1 < n) := by
  have h' := Fact.elim h
  refine fact_iff.mpr ?_
  refine Nat.succ_le_iff.mp ?_
  norm_num
  linarith

--If n > 3 mod n then n - 2 ≠ 1 mod n
lemma neg_two_ne_one {n : ℕ} (h : 3 < n) : (-2 : ZMod n) ≠ 1 := by
  rw[ne_eq, eq_comm, eq_neg_iff_add_eq_zero, add_comm, two_add_one_eq_three]
  contrapose! h
  apply Nat.le_of_dvd zero_lt_three
  exact (ZMod.nat_cast_zmod_eq_zero_iff_dvd 3 n).mp h

--TBD: proof?
theorem chiCycle3 (n : ℕ) (h : Odd n) : (cycle n).chromaticNumber = 3 := by
  sorry

--Proof that the clique number of any cycle is 2
theorem CliqueNumberCycleIsTwo (n : ℕ) (h : n ≥ 4) : CliqueNumber (cycle n) = 2 := by
  unfold CliqueNumber
  apply equivCliqueNumber
  unfold hasNClique
  --Has 2 clique
  --For our 2- clique we will use vertices 0 and 1, then show they're a clique
  · use {0,1}
    apply IsNClique.mk
    unfold IsClique
    unfold cycle
    aesop_graph
    --Prove non-triviality
    refine Finset.card_pair ?h.card_eq.h
    refine zero_mem_nonunits.mp ?h.card_eq.h.a
    rw [@Set.mem_def]
    unfold nonunits
    rw [@Set.setOf_app_iff]
    have g : Fact (4 ≤ n) := by exact { out := h }
    have h' : Nontrivial (ZMod n) := by have g' := four_gt_one n ; have g'' := g' g; exact ZMod.nontrivial n;
    exact not_isUnit_zero
  --Doesn't have 3 clique
  · norm_num
    unfold hasNClique
    rw [@not_exists]
    intro x --The set which is not a 3 clique
    rw [@is3Clique_iff]
    rw [@not_exists]
    intro a --First vertex of x
    rw [@not_exists]
    intro b --Second vertex of x
    rw [@not_exists]
    intro c --Third vertex of x
    intro f
    --Splits up all the individual adjacencies to prove/ disprove
    --Requires a lot of work of all the cases of the vertices being bigger or smaller than each other
    cases f with
    | intro f1 f2 =>
      cases f2 with
      | intro f2 f3 =>
        cases f3 with
        | intro f3 f4 =>
    --We'll assume the edges ac and bc exist, then show that a and b can't be adjacent
    revert f1
    unfold SimpleGraph.Adj
    unfold cycle
    simp
    intro f11 --Hypothesis: a and b distinct
    intro f12 --Hypothesis: a and b are one apart (either a > b or b > a)
    cases f12 with
    --Case: a > b
    | inl h1 => revert f2
                unfold SimpleGraph.Adj
                unfold cycle
                simp
                intro f21 --Hypothesis: a and c distinct (used in introduction of f22)
                intro f22 --Hypothesis: a and c are one apart (either a > c or c > a)
                cases f22 with
                --Case: a > c
                | inl h2 => revert f3
                            unfold SimpleGraph.Adj
                            unfold cycle
                            simp
                            intro f31 --Hypothesis: b and c distinct
                            intro f32 --Hypothesis: b and c are one apart (either b > c or c > b)
                            cases f32 with
                            --Case: b > c
                            | inl h3 => have h1' := minuseqrewrite h1
                                        have h2' := minuseqrewrite h2
                                        rw [h1'] at h2'
                                        have h2'' := add_left_cancel h2'
                                        revert h2''
                                        exact fun h2'' => f31 h2''
                            --Case: c > b
                            | inr h3 => have h1' := minuseqrewrite h1
                                        have h2' := minuseqrewrite h2
                                        rw [h1'] at h2'
                                        have h2'' := add_left_cancel h2'
                                        revert h2''
                                        exact fun h2'' => f31 h2''
                --Case: c > a
                | inr h2 => revert f3
                            unfold SimpleGraph.Adj
                            unfold cycle
                            simp
                            intro f31 --Hypothesis: b and c distinct
                            intro f32 --Hypothesis: b and c are one apart (either b > c or c > b)
                            cases f32 with
                            --Case: b > c
                            | inl h3 => have h4 := one_one_to_minus_two h1 h2
                                        rw [h4] at h3
                                        revert h3
                                        rw[imp_false]
                                        rw [<- ne_eq]
                                        have h' := Nat.succ_le_iff.mp h
                                        exact neg_two_ne_one h'
                            --Case: c > b
                            | inr h3 => have h2' := minuseqrewrite h2
                                        have h3' := minuseqrewrite h3
                                        rw [h3'] at h2'
                                        have h2'' := add_left_cancel h2'
                                        revert h2''
                                        exact fun h2'' => f11 (id h2''.symm)
    --Case: b > a
    | inr h1 => revert f2
                unfold SimpleGraph.Adj
                unfold cycle
                simp
                intro f21 --Hypothesis: a and c distinct
                intro f22 --Hypothesis: a and c are one apart (either a > c or c > a)
                cases f22 with
                --Case: a > c
                | inl h2 => revert f3
                            unfold SimpleGraph.Adj
                            unfold cycle
                            simp
                            intro f31 --Hypothesis: b and c distinct
                            intro f32 --Hypothesis: b and c are one apart (either b > c or c > b)
                            cases f32 with
                            --Case: b > c
                            | inl h3 => have h1' := minuseqrewrite h1
                                        have h3' := minuseqrewrite h3
                                        rw [h1'] at h3'
                                        have h3'' := add_left_cancel h3'
                                        revert h3''
                                        exact fun h3'' => f21 h3''
                            --Case: c > b
                            | inr h3 => have h4 := one_one_to_minus_two h1 h3
                                        rw [h4] at h2
                                        revert h2
                                        rw[imp_false]
                                        rw [<- ne_eq]
                                        have h' := Nat.succ_le_iff.mp h
                                        exact neg_two_ne_one h'
                --Case: c > a
                | inr h2 => revert f3
                            unfold SimpleGraph.Adj
                            unfold cycle
                            simp
                            intro f31 --Hypothesis: b and c distinct
                            intro f32 --Hypothesis: b and c are one apart (either b > c or c > b)
                            cases f32 with
                            --Case: b > c
                            | inl h3 => have h1' := minuseqrewrite h1
                                        have h3' := minuseqrewrite h3
                                        rw [h1'] at h3'
                                        have h3'' := add_left_cancel h3'
                                        revert h3''
                                        exact fun h3'' => f21 h3''
                            --Case: c > b
                            | inr h3 => have h2' := minuseqrewrite h2
                                        have h3' := minuseqrewrite h3
                                        rw [h2'] at h3'
                                        have h3'' := add_left_cancel h3'
                                        revert h3''
                                        exact fun h3'' => f11 h3''

--TBD: this proof
--Prove any odd cycle is imperfect using chi = 3 and omega = 2 from earlier proofs
theorem oddCycleNotPerfect (n : ℕ) (h : Odd n) (h2 : n ≥ 4) : ¬isPerfect (cycle n) := by
  unfold isPerfect
  rw [chiCycle3 n h]
  rw [CliqueNumberCycleIsTwo]
  rw [@not_and]
  intro f1
  intro f2
  contrapose! f1
  norm_num
  exact h2

--------------------------------------------------------------------------
--SECTION: PERFECT GRAPH THEOREMS
--------------------------------------------------------------------------

--Can induce an N cycle in a graph
def hasNCycle {V : Type} (G : SimpleGraph V) (n : Nat) : Prop :=
  ∃ u, ∃ p : G.Walk u u, p.IsCycle ∧ p.length = n

--Can induce an odd hole in a graph
def hasOddHole {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ n : ℕ, hasNCycle G (2*n+5) --odd cycle of length ≥ 5, using that 0 ∈ ℕ in Lean

--Statement of Strong Perfect Graph Theorem
theorem strongPerfectGraphTheorem {V : Type} (G : SimpleGraph V)
 : isPerfect G ↔ ¬ hasOddHole G ∧ ¬ hasOddHole Gᶜ := by
  sorry


--Proving G is perfect → Gᶜ is perfect using the Strong Perfect Graph Theorem
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

--------------------------------------------------------------------------
--SECTION: EXAMPLE APPLICATION OF SPGT
--------------------------------------------------------------------------

/- We now prove that the cycle on 5 vertices is perfect
using the statement of the Strong Perfect Graph Theorem above -/

/-Use the fact that 5 > 1 to show Z mod 5 is non-trivial
As we're working on the 5 cycle, Z mod 5 will be the data type of our vertices for this section-/
lemma five_gt_one : Fact (1 < 5) := by
  refine fact_iff.mpr ?_
  refine Nat.succ_le_iff.mp ?_
  norm_num

--Needed to show adjacencies
lemma zmod5nontrivial : Nontrivial (ZMod 5):= by
  have h := five_gt_one
  exact ZMod.nontrivial 5


--Any two vertices that are 1 apart (mod 5) in the cycle are adjacent
lemma adjacencies (u v : ZMod 5)  (h: v-u=1  ): (cycle 5).Adj u v := by
  unfold cycle
  have h' := zmod5nontrivial
  simp_all only [SimpleGraph.fromRel_adj, ne_eq, or_true, and_true]
  intro
  simp_all only [sub_self, zero_ne_one]



--These are all used to construct our graph
lemma oneminuszero : (1: ZMod 5)-0=1 := by norm_num
lemma  twominusone : (2: ZMod 5)-1=1  := by norm_num
lemma  threeminustwo : (3: ZMod 5)-2=1  := by norm_num
lemma  fourminusthree : (4: ZMod 5)-3=1  := by norm_num
lemma  zerominusfour : (0: ZMod 5)-4=1  := by
  simp_all only [zero_sub]
  apply Eq.refl

--Generic vertex relation
lemma uplusoneminusu (n : ℕ) (u : ZMod n): u+1-u=1 := by
  simp_all only [add_sub_cancel']


--Use SimpleGraph's Walk type to construct a cycle of length 5 and show the relevant vertices are adjacent
def  cycle5Walk : SimpleGraph.Walk (cycle 5) 0 0  :=
  (adjacencies 0 1  oneminuszero).toWalk.append
  ((adjacencies 1 2 twominusone).toWalk.append
  ((adjacencies 2 3 threeminustwo).toWalk.append
  ((adjacencies 3 4 fourminusthree).toWalk.append
  (adjacencies  4 0 zerominusfour).toWalk)))

--Show our cycle 5 is not "nil" i.e. not a walk from a vertex to itself
lemma cycle5WalkisnotNill : cycle5Walk ≠ SimpleGraph.Walk.nil := by
  unfold cycle5Walk
  simp_all only [SimpleGraph.Walk.cons_append, SimpleGraph.Walk.nil_append, ne_eq, not_false_eq_true]

--The following 4 lemmas relate to which of the elements of Z mod 5 0 is not equal to
lemma zero_ne_one' (h': Nontrivial (ZMod 5)) (h: (0: ZMod 5) = 1) : False := by
  simp_all only [zero_ne_one]

lemma zero_ne_two : (0 : ZMod 5) = 2 -> False := by
  have h : 2<5 := by norm_num
  simp only [imp_false]
  contrapose! h
  apply Nat.le_of_dvd zero_lt_two
  symm at h
  exact (ZMod.nat_cast_zmod_eq_zero_iff_dvd 2 5).mp h

lemma zero_ne_three : (0 : ZMod 5) = 3 -> False := by
  have h : 3<5 := by norm_num
  simp only [imp_false]
  contrapose! h
  apply Nat.le_of_dvd zero_lt_three
  symm at h
  exact (ZMod.nat_cast_zmod_eq_zero_iff_dvd 3 5).mp h

lemma zero_ne_four : (0 : ZMod 5) = 4 -> False := by
  have h : 4<5 := by norm_num
  simp only [imp_false]
  contrapose! h
  apply Nat.le_of_dvd zero_lt_four
  symm at h
  exact (ZMod.nat_cast_zmod_eq_zero_iff_dvd 4 5).mp h

/- Support = the list of vertices the walk visits in order
Tail of the support = the final vertex the walk visits
This theorem checks that vertices are not visited more than once in the walk (except maybe the start and end vertex of the cycle)
To do so it must check that there are no equivalences in the vertices mod 5 -/
theorem cycle5Walktailnodup : cycle5Walk.support.tail.Nodup := by
  unfold cycle5Walk
  have h' := zmod5nontrivial
  simp only [SimpleGraph.Walk.cons_append, SimpleGraph.Walk.nil_append,
    SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons, List.nodup_cons,
    List.mem_cons, List.mem_singleton, one_ne_zero, or_false, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_self, and_true]
  aesop
  --1 ≠ 2
  · rw [<- add_right_cancel_iff (a := -1)] at h
    norm_num at h
    exact zero_ne_one' h' h
  --1 ≠ 3
  · rw [<- add_right_cancel_iff (a := -1)] at h
    norm_num at h
    exact zero_ne_two h
  --1 ≠ 4
  · rw [<- add_right_cancel_iff (a := -1)] at h
    norm_num at h
    exact zero_ne_three h
  --2 ≠ 3
  · rw [<- add_right_cancel_iff (a := -2)] at h
    norm_num at h
    exact zero_ne_one' h' h
  --2 ≠ 4
  · rw [<- add_right_cancel_iff (a := -2)] at h
    norm_num at h
    exact zero_ne_two h
  --0 ≠ 2
  · symm at h
    exact zero_ne_two h
    --3 ≠ 4
  · rw [<- add_right_cancel_iff (a := -3)] at h
    norm_num at h
    exact zero_ne_one' h' h
  --0 ≠ 3
  · symm at h
    exact zero_ne_three h
  --0 ≠ 4
  · symm at a
    exact zero_ne_four a
  done

/-Shows cycle 5 is a trail (a walk with no repeating edges)
Again this requires proving a lot of non-equivalences in Z mod 5
Many of the intermediary goals are combinations of non-equalities and so are not commented -/
theorem cycle5WalkisTrail : cycle5Walk.IsTrail := by
  have h' := zmod5nontrivial
  unfold cycle5Walk
  aesop
  · exact zero_ne_three (id left.symm)
  --3 ≠ 0
  · symm at h
    exact zero_ne_three h
  · rw [<- add_right_cancel_iff (a := -2)] at left
    norm_num at left
    exact zero_ne_two left
  --2 ≠ 4
  · rw [<- add_right_cancel_iff (a := -2)] at h
    norm_num at h
    exact zero_ne_two h
  · symm at right
    exact zero_ne_three right
  · symm at left
    exact zero_ne_two left
  · rw [<- add_right_cancel_iff (a := -1)] at left
    norm_num at left
    exact zero_ne_two left
    --1 ≠ 3
  · rw [<- add_right_cancel_iff (a := -1)] at h
    norm_num at h
    exact zero_ne_two h
  · rw [<- add_right_cancel_iff (a := -1)] at left
    norm_num at left
    exact zero_ne_two left
  · rw [<- add_right_cancel_iff (a := -1)] at left
    norm_num at left
    exact zero_ne_three left
  · symm at right
    exact zero_ne_two right
  · exact zero_ne_two h --0 ≠ 2
  · exact zero_ne_two left
  · exact zero_ne_three left
  · exact zero_ne_three left
  · exact zero_ne_four left
  --1 ≠ 4
  · rw [<- add_right_cancel_iff (a := -1)] at h
    norm_num at h
    exact zero_ne_three h
  done



-- This is defined in simplegraph.walk.connectivity file but we ran into issues so have copied across the isCycle definition
universe u  symm at h
  exact (ZMod.nat_cast_zmod_eq_zero_iff_dvd 4 n).mp h
variable {V : Type u}
variable (G : SimpleGraph V)
theorem isCycle_def {u : V} (p : G.Walk u u) :
    p.IsCycle ↔ p.IsTrail ∧ p ≠ SimpleGraph.Walk.nil ∧ p.support.tail.Nodup :=
  Iff.intro (fun h => ⟨h.1.1, h.1.2, h.2⟩) fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩


--Combine all elements to show a cycle of length 5 is a cycle
def cycle5WalkisCycle : cycle5Walk.IsCycle := by
  rw [isCycle_def]
  constructor
  apply cycle5WalkisTrail
  constructor
  apply cycle5WalkisnotNill
  apply cycle5Walktailnodup

  done

--Show the length of a 5 cycle is 5
def cycle5WalkLength5 : cycle5Walk.length=5 := by
  apply Eq.refl (SimpleGraph.Walk.length cycle5Walk)


--Use our definition, hasNCycle, to show a 5 cycle contains a 5 cycle
theorem cycle5hasc5 : hasNCycle (cycle 5) 5  := by
  unfold hasNCycle
  use 0
  use cycle5Walk
  constructor
  {  apply cycle5WalkisCycle
  }
  { apply cycle5WalkLength5
  }

--Use our definition, hasOddHole, to show that the 5 cycle contains an odd hole
theorem cycle5hasOddHole : hasOddHole (cycle 5) := by
  unfold hasOddHole
  use 0
  exact cycle5hasc5


--Finally, use Strong Perfect Graph Theorem to show a 5 cycle is not a perfect graph
theorem cycle5notPerfect : ¬ isPerfect (cycle 5) := by
  rw [strongPerfectGraphTheorem]
  simp only [not_and_or]
  rw [not_not]
  refine Or.inl ?h
  exact cycle5hasOddHole




end PerfectGraphs
