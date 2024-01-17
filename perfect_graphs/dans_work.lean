import Mathlib
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
--import Mathlib.Combinatorics.SimpleGraph.Basic
--import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Clique
--import Mathlib.Combinatorics.SimpleGraph.chromaticNumber
import Mathlib.Data.Fintype.Basic
import Aesop.Check
import Mathlib.Logic.Basic
import Aesop.Tree.Data
set_option trace.aesop true



namespace PerfectGraphs

#check SimpleGraph (Fin 5)






def G : SimpleGraph (Fin 5) where
  Adj x y  :=
    x = 0 ∧ y = 1 ∨ x = 1 ∧ y = 0 ∨ x = 2 ∧ y = 3 ∨ x = 3 ∧ y = 2
  symm a b h := by
    aesop
  loopless a b := by
    aesop
    refine (?_ (id right.symm)).snd
    refine (?_ (id left.symm)).snd
    done
    

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
 verts := {0, 1}
 Adj x y := x = 0 ∧ y = 1 ∨ x = 1 ∧ y = 0 
 adj_sub := by 
  intros v w
  intro f
  unfold Adj G
  aesop
 edge_vert := by 
  aesop
 symm Symmetric Adj := by aesop_graph



open SimpleGraph
theorem subg : G' ≤ G := by
  unfold G; 
  unfold G';
  aesop_graph

#check G.Iso G'

#check (G'' : Subgraph G)

#check G'.IsSubgraph G

theorem ex : G'.IsSubgraph G := by
  unfold IsSubgraph
  unfold G G'
  aesop

def PGIsInduced {V : Type} (H : SimpleGraph V) (H' : Subgraph H) : Prop :=
  ∀ {v w : V}, v ∈ H'.verts → w ∈ H'.verts → H.Adj v w → H'.Adj v w

def PGIsInduced' {V : Type} (H : SimpleGraph V) (H' : SimpleGraph V) : Prop :=
  ∀ {v w : V}, (H.Adj v w → H'.Adj v w) ∨ (H'.neighborSet v = ∅) ∨ (H'.neighborSet w = ∅)

def F := G.toSubgraph G' subg
#check F

open Subgraph

theorem ex22 : F.IsInduced := by
  unfold F
  unfold IsInduced
  unfold G
  unfold G'
  unfold toSubgraph
  unfold SimpleGraph.Adj
  simp
  intros v w

  

theorem ex2 : PGIsInduced G G'' := by
 unfold G
 unfold G''
 unfold PGIsInduced
 aesop
 exact Fin.rev_inj.mp (id left.symm)
 exact neg_add_eq_zero.mp (id right.symm)
 rw [← right] 
 exact self_eq_add_left.mp right
 exact self_eq_add_left.mp (id right.symm)
 done

theorem ex202 : PGIsInduced' G G' := by
  unfold PGIsInduced'
  unfold G
  unfold G'
  intros v w
  cases v with
  | mk val isLt => interval_cases val;
                   · simp only; left; aesop; exact sub_eq_zero.mp (id left.symm); sorry
                   · sorry
                   · sorry
                   · sorry
                   · sorry

def hasNClique {V : Type} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ t, G.IsNClique n t

noncomputable def CliqueNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sSup { n : ℕ | hasNClique G n }

theorem equivCliqueNumber {V : Type} (G : SimpleGraph V) (k : ℕ) (NClique : hasNClique G k) (notNPlusOneClique : ¬ hasNClique G (k+1)) : CliqueNumber G = k := by
  sorry

/- Maybe can redefine this using cliqueSet -/




lemma minuseqrewrite {n : ℕ} {v w : ZMod n} : (v - w = 1) → (v = 1 + w) := by
  intros vminuseq
  rw [← vminuseq]
  simp only [sub_add_cancel]

lemma one_one_to_two {n : ℕ} {x y z : ZMod n} : (x - y = 1) → (z - x = 1) → (z - y = 2) := by
  intros xminy zminx
  have yplusone := minuseqrewrite xminy
  rw [yplusone] at zminx
  rw [add_comm] at zminx
  rw[sub_add_eq_sub_sub] at zminx
  rw [<- one_add_one_eq_two]
  rw [← zminx]
  exact eq_add_of_sub_eq (congrArg (HSub.hSub (z - y)) zminx)

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
    

def cycle (n : ℕ) : (SimpleGraph (ZMod n)) :=
  SimpleGraph.fromRel (λ x y => x-y = 1)

lemma four_gt_one (n : ℕ) (h : Fact (4 ≤ n)) : Fact (1 < n) := by
  have h' := Fact.elim h
  refine fact_iff.mpr ?_
  refine Nat.succ_le_iff.mp ?_
  norm_num
  linarith
  
lemma neg_two_ne_one {n : ℕ} (h : 3 < n) : (-2 : ZMod n) ≠ 1 := by
  rw[ne_eq, eq_comm, eq_neg_iff_add_eq_zero, add_comm, two_add_one_eq_three]
  contrapose! h
  apply Nat.le_of_dvd zero_lt_three
  exact (ZMod.nat_cast_zmod_eq_zero_iff_dvd 3 n).mp h

theorem CliqueNumberCycleIsTwo (n : ℕ) (h : n ≥ 4) : CliqueNumber (cycle n) = 2 := by
  unfold CliqueNumber
  apply equivCliqueNumber
  unfold hasNClique
  · use {0,1}
    apply IsNClique.mk
    unfold IsClique
    unfold cycle
    aesop_graph
    refine Finset.card_pair ?h.card_eq.h
    refine zero_mem_nonunits.mp ?h.card_eq.h.a
    rw [@Set.mem_def]
    unfold nonunits
    rw [@Set.setOf_app_iff]
    have g : Fact (4 ≤ n) := by exact { out := h } 
    have h' : Nontrivial (ZMod n) := by have g' := four_gt_one n ; have g'' := g' g; exact ZMod.nontrivial n;
    exact not_isUnit_zero

    
  · norm_num
    unfold hasNClique
    rw [@not_exists]
    intro x
    rw [@is3Clique_iff]
    rw [@not_exists]
    intro a
    rw [@not_exists]
    intro b
    rw [@not_exists]
    intro c
    intro f
    cases f with
    | intro f1 f2 =>
      cases f2 with
      | intro f2 f3 =>
        cases f3 with
        | intro f3 f4 =>
    revert f1
    unfold SimpleGraph.Adj
    unfold cycle
    simp
    intro f11
    intro f12
    cases f12 with
    | inl h1 => revert f2
                unfold SimpleGraph.Adj
                unfold cycle
                simp
                intro f21
                intro f22
                cases f22 with
                | inl h2 => revert f3
                            unfold SimpleGraph.Adj
                            unfold cycle
                            simp
                            intro f31
                            intro f32
                            cases f32 with
                            | inl h3 => have h1' := minuseqrewrite h1
                                        have h2' := minuseqrewrite h2
                                        rw [h1'] at h2'
                                        have h2'' := add_left_cancel h2'
                                        revert h2''
                                        exact fun h2'' => f31 h2''
                            | inr h3 => have h1' := minuseqrewrite h1
                                        have h2' := minuseqrewrite h2
                                        rw [h1'] at h2'
                                        have h2'' := add_left_cancel h2'
                                        revert h2''
                                        exact fun h2'' => f31 h2''

                | inr h2 => revert f3
                            unfold SimpleGraph.Adj
                            unfold cycle
                            simp
                            intro f31
                            intro f32
                            cases f32 with
                            | inl h3 => have h4 := one_one_to_minus_two h1 h2
                                        rw [h4] at h3
                                        revert h3
                                        rw[imp_false]
                                        rw [<- ne_eq]
                                        have h' := Nat.succ_le_iff.mp h
                                        exact neg_two_ne_one h'                                       

                            | inr h3 => have h2' := minuseqrewrite h2
                                        have h3' := minuseqrewrite h3
                                        rw [h3'] at h2'
                                        have h2'' := add_left_cancel h2'
                                        revert h2''
                                        exact fun h2'' => f11 (id h2''.symm)
    | inr h1 => revert f2
                unfold SimpleGraph.Adj
                unfold cycle
                simp
                intro f21
                intro f22
                cases f22 with
                | inl h2 => revert f3
                            unfold SimpleGraph.Adj
                            unfold cycle
                            simp
                            intro f31
                            intro f32
                            cases f32 with
                            | inl h3 => have h1' := minuseqrewrite h1
                                        have h3' := minuseqrewrite h3
                                        rw [h1'] at h3'
                                        have h3'' := add_left_cancel h3'
                                        revert h3''
                                        exact fun h3'' => f21 h3''
                            | inr h3 => have h4 := one_one_to_minus_two h1 h3
                                        rw [h4] at h2
                                        revert h2
                                        rw[imp_false]
                                        rw [<- ne_eq]
                                        have h' := Nat.succ_le_iff.mp h
                                        exact neg_two_ne_one h' 
                | inr h2 => revert f3
                            unfold SimpleGraph.Adj
                            unfold cycle
                            simp
                            intro f31
                            intro f32
                            cases f32 with
                            | inl h3 => have h1' := minuseqrewrite h1
                                        have h3' := minuseqrewrite h3
                                        rw [h1'] at h3'
                                        have h3'' := add_left_cancel h3'
                                        revert h3''
                                        exact fun h3'' => f21 h3''
                            | inr h3 => have h2' := minuseqrewrite h2
                                        have h3' := minuseqrewrite h3
                                        rw [h2'] at h3'
                                        have h3'' := add_left_cancel h3'
                                        revert h3''
                                        exact fun h3'' => f11 h3''
    


def CompleteG (n : ℕ) : SimpleGraph (Fin n) := completeGraph (Fin n)
  --SimpleGraph.fromRel (λ x y => x ≠ y)

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

/-
theorem CompleteCliqueNumberIsN (n : ℕ) (h : NeZero n) : CliqueNumber (CompleteG n) = n := by
  unfold CliqueNumber
  apply equivCliqueNumber
  unfold hasNClique
  · use Finset.univ
    apply IsNClique.mk
    unfold IsClique
    unfold CompleteG
    aesop_graph
    -- have sizeofZMod := ZMod.card n
    rw [Finset.card_univ]
    exact Fintype.card_fin n
    -- exact sizeofZMod
    

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
    rw [Finset.card_univ] at S''
    rw [fr] at S''
    rw [Fintype.card_fin n] at S''
    contrapose! S''
    norm_num
-/

/- def EmptyG' (n : ℕ)  : SimpleGraph (ZMod n) :=
  SimpleGraph.fromRel (λ _ _  => false) -/

def EmptyG (n : ℕ) : SimpleGraph (Fin n) := emptyGraph (Fin n)
 
/-
theorem EmptyCliqueNumberIsOne (n : ℕ) (h : NeZero n) : CliqueNumber (EmptyG n) = 1 := by
  unfold CliqueNumber
  apply equivCliqueNumber
  unfold hasNClique
  · use {0}
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
    unfold EmptyG
    intro fl
    simp_all
    unfold Set.Subsingleton at fl
    aesop
    rw [@Finset.card_eq_two] at fr
    cases fr with
    | intro x fr =>
    cases fr with
    | intro y fr =>
    cases fr with
    | intro fr1 fr2 =>
    aesop
-/

def isEmpty {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ¬ G.Adj u v



theorem empty_is_empty (n : ℕ) : isEmpty (EmptyG n) := by
  unfold isEmpty
  unfold EmptyG
  aesop

theorem EmptyOne' {V : Type} /- [h' : Fintype V] -/ [h : Nonempty V] [DecidableEq V]  : CliqueNumber (emptyGraph V) = 1 := by
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

theorem equivIsEmpty {V : Type} 
  /- [finV : Fintype V] [nemp : Nonempty V] -/
  (G : SimpleGraph V) (h : isEmpty G) 
  : G = (emptyGraph V) := by
  unfold emptyGraph
  unfold isEmpty at h
  aesop


 /- refine { toEquiv := ?toEquiv, map_rel_iff' := ?map_rel_iff' }
  exact Fintype.equivFin V
  
  intros a b
  unfold SimpleGraph.Adj
  apply Iff.intro

  intros h'
  exact h'.elim

  intros h'
  exact h a b h' -/



def isComplete {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ¬ u = v -> G.Adj u v

theorem equivIsComplete {V : Type} 
  /- [finV : Fintype V] [nemp : Nonempty V] -/
  (G : SimpleGraph V) (h : isComplete G) 
  : G = (completeGraph V) := by
  unfold completeGraph
  unfold isComplete at h
  aesop

--identical other than working for subgraphs, not currently using this but may be useful to have around
def isEmpty' {V : Type} {G : SimpleGraph V} (H : Subgraph G): Prop :=
  ∀ u v : H.verts, ¬ H.Adj u v

def isInducedSubgraph {V : Type} (H : SimpleGraph V) (H' : Subgraph H) : Prop :=
  ∀ {v w : V}, v ∈ H'.verts → w ∈ H'.verts → H.Adj v w → H'.Adj v w

def coe {V : Type}{G : SimpleGraph V}(H : Subgraph G) : SimpleGraph H.verts where
  Adj v w := H.Adj v w
  symm _ _ h := H.symm h
  loopless v h := loopless G v (H.adj_sub h)

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
  rfl

/- These three theorems above, combined with the fact that the graph on no vertices has no subgraphs,
 justify our inclusion of the "∨ H.verts = ∅" clause in our definition of a perfect graph. -/

  


theorem emptyHereditary {V : Type} (G : SimpleGraph V)(H : Subgraph G): isEmpty G → isEmpty H.coe  := by
  sorry

theorem completeHereditary {V : Type} (G : SimpleGraph V)(H : Subgraph G)(h1: isInducedSubgraph G H): isComplete G → isComplete H.coe  := by
  sorry

theorem chromaticNumberAltDef {V : Type} (G : SimpleGraph V) (k : ℕ) (colorable : G.Colorable k) (notColorable : ¬ G.Colorable (k-1)) : G.chromaticNumber = k := by
    /-
    unfold SimpleGraph.chromaticNumber
    refine (Nat.le_antisymm ?h₁ ?h₂).symm
    · refine (le_csInf_iff'' ?h₁.ne).mpr ?h₁.a;
        · exact SimpleGraph.colorable_set_nonempty_of_colorable colorable
      intros b bColorable
    -/
    sorry

#check emptyGraph

/- theorem emptyChiOne' (n : ℕ) : SimpleGraph.chromaticNumber (EmptyG n) = 1 := by
  apply chromaticNumberAltDef
  --unfold EmptyG
  unfold Colorable
  refine Nonempty.intro ?colorable.val
  --sorry
  exact SimpleGraph.Coloring.mk (G := EmptyG n) (λ v : ZMod n => (0 : Fin 1)) (by 
    intro v w
    unfold EmptyG
    simp only [fromRel_adj, ne_eq, or_self, and_false, not_true_eq_false, IsEmpty.forall_iff]
  )
  sorry -/
  
theorem emptyChiOne {V : Type} [Nonempty V] : SimpleGraph.chromaticNumber (emptyGraph V) = 1 := by
  simp only [emptyGraph_eq_bot]
  exact SimpleGraph.chromaticNumber_bot
  

def min_perf {U : Type} (G : SimpleGraph U) : Prop :=
  G.chromaticNumber = CliqueNumber G

theorem equivIsPerfect {V : Type}
  (p : {U : Type} → SimpleGraph U → Prop)
  (G : SimpleGraph V) 
  (g_has_p : p G)
  (p_is_hereditary : ∀ H : Subgraph G, isInducedSubgraph G H -> p G -> p H.coe)
  (g_min_perfect : {W : Type} -> ∀ L : SimpleGraph W, p L -> min_perf L) 
  : isPerfect G := by
  unfold isPerfect
  intro H
  intro induced
  have p_H := p_is_hereditary H induced
  have min_perf_h := p_H g_has_p
  have min_perf2_h := g_min_perfect H.coe min_perf_h
  unfold min_perf at min_perf2_h
  left
  exact min_perf2_h

theorem EmptyIsPerfect' {V : Type} /- [finV : Fintype V] -/ [nemp : Nonempty V] [deq : DecidableEq V]  : isPerfect (emptyGraph V) := by
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
  




/- theorem EmptyIsPerfect (n : ℕ) (nemp : NeZero n) : isPerfect (EmptyG n) := by
  apply equivIsPerfect isEmpty
  unfold isEmpty
  unfold EmptyG
  aesop
  unfold EmptyG
  intro H
  have h := emptyHereditary (EmptyG n)
  have h' := h H
  have h'' : isEmpty (EmptyG n) := by unfold isEmpty; unfold EmptyG; aesop;
  have hIsEmpty := h' h''
  intros f1 f2
  exact hIsEmpty
  unfold min_perf
  intro W
  intro L
  intro f
  have f' := equivIsEmpty L f
  rw [f']
  rw [EmptyOne']
  rw [emptyChiOne]
  rw [f'] 
  intro f
  apply chromaticNumberAltDef
  intro f
  rw [emptyChiOne]
  rw [EmptyCliqueNumberIsOne]
  rfl -/

/- ---------- -/

theorem completeChiN {V : Type} [h' : Fintype V] : SimpleGraph.chromaticNumber (completeGraph V) = (Finset.univ (α := V)).card:= by
  simp only [completeGraph_eq_top] 
  rw [@chromaticNumber_top]
  rfl


/-
theorem CompleteIsPerfect (n : ℕ) (n_not_zero : NeZero n) : isPerfect (CompleteG n) := by
  apply equivIsPerfect isComplete
  unfold CompleteG
  intro H
  intro induced
  have h := completeHereditary (CompleteG n)
  have h' := h H
  have h'' : isComplete (CompleteG n) := by unfold isComplete; unfold CompleteG; aesop;
  have hIsComplete := h' induced h''
  intro F
  exact hIsComplete
  unfold min_perf
  rw [completeChiN]
  rw [CompleteCliqueNumberIsN]
  exact n_not_zero
-/

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
