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


def cycle (n : ℕ) : (SimpleGraph (ZMod n)) :=
  SimpleGraph.fromRel (λ x y => x-y = 1)


theorem chromaticNumberAltDef {V : Type} (G : SimpleGraph V) (k : ℕ) (colorable : G.Colorable k) (notColorable : ¬ G.Colorable (k-1)) : G.chromaticNumber = k := by sorry

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

--lemma odd_cycle_not_two_colorable

lemma zero_neq_1 (n : ℕ) (n_lower_bounded : n ≥ 4) : ¬ (0 : ZMod n) = 1 := by
  rw [← @ne_eq]
  refine zero_mem_nonunits.mp ?h.card_eq.h.a
  rw [@Set.mem_def]
  unfold nonunits
  rw [@Set.setOf_app_iff]
  have g : Fact (4 ≤ n) := by exact { out := n_lower_bounded } 
  have h' : Nontrivial (ZMod n) := by have g' := four_gt_one n ; have g'' := g' g; exact ZMod.nontrivial n;
  exact not_isUnit_zero

/-
  METHOD FOR FOLLOWING PROOF - first half:
  Create a coloring which colours each of 1,...,n-1 based off their parity, and then 0 a new colour.

  METHOD FOR FOLLOWING PROOF - second half:
  1) Have a hypothesis that coloring(0) ≠ coloring(1) (easy)
  2) Have a hypothesis that coloring (0) ≠ coloring(-1) (easy)
  3) Have a hypothesis that coloring (1) ≠ coloring(-1) (harder - will need to use that n is odd)
  4) We therefore have 3 vertices in the complete graph on 2 vertices - this is our contradiction
-/

lemma zero_neq_2 : (0 : Fin 3) ≠ 2 := by  
  exact (bne_iff_ne 0 2).mp rfl

theorem chiCycle3 (n : ℕ) (h : Odd n) (n_lower_bound : n ≥ 4) : (cycle n).chromaticNumber = 3 := by
  classical
  apply chromaticNumberAltDef
  · have coloring := SimpleGraph.Coloring.mk (G := cycle n)
      (λ x : ZMod n => 
        if x == 0 then (0 : Fin 3)
        else if Even x then 1
        else 2)
      (by 
        simp only [beq_iff_eq, ne_eq]
        intros v w
        unfold cycle
        simp only [SimpleGraph.fromRel_adj, ne_eq, and_imp]
        intros v_neq_w v_min_w
        · by_cases w_zero : w = 0
          · rw [w_zero]
            simp only [even_zero, ite_true, ite_eq_left_iff, not_forall, exists_prop]
            aesop <;> revert a <;> simp only [imp_false] <;> rw [← @ne_eq] <;> rw? --exact zero_neq_2
      )

    unfold SimpleGraph.Colorable
    exact Nonempty.intro coloring
    

  · norm_num
    unfold SimpleGraph.Colorable
    simp only [not_nonempty_iff]
    unfold cycle
    refine { false := ?notColorable.false }
    unfold SimpleGraph.fromRel
    simp only [ne_eq]
    unfold SimpleGraph.Coloring
    unfold SimpleGraph.Hom
    intros coloring
    simp only at coloring  
    have morphism := λ x y => RelHom.map_rel coloring (a := x) (b := y)

    have thing := morphism 0 (-1)
    norm_num at thing
    have thing' := morphism 0 1
    norm_num at thing'

    have one_neq_zero : ¬ (0 : ZMod n) = 1 := zero_neq_1 n n_lower_bound

    have col_zero_neq_one := thing' one_neq_zero

    have col_zero_neq_negone : ¬coloring 0 = coloring (-1)  := by
      rw [← @ne_eq, @ne_comm, @ne_eq] at one_neq_zero
      exact thing one_neq_zero  

  /-
    have even_coloring_lemma : 
      ∀ i : ZMod n, Even i → coloring i = coloring 0
      := by
      intros i i_even
      have i_zero_relation := morphism i 0
      by_cases i_eq_zero : i = 0
      · rw [i_eq_zero]

      · simp only [sub_zero, zero_sub, SimpleGraph.top_adj, ne_eq, and_imp] at i_zero_relation 
        have i_is_one_or_neg_one := i_zero_relation i_eq_zero
        have i_i_plus_one_morph := morphism i (i+1)
        simp only [self_eq_add_right, sub_add_cancel', add_sub_cancel', or_true, and_true, SimpleGraph.top_adj, ne_eq] at i_i_plus_one_morph
    -/

    have odd_coloring_lemma :
      ∀ i : ZMod n, Odd i → ¬ coloring i = coloring 0
      := by
      intros i i_is_odd
      intros col_i_is_zero
      have morbius := morphism i 0
      norm_num at morbius

      have i_neq_zero : ¬ i = 0 := by
        intros i_is_zero
        have zero_even := even_zero (α := ZMod n)
        rw [i_is_zero] at i_is_odd 
        




    

    
    --simp only [CharP.cast_eq_zero, zero_sub, zero_eq_neg, sub_neg_eq_add, zero_add, sub_zero, true_or, and_true, SimpleGraph.top_adj, ne_eq] at thing 

    

   /- contrapose! thing
    simp only [zero_sub, sub_zero, or_true, and_true, SimpleGraph.top_adj, ne_eq] at other_thing 

    apply And.intro
    symm
    refine zero_mem_nonunits.mp ?h.card_eq.h.a
    rw [@Set.mem_def]
    unfold nonunits
    rw [@Set.setOf_app_iff]
    have g : Fact (4 ≤ n) := by exact { out := h } 
    have h' : Nontrivial (ZMod n) := by have g' := four_gt_one n ; have g'' := g' g; exact ZMod.nontrivial n;
    exact not_isUnit_zero-/

/-
    have zne1 := zero_neq_1 n n_lower_bound 
    have h2 := other_thing zne1
    have thing2 := morphism 0 (-1)
    simp only [zero_eq_neg, sub_neg_eq_add, zero_add, sub_zero, true_or, and_true, SimpleGraph.top_adj, ne_eq] at thing2 
    have zne1theSequel : ¬(1 : ZMod n) = 0 := by 
      rw [← @ne_eq] 
      symm
      rw [@ne_eq]
      exact zne1
    have bruh := thing2 zne1theSequel
-/
    
      

    
    
    
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
    

open SimpleGraph
open Subgraph


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
                                        revert h2import Mathlib
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


def cycle (n : ℕ) : (SimpleGraph (ZMod n)) :=
  SimpleGraph.fromRel (λ x y => x-y = 1)


theorem chromaticNumberAltDef {V : Type} (G : SimpleGraph V) (k : ℕ) (colorable : G.Colorable k) (notColorable : ¬ G.Colorable (k-1)) : G.chromaticNumber = k := by sorry

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

--lemma odd_cycle_not_two_colorable

lemma zero_neq_1 (n : ℕ) (n_lower_bounded : n ≥ 4) : ¬ (0 : ZMod n) = 1 := by
  rw [← @ne_eq]
  refine zero_mem_nonunits.mp ?h.card_eq.h.a
  rw [@Set.mem_def]
  unfold nonunits
  rw [@Set.setOf_app_iff]
  have g : Fact (4 ≤ n) := by exact { out := n_lower_bounded } 
  have h' : Nontrivial (ZMod n) := by have g' := four_gt_one n ; have g'' := g' g; exact ZMod.nontrivial n;
  exact not_isUnit_zero

/-
  METHOD FOR FOLLOWING PROOF - first half:
  Create a coloring which colours each of 1,...,n-1 based off their parity, and then 0 a new colour.

  METHOD FOR FOLLOWING PROOF - second half:
  1) Have a hypothesis that coloring(0) ≠ coloring(1) (easy)
  2) Have a hypothesis that coloring (0) ≠ coloring(-1) (easy)
  3) Have a hypothesis that coloring (1) ≠ coloring(-1) (harder - will need to use that n is odd)
  4) We therefore have 3 vertices in the complete graph on 2 vertices - this is our contradiction
-/

theorem chiCycle3 (n : ℕ) (h : Odd n) (n_lower_bound : n ≥ 4) : (cycle n).chromaticNumber = 3 := by
  apply chromaticNumberAltDef
  · sorry

  · norm_num
    unfold SimpleGraph.Colorable
    simp only [not_nonempty_iff]
    unfold cycle
    refine { false := ?notColorable.false }
    unfold SimpleGraph.fromRel
    simp only [ne_eq]
    unfold SimpleGraph.Coloring
    unfold SimpleGraph.Hom
    intros coloring
    simp only at coloring  
    have morphism := λ x y => RelHom.map_rel coloring (a := x) (b := y)
    have thing    := morphism 0 (-1)
    
    norm_num at thing


    rw? at thing

    
    --simp only [CharP.cast_eq_zero, zero_sub, zero_eq_neg, sub_neg_eq_add, zero_add, sub_zero, true_or, and_true, SimpleGraph.top_adj, ne_eq] at thing 

    

   /- contrapose! thing
    simp only [zero_sub, sub_zero, or_true, and_true, SimpleGraph.top_adj, ne_eq] at other_thing 

    apply And.intro
    symm
    refine zero_mem_nonunits.mp ?h.card_eq.h.a
    rw [@Set.mem_def]
    unfold nonunits
    rw [@Set.setOf_app_iff]
    have g : Fact (4 ≤ n) := by exact { out := h } 
    have h' : Nontrivial (ZMod n) := by have g' := four_gt_one n ; have g'' := g' g; exact ZMod.nontrivial n;
    exact not_isUnit_zero-/

/-
    have zne1 := zero_neq_1 n n_lower_bound 
    have h2 := other_thing zne1
    have thing2 := morphism 0 (-1)
    simp only [zero_eq_neg, sub_neg_eq_add, zero_add, sub_zero, true_or, and_true, SimpleGraph.top_adj, ne_eq] at thing2 
    have zne1theSequel : ¬(1 : ZMod n) = 0 := by 
      rw [← @ne_eq] 
      symm
      rw [@ne_eq]
      exact zne1
    have bruh := thing2 zne1theSequel
-/
    
      

    
    
    
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
    

open SimpleGraph
open Subgraph


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


  
