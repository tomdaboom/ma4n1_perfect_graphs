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




theorem faveExampleG : CliqueNumber G = 2 := by
  unfold CliqueNumber
  apply equivCliqueNumber
  unfold hasNClique
  · use {0,1}
    apply IsNClique.mk
    unfold IsClique
    unfold G
    aesop_graph
    norm_num
    
  · norm_num
    unfold hasNClique
    rw [@not_exists]
    intro t
    intro f
    cases t with
    | mk val nodup => interval_cases val

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
    refine Finset.card_doubleton ?h.card_eq.h
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
    

def CompleteG (n : ℕ) : SimpleGraph (ZMod n) :=
  SimpleGraph.fromRel (λ x y => x ≠ y)

lemma Finset_imp_card_le_card (n : ℕ) (S : Finset (ZMod n)) : S ⊆ ZMod n := by
  sorry

theorem CompleteCliqueNumberIsN (n : ℕ) (h : 1 < n) : CliqueNumber (CompleteG n) = n := by
  unfold CliqueNumber
  apply equivCliqueNumber
  unfold hasNClique
  · use ZMod n
    apply IsNClique.mk
    unfold IsClique
    unfold CompleteG
    aesop_graph

  · unfold hasNClique
    rw [@not_exists]
    intro S
    rw [@isNClique_iff]
    intro f
    cases f with
    | intro fl fr =>
    have sizeofZMod := ZMod.card n
    have S' := Finset_imp_card_le_card n S
    have S'' := Finset.card_le_card S'
    rw [fr] at S''
    rw [sizeofZMod] at S''

def EmptyG (n : ℕ)  : SimpleGraph (ZMod n) :=
  SimpleGraph.fromRel (λ _ _  => false)

theorem EmptyCliqueNumberIsOne (n : ℕ) : CliqueNumber (EmptyG n) = 1 := by
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

def isEmpty {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ¬ G.Adj u v

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
  ∀ H : Subgraph G, isInducedSubgraph G H → (coe H).chromaticNumber = CliqueNumber (coe H)

theorem emptyHereditary {V : Type} (G : SimpleGraph V)(H : Subgraph G): isEmpty G → isEmpty H.coe  := by
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
theorem emptyChiOne (n : ℕ) : SimpleGraph.chromaticNumber (EmptyG n) = 1 := by
  apply chromaticNumberAltDef
  unfold EmptyG
  simp
  unfold Colorable
  refine Nonempty.intro ?colorable.val
  sorry
 -- have col := SimpleGraph.Coloring.mk (λ v : ZMod n => (0 : Fin 1)) (by 
  sorry

theorem equivIsPerfect {V : Type}
  (p : {U : Type} → SimpleGraph U → Prop)
  (G : SimpleGraph V) 
  (g_satisfies_p : p G) 
  (p_is_hereditary : ∀ H : Subgraph G, p H.coe)
  (g_min_perfect : CliqueNumber G = G.chromaticNumber) : isPerfect G := by
  sorry

theorem EmptyIsPerfect (n : ℕ) : isPerfect (EmptyG n) := by
  apply equivIsPerfect isEmpty
  unfold isEmpty
  unfold EmptyG
  aesop
  have h := emptyHereditary (EmptyG n)
  intros H
  have h' := h H
  have h'' : isEmpty (EmptyG n) := by unfold isEmpty; unfold EmptyG; aesop;
  have hIsEmptyPrime := h' h''
  unfold isEmpty' at h''
  exact hIsEmptyPrime
  rw [emptyChiOne]
  rw [EmptyCliqueNumberIsOne]


  
