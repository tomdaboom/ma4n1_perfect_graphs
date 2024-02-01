import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Parity

--import perfect_graphs.ColouringDefs

--open perfect_graphs.ColouringDefs

namespace Cycles

theorem chromaticNumberAltDef {V : Type} (G : SimpleGraph V) (k : ℕ) (colorable : G.Colorable k) (notColorable : ¬ G.Colorable (k-1)) : G.chromaticNumber = k := by sorry


def cycle (n : ℕ) : (SimpleGraph (ZMod n)) :=
  SimpleGraph.fromRel (λ x y => x-y = 1)

example : (cycle 5).Adj 0 4 := by
  unfold cycle SimpleGraph.fromRel --SimpleGraph.Adj
  simp only

lemma adjMeansDiffIsOne {n : ℕ} (u : ZMod n) (v : ZMod n) : (cycle n).Adj u v → (u-v=1 ∨ v-u=1) := by
  intros u_v_adj
  unfold cycle at u_v_adj
  simp only [ge_iff_le, Fin.val_fin_le, SimpleGraph.fromRel_adj, ne_eq] at u_v_adj
  cases u_v_adj
  trivial

lemma minuseqrewrite {n : ℕ} (v w : ZMod n) : (v - w = 1) → (v = 1 + w) := by
  intros vminuseq
  rw [← vminuseq]
  simp only [sub_add_cancel]

lemma i_plus_one_not_both_even {n : ℕ} (i : ZMod n) : ¬ (↑(1 + i) % 2 : ZMod 2) = ((i % 2) : ZMod 2) := by
  apply?

/-
def evenCycle2Coloring {n : ℕ} (nIsEven : Even n) : (cycle n).Coloring (ZMod 2) :=
  SimpleGraph.Coloring.mk
    (λ v => v % 2)
    (by
      intros v w
      contrapose
      simp only [ne_eq, not_not]
      intros v_u_eq_mod_2
      unfold SimpleGraph.Adj; unfold cycle;
      simp only [SimpleGraph.fromRel_adj, ne_eq, not_and]
      contrapose; simp only [not_not]
    )
-/

/-
      intros v w v_w_adj
      simp only [ne_eq]
      unfold SimpleGraph.Adj at v_w_adj
      unfold cycle at v_w_adj
      simp only [SimpleGraph.fromRel_adj, ne_eq] at v_w_adj
      have diff_one := v_w_adj.right
    -/


def evenCycle2Coloring {n : ℕ} (nIsEven : Even n)
  : (cycle n).Coloring Bool :=
  SimpleGraph.Coloring.mk
    (λ v => ((v : ℕ) % 2 == 0)
    (by
      intros v w
      unfold SimpleGraph.Adj; unfold cycle;
      simp only [SimpleGraph.fromRel_adj, ne_eq, and_imp]
      contrapose; simp only [not_forall, not_not, exists_prop, and_imp]
      sorry
    )


lemma evenCycles2Colorable {n : ℕ} : (cycle (2*n)).Colorable 2 := by
  sorry

lemma cyclesNot1Colorable {n : ℕ} : ¬ (cycle n).Colorable 1 := by
  sorry

theorem evenCyclesChiIsTwo {n : ℕ} : (cycle (2*n)).chromaticNumber = 2 := by
  apply chromaticNumberAltDef
  · exact evenCycles2Colorable
  · exact cyclesNot1Colorable

--lemma if_false_branch_then_false {T : Type} {a b : T} {p : Prop} (h : ¬ p)
--  : b = (if p then a else b) := by

lemma moduloUpperBound {n : ℕ} (a b : Fin n) : a%b ≠ b := by
  sorry

lemma sumParity {n : ℕ} (a b : Fin n) (h : a - b = 1) : a%2 ≠ b%2 := by
  sorry


def cycle3Coloring {n : ℕ} : (cycle n).Coloring (ZMod 3) :=
  SimpleGraph.Coloring.mk
  (λ v => if v == n - 1 then 2 else v % 2)
  (by
    intros v w
    unfold SimpleGraph.Adj cycle
    simp only [SimpleGraph.fromRel_adj, ne_eq, CharP.cast_eq_zero, zero_sub, beq_iff_eq, and_imp]
    intros v_neq_w v_diff_w_is_one
    by_cases h : v=-1
    · rw [h]
      simp only [ite_true]
      rw [← @ne_eq, @ne_comm, @ne_eq] at v_neq_w
      rw [← h, if_neg]
      have mb := moduloUpperBound (w : Fin 3) 2
      exact id (Ne.symm mb)
      exact v_neq_w

    · rw [if_neg]
      by_cases q : w = -1
      · rw [← q, if_pos]
        have mb := moduloUpperBound (v : Fin 3) 2
        exact id (Ne.symm mb)
        triv
      · rw [if_neg]


        cases v_diff_w_is_one with
        | inl vminw => have sp := sumParity v w vminw;


        | inr wminv =>

  )
