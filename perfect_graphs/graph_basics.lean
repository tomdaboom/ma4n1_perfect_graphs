import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
--import Mathlib.Combinatorics.SimpleGraph.Basic
--import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
--import Mathlib.Combinatorics.SimpleGraph.chromaticNumber
import Mathlib.Data.Fintype.Basic


namespace PerfectGraphs

#check SimpleGraph
#check SimpleGraph.chromaticNumber
#check emptyGraph ℕ

#check Fin 5

#check SimpleGraph (Fin 5)

def finiteEmpty (n : ℕ) := emptyGraph (Fin n)

--def finiteChromaticNumber {V : Type} [Fintype V] (G : SimpleGraph V) : Set ℕ
--    :=  {n | SimpleGraph.Colorable G n ∧ n ≤ Fintype.card V}

theorem chromaticNumberAltDef {V : Type} (G : SimpleGraph V) (k : ℕ) (colorable : G.Colorable k) (notColorable : ¬ G.Colorable (k-1)) : G.chromaticNumber = k := by
    /-
    unfold SimpleGraph.chromaticNumber
    refine (Nat.le_antisymm ?h₁ ?h₂).symm
    · refine (le_csInf_iff'' ?h₁.ne).mpr ?h₁.a;
        · exact SimpleGraph.colorable_set_nonempty_of_colorable colorable
      intros b bColorable
    -/
    sorry

def uniformColouring {V : Type} : SimpleGraph.Coloring (emptyGraph V) ℕ :=
    SimpleGraph.Coloring.mk (λ _ : V => 0) (by
        intros v w
        simp only [SimpleGraph.emptyGraph_eq_bot, SimpleGraph.bot_adj, ne_eq, IsEmpty.forall_iff]
    )

theorem emptyOneColorable {V : Type} : SimpleGraph.Colorable (emptyGraph V) 1 := by
    refine (SimpleGraph.colorable_iff_exists_bdd_nat_coloring 1).mpr ?_
    exists uniformColouring
    intros v
    exact Nat.lt_one_iff.mpr rfl


--lemma notZeroColorable {G : SimpleGraph V} : ¬ SimpleGraph.Colorable

theorem emptyChiOne {V : Type} : SimpleGraph.chromaticNumber (emptyGraph V) = 1 := by
    apply chromaticNumberAltDef
    · exact emptyOneColorable
    · simp only [SimpleGraph.emptyGraph_eq_bot, le_refl, tsub_eq_zero_of_le]
      unfold SimpleGraph.Colorable
      sorry

lemma irreflexiveAltDef {V : Type} (rel : V → V → Prop) (irrefl : Irreflexive rel) (x y : V) : rel x y → ¬ x = y := by
    intros x_rel_y
    unfold Irreflexive at irrefl
    sorry

def trivialColouring {n : ℕ} (G : SimpleGraph (Fin n)) : SimpleGraph.Coloring G ℕ :=
    SimpleGraph.Coloring.mk (λ v : Fin n => (v : ℕ)) (by
        intros v w v_adj_w; simp only [ne_eq]
        have neq := irreflexiveAltDef G.Adj G.loopless v w v_adj_w
        exact Fin.vne_of_ne neq
    )

end PerfectGraphs
