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

#check (finiteEmpty 5).loopless

--def finiteChromaticNumber {V : Type} [Fintype V] (G : SimpleGraph V) : Set ℕ
--    :=  {n | SimpleGraph.Colorable G n ∧ n ≤ Fintype.card V}

def uniformColouring {V : Type} : SimpleGraph.Coloring (emptyGraph V) ℕ :=
    SimpleGraph.Coloring.mk (λ _ : V => 0) (by
        intros v w
        simp only [SimpleGraph.emptyGraph_eq_bot, SimpleGraph.bot_adj, ne_eq, IsEmpty.forall_iff]
    )

theorem emptyOneColourable {V : Type} : SimpleGraph.Colorable (emptyGraph V) 1 := by
    refine (SimpleGraph.colorable_iff_exists_bdd_nat_coloring 1).mpr ?_
    exists uniformColouring
    intros v
    exact Nat.lt_one_iff.mpr rfl

def trivialColouring {n : ℕ} (G : SimpleGraph (Fin n)) : SimpleGraph.Coloring G ℕ :=
    SimpleGraph.Coloring.mk (λ v : Fin n => (v : ℕ)) (by
        intros v w v_adj_w; simp only [ne_eq]
        convert G.loopless
        sorry
    )

end PerfectGraphs
