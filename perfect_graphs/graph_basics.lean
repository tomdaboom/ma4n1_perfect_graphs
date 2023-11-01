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

def uniformColouring {V : Type} : SimpleGraph.Coloring (emptyGraph V) ℕ :=
    SimpleGraph.Coloring.mk (λ v : V => 0) (sorry)

theorem emptyOneColourable {V : Type} : SimpleGraph.Colorable (emptyGraph V) 1 := by
    refine (SimpleGraph.colorable_iff_exists_bdd_nat_coloring 1).mpr ?_
    exists uniformColouring
    intros v
    exact Nat.lt_one_iff.mpr rfl

end PerfectGraphs
