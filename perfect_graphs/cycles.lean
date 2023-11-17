import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
-- import Mathlib.Data.finset
-- import Mathlib.Data.finset_union
import Mathlib.Data.Fintype.Basic



def cycle (n : ℕ) : (SimpleGraph (Fin n)) :=
  SimpleGraph.fromRel (λ x y => (x-y : ℕ) = 1)

example : (cycle 5).Adj 1 2 := by
  unfold cycle SimpleGraph.fromRel --SimpleGraph.Adj
  simp only

theorem firstAdjLast {n : ℕ} (i : Fin n) : (cycle n).Adj i (i + 1) := by sorry
