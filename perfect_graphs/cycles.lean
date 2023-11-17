import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.Basic

--import perfect_graphs.ColouringDefs

--open perfect_graphs.ColouringDefs

namespace Cycles

def path (n : ℕ) : (SimpleGraph (Fin n)) :=
  SimpleGraph.fromRel (λ x y => (x-y : ℕ) = 1)

def cycle (n : ℕ) : (SimpleGraph (Fin n)) :=
  SimpleGraph.fromRel (λ x y => ((x-y : ℕ) = 1 ) ∨ ((x:ℕ)=0 ∧ y=n-1))

example : (cycle 5).Adj 0 4 := by
  unfold cycle SimpleGraph.fromRel --SimpleGraph.Adj
  simp only

--theorem evenCyclesChiIsTwo {n : ℕ} : (cycle (2*n)).chromaticNumber = 2 := by
--  apply chromaticNumberAltDef
