import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
--import Mathlib.Combinatorics.SimpleGraph.Basic
--import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
--import Mathlib.Combinatorics.SimpleGraph.chromaticNumber
import Mathlib.Data.Fintype.Basic



-- inductive color : Type
-- | red : color
-- | blue : color
-- | green : color

-- open color



namespace PerfectGraphs

#check SimpleGraph (Fin 5)





-- lemma Symm : Symmetric AdjExample := by
-- dsmip at *




def exampleGraph : SimpleGraph (Fin 5) where
  Adj x y  :=
    --  notice that I removed the `if .. then .. else ..` since it was not necessary
    x = 0 ∧ y = 1 ∨ x = 1 ∧ y = 0 ∨ x = 2 ∧ y = 3 ∨ x = 3 ∧ y = 2
  symm a b h := by
    --  `aesop` is a "search" tactic: among other things, it splits all cases and tries
    --  various finishing tactics.
    aesop
  loopless a b := by
    aesop

def exampleColoringFunction (v : Fin 5) : Prop :=
  v=0 ∨  v=2


lemma valid_coloring : ∀ {v w : Fin 5}, exampleGraph.Adj v w → exampleColoringFunction v ≠ exampleColoringFunction w :=
  by
   sorry





def exampleGraph.Coloring : (exampleGraph).Coloring bool :=
  SimpleGraph.Coloring.mk exampleColoringFunction (valid_coloring)
