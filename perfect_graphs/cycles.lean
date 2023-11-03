import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
-- import Mathlib.Data.finset
-- import Mathlib.Data.finset_union



namespace TPwL


#check SimpleGraph

#check Finset

#check SimpleGraph.chromaticNumber

#check SimpleGraph.adj_injective

#check SimpleGraph





def V : Type := Fin 2  -- A type with 4 elements, representing vertices



def my_graph : SimpleGraph V where

 Adj _ _ := false
  symm := 
  loopless := by sorry
done
