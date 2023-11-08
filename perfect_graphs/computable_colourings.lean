import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.Basic

namespace ComputableColorings

def FiniteGraph (n : ℕ) : Type := SimpleGraph (Fin n)


def validColoring {colors : Type}
  (G : FiniteGraph vs)
  (coloring : Fin vs → colors)
  [∀ u v : Fin vs, Decidable (G.Adj v u)]
  [Decidable (∀ u v : Fin vs, coloring v = coloring u)]
  : Bool
  := Id.run do
    let mut result := true

    for (v : Fin vs) in [0:vs-1] do
--      for (u : Fin vs) in [0:vs-1] do
        if (G.Adj v v) then
          --if (coloring v = coloring u) then
          result := false

    pure result


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

def exampleColoringFunction (v : Fin 5) : Bool := v=0 ∨ v=2

def validColoringSpecific : Bool := Id.run do
    let mut result := true

    for (v : Fin 5) in [0:4] do
      for (u : Fin 5) in [0:4] do
        if (exampleGraph.Adj v u) then
          if (exampleColoringFunction v = exampleColoringFunction u) then
            result := false

    pure result

#eval validColoring exampleGraph exampleColoringFunction

/-
def nColorable
  (G : FiniteGraph vs)
  (i : Fin vs)
  : Bool := Id.run do
-/


end ComputableColorings
