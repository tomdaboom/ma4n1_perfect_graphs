import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Finset.Pairwise
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Subgraph


namespace subgraphs

def CompleteG (n : ℕ) : SimpleGraph (ZMod n) :=
  SimpleGraph.fromRel (λ x y => x ≠ y)


def cycleG (n : ℕ) : SimpleGraph (ZMod n) :=
  SimpleGraph.fromRel (λ x y => x-y = 1)


def CompleteG.Coloring {n : ℕ}: (CompleteG n ).Coloring (ZMod n) :=
  SimpleGraph.Coloring.mk
    (λ v => v)
    (by
      intros v w
      unfold SimpleGraph.Adj; unfold CompleteG;
      aesop

    )



def CycleG5 : SimpleGraph (ZMod 5) := cycleG 5

def CompleteG5 : SimpleGraph (ZMod 5) := CompleteG 5

theorem CycleG5inCompleteG5 : CycleG5 ≤ CompleteG5 := by
  unfold CycleG5; unfold CompleteG5;
  unfold cycleG; unfold CompleteG;
  aesop_graph
  done

#check CompleteG5.toSubgraph CycleG5 CycleG5inCompleteG5

def F  := CompleteG5.toSubgraph CycleG5 CycleG5inCompleteG5

#check F
