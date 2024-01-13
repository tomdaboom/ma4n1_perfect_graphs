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

def CompleteGonNat(n: ℕ )  : SimpleGraph (ℕ ) :=
  SimpleGraph.fromRel (λ x y => (x ≠ y ∧ x < n ∧ y < n))


def CycleG (n : ℕ) : SimpleGraph (ZMod n) :=
  SimpleGraph.fromRel (λ x y => x-y = 1)


-- def CompleteG.Coloring {n : ℕ}: (CompleteG n ).Coloring (ZMod n) :=
--   SimpleGraph.Coloring.mk
--     (λ v => v)
--     (by
--       intros v w
--       unfold SimpleGraph.Adj; unfold CompleteG;
--       aesop

--     )

def CycleG5 : SimpleGraph (ZMod 5) := CycleG 5

def CompleteG5 : SimpleGraph (ZMod 5) := CompleteG 5

def CompleteG3onNat : SimpleGraph ℕ  := CompleteGonNat 3
def CompleteG5onNat : SimpleGraph ℕ  := CompleteGonNat 5

-- theorem CycleG5inCompleteG5 : CycleG5 ≤ CompleteG5 := by
--   unfold CycleG5; unfold CompleteG5;
--   unfold CycleG; unfold CompleteG;
--   aesop_graph
--   done

-- #check CompleteG5.toSubgraph CycleG5 CycleG5inCompleteG5

-- def F  := CompleteG5.toSubgraph CycleG5 CycleG5inCompleteG5

-- #check F


theorem CycleGNCompleteGN (n : ℕ) : CycleG n ≤ CompleteG n := by

  unfold CycleG; unfold CompleteG;
  aesop_graph
  done
-- toSubgraph works like this : ( The big graph).toSubgraph (The small graph) (The proof that the small graph is a subgraph of the big graph)
def CycleNAsSubgraphofCompleteN (n : ℕ) : SimpleGraph.Subgraph (CompleteG n) :=
  (CompleteG n ).toSubgraph (CycleG n) (CycleGNCompleteGN n)

#check CycleNAsSubgraphofCompleteN 5


theorem CompleteG3inCompleteG5 : CompleteG3onNat ≤ CompleteG5onNat := by
  unfold CompleteG3onNat CompleteG5onNat CompleteGonNat
  rintro x y ⟨xy, ⟨-, x3, y3⟩ | ⟨-, y3, x3⟩⟩
  all_goals
    have x5 : x < 5 := by linarith
    have y5 : y < 5 := by linarith
    aesop
  done


example : CompleteG 3 ↪g CompleteG5 where
  toFun x := x
  inj' _ _ := by apply ZMod.cast_injective_of_lt (by norm_num)
  map_rel_iff' {a b} := by
    dsimp only [Function.Embedding.coeFn_mk]
    unfold CompleteG5 CompleteG
    constructor <;> intro h
    · aesop
    · contrapose! h
      simp_all only [ne_eq, SimpleGraph.fromRel_adj, not_and, not_false_eq_true, true_or,
      not_true_eq_false, imp_false, not_not]
      exact ZMod.cast_injective_of_lt (by norm_num) h

    done

#check CompleteG3Embed

theorem G3isSubgraphofG5 : CompleteG3Embed ≤ CompleteG5 := by
  unfold CompleteG3onNat CompleteG5onNat CompleteGonNat
  rintro x y ⟨xy, ⟨-, x3, y3⟩ | ⟨-, y3, x3⟩⟩
  all_goals
    have x5 : x < 5 := by linarith
    have y5 : y < 5 := by linarith
    aesop
  done


