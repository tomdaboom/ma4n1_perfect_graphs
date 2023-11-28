-- FILEPATH: /Users/achung/Library/CloudStorage/OneDrive-UniversityofWarwick/year 4/lean/lectures/ma4n1_perfect_graphs/perfect_graphs/GraphFromRel.lean
-- BEGIN: abpxx6d04wxr
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.Basic


namespace Relations

def cylce5G (n : ℕ) : SimpleGraph (ZMod n) :=
  SimpleGraph.fromRel (λ x y => x-y = 1)

def CompleteG (n : ℕ) : SimpleGraph (ZMod n) :=
  SimpleGraph.fromRel (λ x y => x ≠ y)

def EmptyG(n : ℕ)  : SimpleGraph (ZMod n) :=
  SimpleGraph.fromRel (λ _ _  => false)


#check CompleteG 5

example : (CompleteG 5).Adj 0 2 := by
  unfold CompleteG SimpleGraph.fromRel --SimpleGraph.Adj
  simp only





def EmptyGraph.Coloring {n : ℕ}: (EmptyG n ).Coloring (ZMod 2) :=
  SimpleGraph.Coloring.mk

def evenCycle2Coloring {n : ℕ} (nIsEven : Even n) : (cycle n).Coloring (ZMod 2) :=
  SimpleGraph.Coloring.mk
    (λ v => v % 2)
    (by
      intros v w
      contrapose
      simp only [ne_eq, not_not]
      intros v_u_eq_mod_2
      unfold SimpleGraph.Adj; unfold cycle;
      simp only [SimpleGraph.fromRel_adj, ne_eq, not_and]
      intros v_neq_w
      sorry
    )

-- FILEPATH: /Users/achung/Library/CloudStorage/OneDrive-UniversityofWarwick/year 4/lean/lectures/ma4n1_perfect_graphs/perfect_graphs/GraphFromRel.lean
-- BEGIN: be15d9bcejpp
-- END: ed8c6549bwf9

#check (EmptyGraph' 5).adj
