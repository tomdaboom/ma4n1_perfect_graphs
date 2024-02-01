import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
--import Mathlib.Combinatorics.SimpleGraph.Basic
--import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.Basic



-- theorem CompleteBipartiteGraph.chromaticNumber {V W : Type*} [Nonempty V] [Nonempty W] :
--     (completeBipartiteGraph V W).chromaticNumber = 2 := by
--   apply chromaticNumber_eq_card_of_forall_surj (CompleteBipartiteGraph.bicoloring V W)
--   intro C b
--   have v := Classical.arbitrary V
--   have w := Classical.arbitrary W
--   have h : (completeBipartiteGraph V W).Adj (Sum.inl v) (Sum.inr w) := by simp
--   have hn := C.valid h
--   by_cases he : C (Sum.inl v) = b
--   · exact ⟨_, he⟩
--   · by_cases he' : C (Sum.inr w) = b
--     · exact ⟨_, he'⟩
--     · exfalso
--       cases b <;>
--         simp only [Bool.eq_true_eq_not_eq_false, Bool.eq_false_eq_not_eq_true] at he he' <;>
--           rw [he, he'] at hn <;>
--         contradiction




-- def completeBipartiteGraph (V W : Type*) : SimpleGraph (Sum V W) where
--   Adj v w := v ∧ w.isRight ∨ v.isRight ∧ w.isLeft
--   symm v w := by cases v <;> cases w <;> simp
--   loopless v := by cases v <;> simp


def completeTripartiteGraph (V W X : Type*) : SimpleGraph (Sum (Sum V W) X) where
  Adj v w := v.isLeft.isLeft
  symm v w := by 
    cases v; cases w;


 
  loopless v := by cases v <;> simp





-- def completeNmultipartiteGraph (V W :Type*) : SimpleGraph (Sum V W) where
--   Adj v w := v ≠ w
--   symm v w := by simp
--   loopless v := by simp

-- theorem CompleteNmultipartiteGraph.chromaticNumber {V W : Type*} [Nonempty V] [Nonempty W] :
--     (CompleteNmultipartiteGraph V W).chromaticNumber = N := by
