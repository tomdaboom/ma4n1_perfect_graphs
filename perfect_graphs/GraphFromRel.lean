-- FILEPATH: /Users/achung/Library/CloudStorage/OneDrive-UniversityofWarwick/year 4/lean/lectures/ma4n1_perfect_graphs/perfect_graphs/GraphFromRel.lean
-- BEGIN: abpxx6d04wxr


import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity




namespace Relations

def cycleG (n : ℕ) : SimpleGraph (ZMod n) :=
  SimpleGraph.fromRel (λ x y => x-y = 1)

#check cycleG 5

def CompleteG (n : ℕ) : SimpleGraph (ZMod n) :=
  SimpleGraph.fromRel (λ x y => x ≠ y)

def EmptyG(n : ℕ)  : SimpleGraph (ZMod n) :=
  SimpleGraph.fromRel (λ _ _  => false)


#check CompleteG 5

example : (CompleteG 5).Adj 0 2 := by
  unfold CompleteG SimpleGraph.fromRel --SimpleGraph.Adj
  simp only





def EmptyG.Coloring {n : ℕ}: (EmptyG n ).Coloring (ZMod 0) :=
  SimpleGraph.Coloring.mk
    (λ _ => 0)
    (by
      intros v w
      unfold SimpleGraph.Adj; unfold EmptyG;
      aesop
    )

def CompleteG.Coloring {n : ℕ}: (CompleteG n ).Coloring (ZMod n) :=
  SimpleGraph.Coloring.mk
    (λ v => v)
    (by
      intros v w
      unfold SimpleGraph.Adj; unfold CompleteG;
      aesop
    )

set_option trace.aesop true
def cylceG.Coloring {n : ℕ}: (cycleG n ).Coloring (ZMod 3) :=
  SimpleGraph.Coloring.mk
    (λ v => v % 3)
    (by
      intros v w
      unfold SimpleGraph.Adj; unfold cycleG;
      aesop

      -- | inl hq => sorry




      -- | inr hp => sorry





      /-
      n : ℕ
      v w : ZMod n
      ⊢ ¬v = w → v - w = 1 ∨ w - v = 1 → ¬↑v % 2 = ↑w % 2
      -/


    )
def oddHoleTestG  : SimpleGraph (ZMod 6) :=
  SimpleGraph.fromRel (λ x y =>
   if x.val<5 ∧ y.val<5 then
   x-y=1
   else if x.val=5 ∧ y.val=4 then True
   else if x.val=5 ∧ y.val=3 then True
   else False )

#eval hasNCycle cycle5 5


def cycle5  : SimpleGraph (ZMod 5) :=
  SimpleGraph.fromRel (λ x y => x-y = 1)



def hasNCycle {V : Type} (G : SimpleGraph V) (n : Nat) : Prop :=
  ∃ u, ∃ p : G.Walk u u, p.IsCycle ∧ p.length = n


-- theorem connections : cycle5.Adj 1 0 := by
--   unfold cycle5
--   aesop_graph


theorem cycle5hasc5 : hasNCycle cycle5 5  := by
  unfold hasNCycle
  -- unfold cycle5
  use  SimpleGraph.Walk.cons
