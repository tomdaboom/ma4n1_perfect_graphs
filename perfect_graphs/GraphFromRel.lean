import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sym.Sym2
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


#eval hasNCycle cycle5 5


def cycle5  : SimpleGraph (ZMod 5) :=
  SimpleGraph.fromRel (λ x y => x-y = 1)

def adjacencies (u v : ZMod 5) : cycle5.Adj u v := by
  cases u; cases v;







def hasNCycle {V : Type} (G : SimpleGraph V) (n : Nat) : Prop :=
  ∃ u, ∃ p : G.Walk u u, p.IsCycle ∧ p.length = n


-- theorem connections : cycle5.Adj 1 0 := by
--   unfold cycle5
--   aesop_graph
def my_pair : Sym2 ℕ := Sym2.mk (0, 1)



lemma five_gt_one (n : ℕ) (h : Fact (4 ≤ n)) : Fact (1 < n) := by
  have h' := Fact.elim h
  refine fact_iff.mpr ?_
  refine Nat.succ_le_iff.mp ?_
  norm_num
  linarith

def zerotoone : cycle5.Adj 0 1 := by
  unfold cycle5
  rw [SimpleGraph.adj_iff_exists_edge]
  constructor
  {sorry }
  {
    use ⟦(0, 1)⟧
    norm_num
    have h' : Nontrivial (ZMod 5) := by  exact ZMod.nontrivial 5;


  }





def cycle5Walk : cycle5.Walk 0 0   :=
  (adjacencies 0 1).toWalk.append
  ((adjacencies 1 2).toWalk.append
  ((adjacencies 2 3).toWalk.append
  ((adjacencies 3 4).toWalk.append
  (adjacencies  4 0).toWalk)))

  -- exact SimpleGraph.Walk.nil
  done

#check cycle5Walk

def cycle5WalkisCycle : cycle5Walk.IsCycle := by
  unfold cycle5Walk
  sorry
  done



def cycle5WalkLength5 : cycle5Walk.length=5 := by
  sorry


theorem cycle5hasc5 : hasNCycle cycle5 5  := by
  unfold hasNCycle
  use 0
  use cycle5Walk
  constructor
  {  apply cycle5WalkisCycle
  }
  { apply cycle5WalkLength5
  }




def oddHoleTestG  : SimpleGraph (ZMod 6) :=
  SimpleGraph.fromRel (λ x y =>
   if x.val<5 ∧ y.val<5 then
   x-y=1
   else if x.val=5 ∧ y.val=0 then True
   else False )

def adjacenciesTestG (u v : ZMod 5) : cycle5.Adj u v := by
  cases u; cases v;
  sorry


def TestGCycle5walk : oddHoleTestG.Walk 0 0   :=
  (adjacenciesTestG 0 1).toWalk.append
  ((adjacenciesTestG 1 2).toWalk.append
  ((adjacenciesTestG 2 3).toWalk.append
  ((adjacenciesTestG 3 4).toWalk.append
  (adjacenciesTestG  4 0).toWalk)))


def TestGCycle5walkisCycle : cycle5Walk.IsCycle := by
  unfold cycle5Walk
  sorry
  done



def TestGCycle5walkLength5 : cycle5Walk.length=5 := by
  sorry
  -- exact SimpleGraph.Walk.nil
  done
theorem TestGhasc5 : hasNCycle  oddHoleTestG 5 := by
    unfold hasNCycle
  use 0
  use cycle5Walk
  constructor
  {  apply TestGCycle5walkisCycle
  }
  { apply TestGCycle5walkLength5
  }
