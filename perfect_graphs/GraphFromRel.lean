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







def hasNCycle {V : Type} (G : SimpleGraph V) (n : Nat) : Prop :=
  ∃ u, ∃ p : G.Walk u u, p.IsCycle ∧ p.length = n


-- theorem connections : cycle5.Adj 1 0 := by
--   unfold cycle5
--   aesop_graph
def my_pair : Sym2 ℕ := Sym2.mk (0, 1)



lemma five_gt_one : Fact (1 < 5) := by
  refine fact_iff.mpr ?_
  refine Nat.succ_le_iff.mp ?_
  norm_num


def zmod5nontrivial : Nontrivial (ZMod 5):= by
  have h := five_gt_one
  exact ZMod.nontrivial 5


def zerotoone : cycle5.Adj 0 1 := by
  unfold cycle5
  have h := zmod5nontrivial

  rw [SimpleGraph.adj_iff_exists_edge]
  constructor
  {    exact zero_ne_one}  -- this implicitly uses h
  {
    use s(0, 1)
    norm_num

  }

def adjacencies (u v : ZMod 5)  (h: v-u=1  ): cycle5.Adj u v := by
  unfold cycle5
  have h' := zmod5nontrivial
  simp_all only [SimpleGraph.fromRel_adj, ne_eq, or_true, and_true]
  intro
  simp_all only [sub_self, zero_ne_one]




lemma oneminuszero : (1: ZMod 5)-0=1 := by norm_num
lemma  twominusone : (2: ZMod 5)-1=1  := by norm_num
lemma  threeminustwo : (3: ZMod 5)-2=1  := by norm_num
lemma  fourminusthree : (4: ZMod 5)-3=1  := by norm_num
lemma  zerominusfour : (0: ZMod 5)-4=1  := by
  simp_all only [zero_sub]
  apply Eq.refl

lemma uplusoneminusu (u : ZMod 5): u+1-u=1 := by
  simp_all only [add_sub_cancel']



def  cycle5Walk : SimpleGraph.Walk cycle5 0 0  :=
  (adjacencies 0 1  oneminuszero).toWalk.append
  ((adjacencies 1 2 twominusone).toWalk.append
  ((adjacencies 2 3 threeminustwo).toWalk.append
  ((adjacencies 3 4 fourminusthree).toWalk.append
  (adjacencies  4 0 zerominusfour).toWalk)))

lemma noteqinMod5 {u v : ZMod 5} (h : ¬(u - v).val ∣ 5) : u ≠ v := by
  sorry


theorem cycle5WalkisTrail : cycle5Walk.IsTrail := by
  unfold cycle5Walk
  aesop
  sorry

theorem cycle5WalkisnotNill : cycle5Walk ≠ SimpleGraph.Walk.nil := by
  unfold cycle5Walk
  simp_all only [SimpleGraph.Walk.cons_append, SimpleGraph.Walk.nil_append, ne_eq, not_false_eq_true]


lemma zeronotequalone (h': Nontrivial (ZMod 5)) (h: (0: ZMod 5) = 1) : False := by
  simp_all only [zero_ne_one]


lemma minuseqrewrite {n : ℕ} {v w : ZMod n} : (v - w = 1) → (v = 1 + w) := by
  intros vminuseq
  rw [← vminuseq]
  simp only [sub_add_cancel]

theorem cycle5Walktailnodup : cycle5Walk.support.tail.Nodup := by
  unfold cycle5Walk
  have h' := zmod5nontrivial
  simp only [SimpleGraph.Walk.cons_append, SimpleGraph.Walk.nil_append,
    SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons, List.nodup_cons,
    List.mem_cons, List.mem_singleton, one_ne_zero, or_false, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_self, and_true]

  aesop








  sorry




-- defined in simplegraph.walk.connectivity file but lean couldnt find it
universe u
variable {V : Type u}
variable (G : SimpleGraph V)
theorem isCycle_def {u : V} (p : G.Walk u u) :
    p.IsCycle ↔ p.IsTrail ∧ p ≠ SimpleGraph.Walk.nil ∧ p.support.tail.Nodup :=
  Iff.intro (fun h => ⟨h.1.1, h.1.2, h.2⟩) fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩


def cycle5WalkisCycle : cycle5Walk.IsCycle := by
  rw [isCycle_def]
  constructor
  apply cycle5WalkisTrail
  constructor
  apply cycle5WalkisnotNill
  apply cycle5Walktailnodup

  done


def cycle5WalkLength5 : cycle5Walk.length=5 := by
  apply Eq.refl (SimpleGraph.Walk.length cycle5Walk)



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


def adjacenciesTestG (u v : ZMod 5) (h: u-v=1) (h2: (u.val<5 ∧ v.val<5)): oddHoleTestG.Adj u v := by
  cases u; cases v;
  sorry


def TestGCycle5walk : oddHoleTestG.Walk 0 0  :=
  (adjacenciesTestG 0 1).toWalk.append
  ((adjacenciesTestG 1 2).toWalk.append
  ((adjacenciesTestG 2 3).toWalk.append
  ((adjacenciesTestG 3 4).toWalk.append
  (adjacenciesTestG  4 0).toWalk)))



def TestGCycle5walkisCycle : TestGCycle5walk.IsCycle := by
  unfold TestGCycle5walk
  sorry
  done



def TestGCycle5walkLength5 : TestGCycle5walk.length=5 := by
  sorry
  -- exact SimpleGraph.Walk.nil
  done


theorem TestGhasc5 : hasNCycle  oddHoleTestG 5 := by
  unfold hasNCycle
  use 0
  use TestGCycle5walk
  constructor
  {  apply TestGCycle5walkisCycle
  }
  { apply TestGCycle5walkLength5
  }
