import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.SimpleGraph.Connectivity




namespace rels
open SimpleGraph
open Subgraph
def cycle (n : ℕ) : (SimpleGraph (ZMod n)) :=
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


-- def cycle5  : SimpleGraph (ZMod 5) :=
--   SimpleGraph.fromRel (λ x y => x-y = 1)







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


def zerotoone : (cycle 5).Adj 0 1 := by
  unfold cycle
  have h := zmod5nontrivial

  rw [SimpleGraph.adj_iff_exists_edge]
  constructor
  {    exact zero_ne_one}  -- this implicitly uses h
  {
    use s(0, 1)
    norm_num

  }

def adjacencies (u v : ZMod 5)  (h: v-u=1  ): (cycle 5).Adj u v := by
  unfold cycle
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



def  cycle5Walk : SimpleGraph.Walk (cycle 5) 0 0  :=
  (adjacencies 0 1  oneminuszero).toWalk.append
  ((adjacencies 1 2 twominusone).toWalk.append
  ((adjacencies 2 3 threeminustwo).toWalk.append
  ((adjacencies 3 4 fourminusthree).toWalk.append
  (adjacencies  4 0 zerominusfour).toWalk)))







theorem cycle5WalkisnotNill : cycle5Walk ≠ SimpleGraph.Walk.nil := by
  unfold cycle5Walk
  simp_all only [SimpleGraph.Walk.cons_append, SimpleGraph.Walk.nil_append, ne_eq, not_false_eq_true]

-- these can probably be combined into one
lemma zero_ne_one' (h': Nontrivial (ZMod 5)) (h: (0: ZMod 5) = 1) : False := by
  simp_all only [zero_ne_one]



lemma zero_ne_two : (0 : ZMod 5) = 2 -> False := by
  have h : 2<5 := by norm_num
  simp only [imp_false]
  contrapose! h
  apply Nat.le_of_dvd zero_lt_two
  symm at h
  exact (ZMod.nat_cast_zmod_eq_zero_iff_dvd 2 5).mp h

lemma zero_ne_three : (0 : ZMod 5) = 3 -> False := by
  have h : 3<5 := by norm_num
  simp only [imp_false]
  contrapose! h
  apply Nat.le_of_dvd zero_lt_three
  symm at h
  exact (ZMod.nat_cast_zmod_eq_zero_iff_dvd 3 5).mp h

lemma zero_ne_four : (0 : ZMod 5) = 4 -> False := by
  have h : 4<5 := by norm_num
  simp only [imp_false]
  contrapose! h
  apply Nat.le_of_dvd zero_lt_four
  symm at h
  exact (ZMod.nat_cast_zmod_eq_zero_iff_dvd 4 5).mp h



theorem cycle5Walktailnodup : cycle5Walk.support.tail.Nodup := by
  unfold cycle5Walk
  have h' := zmod5nontrivial
  simp only [SimpleGraph.Walk.cons_append, SimpleGraph.Walk.nil_append,
    SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons, List.nodup_cons,
    List.mem_cons, List.mem_singleton, one_ne_zero, or_false, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_self, and_true]
  aesop
  · rw [<- add_right_cancel_iff (a := -1)] at h
    norm_num at h
    exact zero_ne_one' h' h

  · rw [<- add_right_cancel_iff (a := -1)] at h
    norm_num at h
    exact zero_ne_two h
  · rw [<- add_right_cancel_iff (a := -1)] at h
    norm_num at h
    exact zero_ne_three h
  · rw [<- add_right_cancel_iff (a := -2)] at h
    norm_num at h
    exact zero_ne_one' h' h

  · rw [<- add_right_cancel_iff (a := -2)] at h
    norm_num at h
    exact zero_ne_two h
  · symm at h
    exact zero_ne_two h
  · rw [<- add_right_cancel_iff (a := -3)] at h
    norm_num at h
    exact zero_ne_one' h' h
  · symm at h
    exact zero_ne_three h
  · symm at a
    exact zero_ne_four a
  done


-- definitely a better way do this. Maybe using <;> ?
theorem cycle5WalkisTrail : cycle5Walk.IsTrail := by
  have h' := zmod5nontrivial
  unfold cycle5Walk
  aesop
  · exact zero_ne_three (id left.symm)
  · symm at h
    exact zero_ne_three h
  · rw [<- add_right_cancel_iff (a := -2)] at left
    norm_num at left
    exact zero_ne_two left
  · rw [<- add_right_cancel_iff (a := -2)] at h
    norm_num at h
    exact zero_ne_two h
  · symm at right
    exact zero_ne_three right
  · symm at left
    exact zero_ne_two left
  · rw [<- add_right_cancel_iff (a := -1)] at left
    norm_num at left
    exact zero_ne_two left
  · rw [<- add_right_cancel_iff (a := -1)] at h
    norm_num at h
    exact zero_ne_two h
  · rw [<- add_right_cancel_iff (a := -1)] at left
    norm_num at left
    exact zero_ne_two left
  · rw [<- add_right_cancel_iff (a := -1)] at left
    norm_num at left
    exact zero_ne_three left
  · symm at right
    exact zero_ne_two right
  · exact zero_ne_two h
  · exact zero_ne_two left
  · exact zero_ne_three left
  · exact zero_ne_three left
  · exact zero_ne_four left
  · rw [<- add_right_cancel_iff (a := -1)] at h
    norm_num at h
    exact zero_ne_three h
  done



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



theorem cycle5hasc5 : hasNCycle (cycle 5) 5  := by
  unfold hasNCycle
  use 0
  use cycle5Walk
  constructor
  {  apply cycle5WalkisCycle
  }
  { apply cycle5WalkLength5
  }

def hasOddHole {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ n : ℕ, hasNCycle G (2*n+5) --odd cycle of length ≥ 5, using that 0 ∈ ℕ in Lean


theorem cycle5hasOddHole : hasOddHole (cycle 5) := by
  unfold hasOddHole
  use 0
  exact cycle5hasc5


-- repeat definitions
def isInducedSimpleGraph {V : Type} (H : SimpleGraph V) (H' : SimpleGraph V) : Prop :=
  ∀ {v w : V}, (H.Adj v w → H'.Adj v w) ∨ (H'.neighborSet v = ∅) ∨ (H'.neighborSet w = ∅)

def coe {V : Type}{G : SimpleGraph V}(H : Subgraph G) : SimpleGraph H.verts where
  Adj v w := H.Adj v w
  symm _ _ h := H.symm h
  loopless v h := loopless G v (H.adj_sub h)
def isInducedSubgraph {V : Type} (H : SimpleGraph V) (H' : Subgraph H) : Prop :=
  ∀ {v w : V}, v ∈ H'.verts → w ∈ H'.verts → H.Adj v w → H'.Adj v

def hasNClique {V : Type} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ t, G.IsNClique n t
noncomputable def CliqueNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sSup { n : ℕ | hasNClique G n }

def isPerfect {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ H : Subgraph G, isInducedSubgraph G H → (coe H).chromaticNumber = CliqueNumber (coe H)


theorem strongPerfectGraphTheorem {V : Type} (G : SimpleGraph V) : isPerfect G ↔ ¬ hasOddHole G ∧ ¬ hasOddHole Gᶜ := by
  sorry


theorem cycle5notPerfect : ¬ isPerfect (cycle 5) := by
  rw [strongPerfectGraphTheorem]
  simp only [not_and_or]
  rw [not_not]
  refine Or.inl ?h
  exact cycle5hasOddHole


@[aesop]
lemma zero_ne_one_ {n : ℕ} (h': Nontrivial (ZMod n)): (0: ZMod n) = 1 -> False := by
  simp_all only [zero_ne_one]



@[aesop]
lemma zero_ne_two_ {n : ℕ} (h : 2 < n): (0 : ZMod n) = 2 -> False := by
  simp only [imp_false]
  contrapose! h
  apply Nat.le_of_dvd zero_lt_two
  symm at h
  exact (ZMod.nat_cast_zmod_eq_zero_iff_dvd 2 n).mp h

lemma zero_ne_three_ {n : ℕ} (h : 3 < n): (0 : ZMod n) = 3 -> False := by
  simp only [imp_false]
  contrapose! h
  apply Nat.le_of_dvd zero_lt_three
  symm at h
  exact (ZMod.nat_cast_zmod_eq_zero_iff_dvd 3 n).mp h

lemma zero_ne_four_ {n : ℕ} (h : 4 < n): (0 : ZMod n) = 4 -> False := by
  simp only [imp_false]
  contrapose! h
  apply Nat.le_of_dvd zero_lt_four
  symm at h
  exact (ZMod.nat_cast_zmod_eq_zero_iff_dvd 4 n).mp h

lemma zero_ne_five_ {n : ℕ} (h : 5 < n): (0 : ZMod n) = 5 -> False := by
  simp only [imp_false]
  contrapose! h
  have zero_lt_five : 0<5 := by simp_all only [Nat.zero_lt_succ]
  apply Nat.le_of_dvd zero_lt_five
  symm at h
  exact (ZMod.nat_cast_zmod_eq_zero_iff_dvd 5 n).mp h

lemma zero_ne_six_ {n : ℕ} (h : 6 < n): (0 : ZMod n) = 6 -> False := by
  simp only [imp_false]
  contrapose! h
  have zero_lt_six : 0<6 := by simp_all only [Nat.zero_lt_succ]
  apply Nat.le_of_dvd zero_lt_six
  symm at h
  exact (ZMod.nat_cast_zmod_eq_zero_iff_dvd 6 n).mp h

-- graph with induced c7
-- definition could have been more compact but it changes the proof so did not change
def funkyGraph  : SimpleGraph (ZMod 12) :=
  SimpleGraph.fromRel (λ x y =>
   ((x.val<7 ∧ y.val<7) ∧ x-y=1) ∨
  (x=0 ∧ y = 6) -- edge to finish of cycle
  ∨ (x=0 ∧ y=9)
  ∨ (x=2 ∧ y=11)
  ∨ (x=4 ∧ y=9)
  ∨ (x=10 ∧ y=9)
  ∨ (x=2 ∧ y=9))


lemma twelve_gt_one : Fact (1 < 12) := by
  refine fact_iff.mpr ?_
  refine Nat.succ_le_iff.mp ?_
  norm_num


lemma  zmod12nontrivial : Nontrivial (ZMod 12):= by
  have h := twelve_gt_one
  exact ZMod.nontrivial 12

lemma  adjacenciesforc7infunckygraph (u v : ZMod 12) (h: v-u=1∧ u.val <7∧ v.val<7 ): funkyGraph.Adj u v := by
  unfold funkyGraph
  have h' := zmod12nontrivial
  simp_all only [fromRel_adj, ne_eq, and_self, true_and, true_or, or_true, and_true]
  intro a
  simp_all only [sub_self, zero_ne_one]


lemma uplusoneminusuandlessthan7 {n : ℕ }(u : ZMod n): (u+1)-u=1 := by
  simp_all only [add_sub_cancel']

lemma oneminuszeroandlessthan7 : (1: ZMod 12)-0=1 ∧ (0 : ZMod 12).val<7 ∧ (1 : ZMod 12).val <7 := by
  unfold ZMod.val
  simp_all only [sub_zero, Fin.val_zero, Nat.zero_lt_succ, Fin.val_one, Nat.one_lt_succ_succ, and_self]

lemma  twominusoneandlessthan7 : (2: ZMod 12)-1=1 ∧ (1 : ZMod 12).val<7 ∧ (2 : ZMod 12).val <7   := by
  unfold ZMod.val
  norm_num

lemma  threeminustwoandlessthan7 : (3: ZMod 12)-2=1 ∧ (2 : ZMod 12).val<7 ∧ (3 : ZMod 12).val <7 := by
  unfold ZMod.val
  norm_num
  exact Nat.compare_eq_lt.mp rfl

lemma  fourminusthreeandlessthan7 : (4: ZMod 12)-3=1 ∧ (3 : ZMod 12).val<7 ∧ (4 : ZMod 12).val <7 := by
  unfold ZMod.val
  norm_num
  constructor
  <;>  exact Nat.compare_eq_lt.mp rfl

lemma  fiveminusfourandlessthan7 : (5: ZMod 12)-4=1 ∧ (4 : ZMod 12).val<7 ∧ (5 : ZMod 12).val <7 := by
  unfold ZMod.val
  norm_num
  constructor
  <;>  exact Nat.compare_eq_lt.mp rfl

lemma  sixminusfiveandlessthan7 : (6: ZMod 12)-5=1 ∧ (5 : ZMod 12).val<7 ∧ (6 : ZMod 12).val <7 := by
  unfold ZMod.val
  norm_num
  constructor
  <;>  exact Nat.compare_eq_lt.mp rfl



lemma sixconnectedtozero : funkyGraph.Adj 6 0 := by
  unfold funkyGraph
  have sixlessthan12: 6<12 := by exact Nat.compare_eq_lt.mp rfl
  simp_all only [fromRel_adj, ne_eq, and_self, true_and, true_or, or_true, and_true]
  rw [← @ne_eq]
  symm
  apply (zero_ne_six_  sixlessthan12)






  -- aesop_graph
  -- · symm at a
  --   apply  (zero_ne_six_  sixlessthan12) at a
  --   exact a
  -- ·
  -- ·




def funkyGraphc7Walk : funkyGraph.Walk 0 0  :=
  (adjacenciesforc7infunckygraph 0 1 oneminuszeroandlessthan7).toWalk.append
  ((adjacenciesforc7infunckygraph 1 2 twominusoneandlessthan7).toWalk.append
  ((adjacenciesforc7infunckygraph 2 3 threeminustwoandlessthan7).toWalk.append
  ((adjacenciesforc7infunckygraph 3 4 fourminusthreeandlessthan7).toWalk.append
  ((adjacenciesforc7infunckygraph 4 5 fiveminusfourandlessthan7).toWalk.append
  ((adjacenciesforc7infunckygraph 5 6 sixminusfiveandlessthan7).toWalk.append
  (sixconnectedtozero.toWalk))))))


lemma funkyGraphWalkisTrail : funkyGraphc7Walk.IsTrail := by
  have h' := zmod12nontrivial
  unfold funkyGraphc7Walk
  aesop
  simp_all only []

lemma funkyGraphWalkisnotNill

lemma funkyGraphWalktailnodup

lemma  funkyGraphWalkIsCycle : funkyGraphc7Walk.IsCycle := by
  rw [isCycle_def]
  constructor
  apply funkyGraphWalkisTrail
  constructor
  apply funkyGraphWalkisnotNill
  apply funkyGraphWalktailnodup

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
