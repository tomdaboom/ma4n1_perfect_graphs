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

lemma twelve_gt_one : Fact (1 < 12) := by
  refine fact_iff.mpr ?_
  refine Nat.succ_le_iff.mp ?_
  norm_num


lemma  zmod12nontrivial : Nontrivial (ZMod 12):= by
  have h := twelve_gt_one
  exact ZMod.nontrivial 12

@[simp]
lemma zero_ne_a_ {n : ℕ} (a: ZMod n)(h : a.val < n ∧ 0<a.val): 0 = a -> False := by
  simp only [imp_false]
  contrapose! h
  intro _
  aesop_subst h
  simp_all only [ZMod.val_zero, le_refl]


-- proof provided by damiano
@[simp]
lemma uminusvandlessthan7 {u v : ℕ}(h: u<7∧ v<7 ∧ u-v=1): (u: ZMod 12)-v=1 ∧ (v : ZMod 12).val<7 ∧ (u : ZMod 12).val <7 := by
  rcases h with ⟨h1, h2, h3⟩
  interval_cases u <;> interval_cases v <;> simp_all <;> norm_cast


-- similar case bash to above
@[simp]
lemma lessthan12greaterthanzero {n : ℕ} (h : n > 0 ∧ n < 12) : (n : ZMod 12).val < 12 ∧ 0 < (n : ZMod 12).val  := by
  rcases h with ⟨h1, h2⟩
  interval_cases n <;> simp_all <;> norm_cast

-- @[simp]
-- lemma zero_ne_one_mod12 : (0: ZMod 12) = 1 -> False := by apply zero_ne_a_ 1 (by exact lessthan12greaterthanzero (by trivial))
-- @[simp]
-- lemma zero_ne_two_mod12 : (0: ZMod 12) = 2 -> False := by apply zero_ne_a_ 2 (by exact lessthan12greaterthanzero (by trivial))
-- @[simp]
-- lemma zero_ne_three_mod12 : (0: ZMod 12) = 3 -> False := by apply zero_ne_a_ 3 (by exact lessthan12greaterthanzero (by trivial))
-- @[simp]
-- lemma zero_ne_four_mod12 : (0: ZMod 12) = 4 -> False := by apply zero_ne_a_ 4 (by exact lessthan12greaterthanzero (by trivial))
-- @[simp]
-- lemma zero_ne_five_mod12 : (0: ZMod 12) = 5 -> False := by apply zero_ne_a_ 5 (by exact lessthan12greaterthanzero (by trivial))
-- @[simp]
-- lemma zero_ne_six_mod12 : (0: ZMod 12) = 6 -> False := by apply zero_ne_a_ 6 (by exact lessthan12greaterthanzero (by trivial))


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




lemma  adjacenciesforc7infunckygraph (u v : ZMod 12) (h: v-u=1∧ u.val <7∧ v.val<7 ): funkyGraph.Adj u v := by
  unfold funkyGraph
  have h' := zmod12nontrivial
  simp_all only [fromRel_adj, ne_eq, and_self, true_and, true_or, or_true, and_true]
  intro a
  simp_all only [sub_self, zero_ne_one]





lemma sixconnectedtozero : funkyGraph.Adj 6 0 := by
  unfold funkyGraph
  simp_all only [fromRel_adj, ne_eq, and_self, true_and, true_or, or_true, and_true]
  rw [← @ne_eq]
  symm
  apply (zero_ne_a_  6 (by exact lessthan12greaterthanzero (by trivial)))



def funkyGraphc7Walk : funkyGraph.Walk 0 0  :=
  (adjacenciesforc7infunckygraph 0 1 (uminusvandlessthan7 (by trivial))).toWalk.append
  ((adjacenciesforc7infunckygraph 1 2 (uminusvandlessthan7 (by trivial))).toWalk.append
  ((adjacenciesforc7infunckygraph 2 3 (uminusvandlessthan7 (by trivial))).toWalk.append
  ((adjacenciesforc7infunckygraph 3 4 (uminusvandlessthan7 (by trivial))).toWalk.append
  ((adjacenciesforc7infunckygraph 4 5 (uminusvandlessthan7 (by trivial))).toWalk.append
  ((adjacenciesforc7infunckygraph 5 6 (uminusvandlessthan7 (by trivial))).toWalk.append
  (sixconnectedtozero.toWalk))))))


lemma funkyGraphWalkisTrail : funkyGraphc7Walk.IsTrail := by
  have h' := zmod12nontrivial

  unfold funkyGraphc7Walk
  simp only [Walk.cons_append, Walk.nil_append, Walk.cons_isTrail_iff, Walk.IsTrail.nil,
    Walk.edges_nil, List.not_mem_nil, not_false_eq_true, and_self, Walk.edges_cons,
    List.mem_singleton, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, and_true,
    true_and, List.mem_cons, one_ne_zero, false_and, or_false, zero_ne_one, false_or, and_false,zero_ne_six_mod12,zero_ne_five_mod12,
    zero_ne_four_mod12,zero_ne_three_mod12,zero_ne_two_mod12,zero_ne_one_mod12]
  norm_cast



lemma funkyGraphWalktailnodup  : funkyGraphc7Walk.support.tail.Nodup := by
  unfold funkyGraphc7Walk
  simp only [Walk.cons_append, Walk.nil_append, Walk.support_cons, Walk.support_nil, List.tail_cons,
    List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_self, and_true]
  norm_cast



lemma funkyGraphWalkisnotNil : funkyGraphc7Walk ≠ SimpleGraph.Walk.nil := by
  unfold funkyGraphc7Walk
  simp_all only [SimpleGraph.Walk.cons_append, SimpleGraph.Walk.nil_append, ne_eq, not_false_eq_true]

-- lemma funkyGraphWalktailnodup

lemma  funkyGraphWalkIsCycle : funkyGraphc7Walk.IsCycle := by
  rw [isCycle_def]
  constructor
  apply funkyGraphWalkisTrail
  constructor
  apply funkyGraphWalkisnotNil
  apply funkyGraphWalktailnodup

  done


lemma funkyGraphWalkLength7 : funkyGraphc7Walk.length=7 := by
  apply Eq.refl (SimpleGraph.Walk.length funkyGraphc7Walk)




theorem funkyGraphhasc7 : hasNCycle funkyGraph 7  := by
  unfold hasNCycle
  use 0
  use funkyGraphc7Walk
  constructor
  {  apply funkyGraphWalkIsCycle
  }
  { apply funkyGraphWalkLength7
  }

theorem funkyGraphhasOddhole : hasOddHole funkyGraph := by
  unfold hasOddHole
  use 1
  exact funkyGraphhasc7


theorem funkyGraphnotPerfect : ¬ isPerfect funkyGraph := by
  rw [strongPerfectGraphTheorem]
  simp only [not_and_or]
  rw [not_not]
  refine Or.inl ?h
  exact funkyGraphhasOddhole




