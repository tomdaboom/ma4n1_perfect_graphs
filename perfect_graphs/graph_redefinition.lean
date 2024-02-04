import Mathlib.Tactic
import Mathlib.Data.Setoid.Partition

-- A graph is a pair (V, E)
-- where V is a set of vertices of type α
-- and E is a set of edges between elements of type α
structure Graph (α : Type u) [DecidableEq α] where
  VertexSet : Set α
  EdgeSet   : Set (α × α)
  EdgeSetConstriction : ∀ e ∈ EdgeSet, e.fst ∈ VertexSet ∧ e.snd ∈ VertexSet

def makeGraph {α : Type u} [DecidableEq α] (vertices : Set α) (edges : Set (α × α)) : Graph α :=
  {
    VertexSet := vertices,
    EdgeSet := (vertices ×ˢ vertices) ∩ edges,
    EdgeSetConstriction := by
      simp only [Set.mem_inter_iff, Set.mem_prod, and_imp, Prod.forall]
      intros a b a_vert b_vert _
      exact { left := a_vert, right := b_vert }
  }

-- The completely empty graph
def completelyEmptyGraph {α : Type u} [DecidableEq α] : Graph α := makeGraph ∅ ∅

-- The graph with no edges on a set of vertices
def emptyGraph {α : Type u} [DecidableEq α] (vertices : Finset α) : Graph α := makeGraph vertices ∅

-- The complete graph on 3 vertices
-- aka a triangle
def k3 := makeGraph {0, 1, 2} {(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)}

-- u is adjacent to v iff (u, v) is an edge in our graph
def adjacent {α : Type u} [DecidableEq α] (G : Graph α) (u v : α) : Prop
  := (u, v) ∈ G.EdgeSet

-- A graph is complete if every vertex is connected to every other vertex
def complete {α : Type u} [DecidableEq α] (G : Graph α) : Prop
  := ∀ u ∈ G.VertexSet, ∀ v ∈ G.VertexSet, u ≠ v → adjacent G u v


#check k3
#check adjacent k3 1 2

-- 1 and 2 are adjacent in k3
example : adjacent k3 1 2 := by
  unfold k3 adjacent makeGraph
  simp only [Set.mem_singleton_iff, OfNat.one_ne_ofNat, Set.mem_insert_iff, zero_ne_one, or_self,
    Prod.mk.injEq, and_false, OfNat.ofNat_ne_zero, and_self, OfNat.ofNat_ne_one,
    OfNat.zero_ne_ofNat, and_true, one_ne_zero, Set.mem_inter_iff, Set.mem_prod, or_false, or_true]

-- k3 is complete
example : complete k3 := by
  unfold complete k3 makeGraph adjacent
  simp only [Set.mem_singleton_iff, OfNat.one_ne_ofNat, Set.mem_insert_iff, zero_ne_one, or_self,
    ne_eq, Prod.mk.injEq, and_false, OfNat.ofNat_ne_zero, and_self, OfNat.ofNat_ne_one,
    OfNat.zero_ne_ofNat, and_true, one_ne_zero, Set.mem_inter_iff, Set.mem_prod, forall_eq_or_imp,
    or_false, false_or, or_true, forall_eq, not_true_eq_false, IsEmpty.forall_iff,
    not_false_eq_true, forall_true_left]


-- H is a subgraph of G iff V(H) ⊆ V(G) and E(H) ⊆ E(G)
def subgraph {α : Type u} [DecidableEq α] (H : Graph α) (G : Graph α) :=
  H.VertexSet ⊆ G.VertexSet ∧ H.EdgeSet ⊆ G.EdgeSet

-- Any graph is a subgraph of itself
theorem G_is_subgraph_of_G {α : Type u} [DecidableEq α] : ∀ G : Graph α, subgraph G G := by
  intros G
  unfold subgraph
  apply And.intro
  · exact Eq.subset rfl
  · exact Eq.subset rfl

-- The completely empty graph is a subset of all graphs
theorem completely_empty_is_subgraph_of_G {α : Type u} [DecidableEq α] :
  ∀ G : Graph α, subgraph completelyEmptyGraph G := by
  intros G
  unfold subgraph completelyEmptyGraph makeGraph
  simp only [Set.empty_subset, Set.prod_empty, Set.inter_self, and_self]


-- A simple graph is loopless and undirected
-- (the fact that E isn't a multiset deals with having no parallel edges for us)
class SimpleGraph {α : Type u} [DecidableEq α] (G : Graph α) where
  loopless  : ∀ v   : α, (v, v) ∉ G.EdgeSet
  reflexive : ∀ u v : α, (u, v) ∈ G.EdgeSet ↔ (v, u) ∈ G.EdgeSet

-- The complete graph on a given set of vertices
--def completeOn {α : Type u} (VertexSet : Finset α) : FiniteGraph α :=
--  makeFiniteGraph VertexSet ((Finset.product VertexSet VertexSet) - {(i, i) | i ∈ VertexSet})

-- All edges in a simple graph have different endpoints
lemma simpleGraphsHaveNoSelfLoops {α : Type u} [DecidableEq α] (G : Graph α) [G_is_simple : SimpleGraph G] :
  ∀ e ∈ G.EdgeSet, e.1 ≠ e.2
  := by
  intros e e_is_edge
  have ll := G_is_simple.loopless
  contrapose! ll
  use e.1
  exact Eq.mpr (congrFun (congrArg Membership.mem (congrArg (Prod.mk e.1) ll)) G.EdgeSet) e_is_edge

-- All simple graphs are subgraphs of the complete graph
theorem subgraphOfCompleteGraph {α : Type u} [DecidableEq α]
  (G : Graph α) [G_is_simple: SimpleGraph G]
  (H : Graph α) (H_is_complete : complete H) (H_has_more_verts : G.VertexSet ⊆ H.VertexSet)
  : subgraph G H := by
  unfold complete at H_is_complete
  unfold subgraph
  refine (and_iff_right H_has_more_verts).mpr ?_
  unfold adjacent at H_is_complete
  intro e e_is_edge
  have constl := H_has_more_verts (G.EdgeSetConstriction e e_is_edge).left
  have constr := H_has_more_verts (G.EdgeSetConstriction e e_is_edge).right
  have e1_e2_differ := simpleGraphsHaveNoSelfLoops G e e_is_edge
  exact H_is_complete e.1 constl e.2 constr e1_e2_differ


-- Definition of a clique
structure Clique {α : Type u} [DecidableEq α] (G : Graph α) where
  Vertices : Set α
  IsClique : ∀ u ∈ Vertices, ∀ v ∈ Vertices, u ≠ v → adjacent G u v

-- Definition of a colouring (restricted to finite colours)
structure Coloring {α : Type u} [DecidableEq α] (G : Graph α) where
  Partition   : Set (Set α)
  IsPartition : ∀ a ∈ G.VertexSet, ∃! p, p ∈ Partition ∧ a ∈ p

-- The complete graph has a clique that is the entire graph
def CompleteClique
  {α : Type u} [DecidableEq α] (G : Graph α) (G_is_complete : complete G)
  : Clique G :=
  {
    Vertices := G.VertexSet,
    IsClique := by
      intros u u_vertex v v_vertex
      unfold adjacent
      unfold complete at G_is_complete
      exact fun a => G_is_complete u u_vertex v v_vertex a
  }

-- Any graph has a colouring where each vertex gets its own colour
def CompleteColoring
  {α : Type u} [DecidableEq α] (G : Graph α)
  : Coloring G :=
  {
    Partition := {{v} | v ∈ G.VertexSet},

    IsPartition := by
      simp only [Set.mem_setOf_eq]
      intros a a_vertex
      unfold ExistsUnique
      use {a}
      simp only [Set.singleton_eq_singleton_iff, exists_eq_right, Set.mem_singleton_iff, and_true,
        and_imp, forall_exists_index, forall_apply_eq_imp_iff₂]
      apply And.intro
      · exact a_vertex
      · intros b _ a_eq_b
        exact id a_eq_b.symm
  }

def cycle (n : ℕ) : Graph ℕ :=
  let vertices := Finset.range n
  let edges := { (i, (i+1) % n) | i ∈ vertices } ∪ { ((i+1) % n, i) | i ∈ vertices }
  makeGraph vertices edges


-- A cycle has a 3-colouring
-- Note that this theorem was, with our level of understanding, basically impossible to prove
-- using Mathlib's relational definition of a graph
-- and functional definition of a graph colouring
def CycleColoring (n : ℕ) : Coloring (cycle n) :=
  let G := cycle n
  {
    Partition := {{0}, {i | i ∈ G.VertexSet ∧ i%2 == 0 ∧ i ≠ 0}, {i | i ∈ G.VertexSet ∧ i%2 == 1} },

    IsPartition := by
      simp only [beq_iff_eq, ne_eq, Set.sep_and, Set.mem_singleton_iff, Set.mem_insert_iff]
      intros a a_vertex
      unfold ExistsUnique
      simp only [and_imp, forall_eq_or_imp, Set.mem_singleton_iff, Set.mem_inter_iff,
        Set.mem_setOf_eq, forall_eq]

      by_cases a_is_zero : a = 0

      · use {0}
        simp only [true_or, Set.mem_singleton_iff, true_and, implies_true]
        apply And.intro
        · exact a_is_zero
        . apply And.intro
          · intros _ a_even _ a_neq_zero
            exact (a_neq_zero a_is_zero).elim
          · intros _
            rw [a_is_zero]
            simp only [Nat.zero_mod, zero_ne_one, IsEmpty.forall_iff]

      . by_cases a_is_even : a % 2 = 0
        use {i | i ∈ G.VertexSet ∧ i%2 == 0 ∧ i ≠ 0}
        simp only [beq_iff_eq, ne_eq, Set.sep_and, true_or, or_true, Set.mem_inter_iff,
          Set.mem_setOf_eq, true_and, implies_true]
        apply And.intro
        · apply And.intro
          · exact { left := a_vertex, right := a_is_even }
          · exact { left := a_vertex, right := a_is_zero }

        · apply And.intro
          · intros a_defo_zero
            exact (a_is_zero a_defo_zero).elim
          · intros _ a_is_odd
            have a_not_even : ¬ a % 2 = 0 := by
              exact Nat.mod_two_ne_zero.mpr a_is_odd
            exact (a_not_even a_is_even).elim

        · have a_is_odd : a % 2 = 1 := by
            exact Nat.mod_two_ne_zero.mp a_is_even
          use {i | i ∈ G.VertexSet ∧ i%2 == 1}
          simp only [beq_iff_eq, or_true, Set.mem_setOf_eq, true_and, implies_true, and_true]
          apply And.intro
          · exact { left := a_vertex, right := a_is_odd }
          · apply And.intro
            · intros a_defo_zero
              exact (a_is_zero a_defo_zero).elim
            · intros _ a_defo_even
              exact fun a_1 a => (a_is_even a_defo_even).elim
  }
