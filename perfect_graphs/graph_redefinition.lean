import Mathlib.Tactic

-- A finite graph is a pair (VertexSet, EdgeSet)
-- where V is a finite set of vertices of type α
-- and E is a finite set of edges between elements of type α
structure FiniteGraph (α : Type u) where
  VertexSet : Finset α
  EdgeSet   : Finset (α × α)


def makeFiniteGraph {α : Type u} (vertices : Finset α) (edges : Finset (α × α)) : FiniteGraph α :=
  { VertexSet := vertices, EdgeSet := edges }

-- The completely empty graph
def completelyEmptyGraph {α : Type u} : FiniteGraph α := makeFiniteGraph ∅ ∅

-- The graph with no edges on a set of vertices
def emptyGraph {α : Type u} (vertices : Finset α) : FiniteGraph α := makeFiniteGraph vertices ∅

-- Check that K3 is a graph
def k3 := makeFiniteGraph {0, 1, 2} {(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)}

-- u is adjacent to v iff (u, v) is an edge in our graph
def adjacent {α : Type u} (G : FiniteGraph α) (u v : α) : Prop
  := (u, v) ∈ G.EdgeSet

-- A graph is complete if every vertex is connected to every other vertex
def complete {α : Type u} (G : FiniteGraph α) : Prop
  := ∀ u ∈ G.VertexSet, ∀ v ∈ G.VertexSet, u ≠ v → adjacent G u v


#check k3
#check adjacent k3 1 2

-- 1 and 2 are adjacent in k3
example : adjacent k3 1 2 := by
  unfold k3 adjacent makeFiniteGraph
  simp only [Finset.mem_singleton, Prod.mk.injEq, zero_ne_one, and_false, Finset.mem_insert,
    OfNat.one_ne_ofNat, OfNat.ofNat_ne_zero, and_self, OfNat.ofNat_ne_one, or_self,
    OfNat.zero_ne_ofNat, and_true, one_ne_zero, or_false, or_true]

-- k3 is complete
example : complete k3 := by
  unfold complete k3 makeFiniteGraph adjacent
  simp only [Finset.mem_singleton, OfNat.one_ne_ofNat, Finset.mem_insert, zero_ne_one, or_self,
    ne_eq, Prod.mk.injEq, and_false, OfNat.ofNat_ne_zero, and_self, OfNat.ofNat_ne_one,
    OfNat.zero_ne_ofNat, and_true, one_ne_zero, forall_eq_or_imp, or_false, false_or, forall_eq,
    not_true_eq_false, IsEmpty.forall_iff, not_false_eq_true, forall_true_left, or_true]


-- H is a subgraph of G iff V(H) ⊆ V(G) and E(H) ⊆ E(G)
def subgraph {α : Type u} (H : FiniteGraph α) (G : FiniteGraph α) :=
  H.VertexSet ⊆ G.VertexSet ∧ H.EdgeSet ⊆ G.EdgeSet

-- Any graph is a subgraph of itself
theorem G_is_subgraph_of_G {α : Type u} : ∀ G : FiniteGraph α, subgraph G G := by
  intros G
  unfold subgraph
  simp only [Finset.Subset.refl, and_self]

-- The completely empty graph is a subset of all graphs
theorem completely_empty_is_subgraph_of_G {α : Type u} : ∀ G : FiniteGraph α, subgraph completelyEmptyGraph G := by
  intros G
  unfold subgraph completelyEmptyGraph makeFiniteGraph
  simp only [Finset.empty_subset, and_self]



-- G and H are isomorphic iff there is a bijection between their edges
-- that preserves the edge relation
def isomorphic {α β : Type u} (G : FiniteGraph α) (H : FiniteGraph β) :=
  ∃ f : α → β,
  ∀ u v : α,
  adjacent G u v ↔ adjacent H (f u) (f v)


-- A simple graph is loopless and undirected
-- (the fact that E isn't a multiset deals with having no parallel edges for us)
class SimpleFiniteGraph {α : Type u} (G : FiniteGraph α) where
  loopless  : ∀ v   : α, (v, v) ∉ G.EdgeSet
  reflexive : ∀ u v : α, (u, v) ∈ G.EdgeSet ↔ (v, u) ∈ G.EdgeSet

-- The complete graph on a given set of vertices
def completeOn {α : Type u} (VertexSet : Finset α) : FiniteGraph α :=
  makeFiniteGraph VertexSet ((Finset.product VertexSet VertexSet) - {(i, i) | i ∈ VertexSet})

-- All simple graphs are subgraphs of the complete graph
theorem subgraphOfCompleteGraph {α : Type u} (G : FiniteGraph α) [G_is_simple: SimpleFiniteGraph G]
  (H : FiniteGraph α) (H_is_complete : complete H) (H_has_more_verts : G.VertexSet ⊆ H.VertexSet) : subgraph G H := by
  unfold complete at H_is_complete
  unfold subgraph
  refine (and_iff_right H_has_more_verts).mpr ?_
  unfold adjacent at H_is_complete
