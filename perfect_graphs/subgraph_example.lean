import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
--import Mathlib.Combinatorics.SimpleGraph.Basic
--import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Clique
--import Mathlib.Combinatorics.SimpleGraph.chromaticNumber
import Mathlib.Data.Fintype.Basic
import Aesop.Check
import Mathlib.Logic.Basic
import Aesop.Tree.Data
set_option trace.aesop true



namespace PerfectGraphs

#check SimpleGraph (Fin 5)





-- lemma Symm : Symmetric AdjExample := by
-- dsmip at *

/-
def CliqueNumber {V : Type} (G : SimpleGraph V) (hasNclique): ℕ :=
-/

def G : SimpleGraph (Fin 5) where
  Adj x y  :=
    x = 0 ∧ y = 1 ∨ x = 1 ∧ y = 0 ∨ x = 2 ∧ y = 3 ∨ x = 3 ∧ y = 2
  symm a b h := by
    aesop
  loopless a b := by
    aesop
    refine (?_ (id right.symm)).snd
    refine (?_ (id left.symm)).snd
    done
    

def G' : SimpleGraph (Fin 5) where
  Adj x y  :=
    --  notice that I removed the `if .. then .. else ..` since it was not necessary
    x = 0 ∧ y = 1 ∨ x = 1 ∧ y = 0 
  symm a b h := by
    --  `aesop` is a "search" tactic: among other things, it splits all cases and tries
    --  various finishing tactics.
    aesop
  loopless a b := by
    aesop

open SimpleGraph
def G'' : Subgraph G where
 verts := {0, 1}
 Adj x y := x = 0 ∧ y = 1 ∨ x = 1 ∧ y = 0 
 adj_sub := by 
  intros v w
  intro f
  unfold Adj G
  aesop
 edge_vert := by 
  aesop
 symm Symmetric Adj := by aesop_graph



open SimpleGraph
theorem subg : G' ≤ G := by
  unfold G; 
  unfold G';
  aesop_graph






#check (G'' : Subgraph G)


#check G'.IsSubgraph G

theorem ex : G'.IsSubgraph G := by
  unfold IsSubgraph
  unfold G G'
  aesop

def PGIsInduced {V : Type} (H : SimpleGraph V) (H' : Subgraph H) : Prop :=
  ∀ {v w : V}, v ∈ H'.verts → w ∈ H'.verts → H.Adj v w → H'.Adj v w

def PGIsInduced' {V : Type} (H : SimpleGraph V) (H' : SimpleGraph V) : Prop :=
  ∀ {v w : V}, (H.Adj v w → H'.Adj v w) ∨ (H'.neighborSet v = ∅) ∨ (H'.neighborSet w = ∅)

def F := G.toSubgraph G' subg
#check F

open Subgraph

theorem ex22 : F.IsInduced := by
  unfold F
  unfold IsInduced
  unfold G
  unfold G'
  unfold toSubgraph
  unfold SimpleGraph.Adj
  simp
  intros v w
  sorry

  

theorem ex2 : PGIsInduced G G'' := by
 unfold G
 unfold G''
 unfold PGIsInduced
 aesop
 exact Fin.rev_inj.mp (id left.symm)
 exact neg_add_eq_zero.mp (id right.symm)
 rw [← right] 
 exact self_eq_add_left.mp right
 exact self_eq_add_left.mp (id right.symm)
 done

theorem ex22 : PGIsInduced' G G' := by
  unfold PGIsInduced'
  unfold G
  unfold G'
  intros v w
  cases v with
  | mk val isLt => interval_cases val;
                   · simp only; left; aesop; exact sub_eq_zero.mp (id left.symm); sorry
                   · sorry
                   · sorry
                   · sorry
                   · sorry

def hasNClique {V : Type} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ t, G.IsNClique n t

noncomputable def CliqueNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sSup { n : ℕ | hasNClique G n }

theorem equivCliqueNumber {V : Type} (G : SimpleGraph V) (k : ℕ) (NClique : hasNClique G k) (notNPlusOneClique : ¬ hasNClique G (k+1)) : CliqueNumber G = k := by
  sorry

/- Maybe can redefine this using cliqueSet -/




theorem faveExampleG : CliqueNumber G = 2 := by
  unfold CliqueNumber
  apply equivCliqueNumber
  unfold hasNClique
  · use {0,1}
    apply IsNClique.mk
    unfold IsClique
    unfold G
    aesop_graph
    norm_num
    
  · norm_num
    unfold hasNClique
    rw [@not_exists]
    intro t
    intro f
    cases t with
    | mk val nodup => interval_cases val


def cycle (n : ℕ) : (SimpleGraph (ZMod n)) :=
  SimpleGraph.fromRel (λ x y => x-y = 1)

theorem sizeOfSet : Finset.card {0, 1} = 2 := by
  norm_num

theorem CliqueNumberCycleIsTwo (n : ℕ) (h : n ≥ 4) : CliqueNumber (cycle n) = 2 := by
  unfold CliqueNumber
  apply equivCliqueNumber
  unfold hasNClique
  · use {0,1}
    apply IsNClique.mk
    unfold IsClique
    unfold cycle
    aesop_graph
    refine Finset.card_doubleton ?h.card_eq.h
    refine zero_mem_nonunits.mp ?h.card_eq.h.a
    rw [@Set.mem_def]
    apply?
    rw [@mem_nonunits_iff]
    sorry
    

  · norm_num
    unfold hasNClique
    rw [@not_exists]
    intro x
    rw [@is3Clique_iff]
    rw [@not_exists]
    intro a
    rw [@not_exists]
    intro b
    rw [@not_exists]
    intro c
    intro f
    cases f with
    | intro f1 f2 =>
      cases f2 with
      | intro f2 f3 =>
        cases f3 with
        | intro f3 f4 =>
    revert f1
    unfold SimpleGraph.Adj
    unfold cycle
    simp
    intro f11
    intro f12
    cases f12 with
    | inl h1 => revert f2
                unfold SimpleGraph.Adj
                unfold cycle
                simp
                intro f21
                intro f22
                cases f22 with
                | inl h2 => revert f3
                            unfold SimpleGraph.Adj
                            unfold cycle
                            simp
                            intro f31
                            intro f32
                            cases f32 with
                            | inl h3 => rw [<- h1] at h2
                            | inr h3 => sorry

                | inr h2 => sorry
    | inr h1 => sorry
    revert f2
    unfold SimpleGraph.Adj
    unfold cycle
    aesop
    revert f3
    unfold SimpleGraph.Adj
    unfold cycle
    
        
        
    
    