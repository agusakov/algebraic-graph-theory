import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Acyclic
/-
Copyright (c) 2024 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov
-/

/-
Collection of various experiments to do with graph definitions.
-/

open Matrix

universe u

namespace SimpleGraph

variable {V : Type u} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem isSRGWith.adjMatrix_mulVec_const_apply_of_regular [NonAssocSemiring α] {a : α}
    (h : G.IsSRGWith n k ℓ μ) {v : V} : (G.adjMatrix α *ᵥ Function.const _ a) v = k * a := by
  simp [h.regular v]

def vertexTransitive := ∀ v u : V, ∃ (fᵥᵤ : G ≃g G), fᵥᵤ v = u

theorem vertexTransitive.regular (h : G.vertexTransitive) (v : V) [Fintype (G.neighborSet v)] :
  G.IsRegularOfDegree (G.degree v) := by
  intros x
  obtain ⟨f, rfl⟩ := h v x
  simp only [← card_neighborSet_eq_degree, (Fintype.card_eq.2 ⟨f.mapNeighborSet v⟩)]

--def degreeSequence :

/-- A subgraph is acyclic if it is acyclic as a simple graph. -/
abbrev Subgraph.IsAcyclic (H : G.Subgraph) : Prop := H.coe.IsAcyclic

lemma Subgraph.Acyclic_of_Acyclic {G' : Subgraph G} (h : G.IsAcyclic) : G'.IsAcyclic := by
  intros v p
  rw [← Walk.map_isCycle_iff_of_injective (SimpleGraph.Subgraph.hom.injective)]
  apply h (Walk.map (SimpleGraph.Subgraph.hom G') p)

theorem subgraphAcyclic' (G' H : Subgraph G) (h : G' ≤ H) (h2 : H.IsAcyclic) : G'.IsAcyclic := by
  intros v p
  rw [← Walk.map_isCycle_iff_of_injective (SimpleGraph.Subgraph.inclusion.injective h)]
  apply h2 (Walk.map (SimpleGraph.Subgraph.inclusion h) p)

/-- For each node set its degree to the number of times it appears in the sequence plus 1 -/
def degreeList (p : List (Fin (n + 2))) : List ℕ :=
  (List.range (n + 2)).map fun i => List.count i p + 1

lemma degreeList_length (p : List (Fin (n + 2))) (hp : List.length p = n) :
  (degreeList p).length = n + 2 := by sorry

def pruferConstructStep (G : SimpleGraph (Fin (n + 2))) (m : Fin (n + 2)) (d : List ℕ) :
  SimpleGraph (Fin (n + 2)) where
    Adj := fun x y => G.Adj x y ∨ ((x = d.indexOf? 1) ∧ (y = m)) ∨ ((y = d.indexOf? 1) ∧ (x = m))
    symm := fun x y hxy => _
    loopless := _

/-theorem subgraphAcyclic_of {G' : Subgraph G} : G'.spanningCoe.IsAcyclic → G'.IsAcyclic :=
by
  intros h v p-/
  /-have f := embedding.spanningCoe G'.coe
  rw [subgraph.spanning_coe_coe] at f
  have h3 : function.injective f.to_hom := by
    · exact rel_embedding.injective f
  rw [← walk.map_is_cycle_iff_of_injective h3]
  exact h _ (walk.map f.to_hom p)-/


/-instance  (G' H : Subgraph G) (h : G' ≤ H) : hasLiftT (G'.verts) (H.verts) :=
by { fconstructor, exact λ v, ⟨v, h.1 (subtype.mem v)⟩, }-/

/-def pruferConstructStep (G : SimpleGraph (Fin n)) (hG : G.IsTree) (m : Fin n) :
  SimpleGraph (Fin (n + 1)) where
    Adj := fun x y => if x < n + 1 ∧ y < n + 1 then G.adj x y else
    symm := _
    loopless := _-/

/-theorem numTrees [Nontrivial V] [Fintype V] (hc : Fintype.card V = n) :
  Fintype.card {G : SimpleGraph V | G.IsTree} = n ^ (n - 2) := sorry-/

end SimpleGraph
