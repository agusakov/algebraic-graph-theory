import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Walk
/-
Copyright (c) 2024 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov
-/

/-
Collection of various experiments to do with graph definitions.
-/

universe u

namespace SimpleGraph

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G G₁ G₂ : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]

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

theorem degree_eq (hG : G₁ = G₂) (v : V) :
  G₁.degree v = G₂.degree v := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  have h2 : G₁.neighborFinset v = G₂.neighborFinset v := by
    ext w;
    simp only [mem_neighborFinset]
    rw [hG]
  rw [h2]

@[simp] lemma degree_zero : (∀ v : V, G.degree v = 0) ↔ G = ⊥ := by
  refine ⟨fun hv => ?_, fun hG v => ?_⟩
  · by_contra hb
    obtain ⟨⟨v, w⟩, he⟩ := edgeSet_nonempty.2 hb
    apply ne_of_gt ((G.degree_pos_iff_exists_adj v).2 ⟨w, he⟩) (hv v)
  · rw [degree_eq _ _ hG]
    apply bot_degree

/--
Number of connected components finite - there's probably a cleaner way to do this
-/
noncomputable instance : Fintype G.ConnectedComponent := by
  haveI := Finite.of_surjective G.connectedComponentMk (surjective_quot_mk G.Reachable)
  apply Fintype.ofFinite G.ConnectedComponent

lemma IsAcyclic.card_edgeFinset (c : G.ConnectedComponent) [Nonempty c.supp]
(hG : (G.induce c.supp).IsAcyclic) :
  Finset.card (SimpleGraph.induce c.supp G).edgeFinset + 1 = Fintype.card c.supp := by
  apply IsTree.card_edgeFinset ⟨?_, hG⟩
  apply Connected.mk ?_
  · intros v w
    obtain ⟨v, hv⟩ := v
    obtain ⟨w, hw⟩ := w
    have h3 : G.Reachable v w := by
      · rw [← SimpleGraph.ConnectedComponent.eq, (c.mem_supp_iff v).1 hv, (c.mem_supp_iff w).1 hw]
    obtain ⟨p⟩ := h3
    induction p with
    | nil => use (@SimpleGraph.Walk.copy _ _ (⟨_, hv⟩ : c.supp) (⟨_, hw⟩ : c.supp)
        (⟨_, hw⟩ : c.supp) (⟨_, hw⟩ : c.supp)
        (Walk.nil : (induce c.supp G).Walk (⟨_, hv⟩ : c.supp) (⟨_, hv⟩ : c.supp)) (by simp only) rfl)
    | cons h _ ih => {
        have h2 := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h.symm
        rw [(c.mem_supp_iff _).1 hv, ← c.mem_supp_iff] at h2
        specialize ih h2 hw
        have h4 : (induce c.supp G).Adj (⟨_, hv⟩ : c.supp) (⟨_, h2⟩ : c.supp) := by
          simp only [comap_adj, Function.Embedding.coe_subtype]
          apply h
        apply Reachable.trans (Adj.reachable h4) ih }



/-lemma IsAcyclic.card_edgeFinset_components [Fintype V] [Nontrivial V] (hG : G.IsAcyclic) :
    Finset.card G.edgeFinset = ∑ c : G.ConnectedComponent, Finset.card c.edgeFinset := by sorry-/

theorem Acyclic.existsLeaf (h : G.IsAcyclic) (hG : G ≠ ⊥) :
  ∃ v : V, G.degree v = 1 := by
  obtain ⟨e, he⟩ := edgeSet_nonempty.2 hG
  by_contra hv
  push_neg at hv

  have h2 := sum_degrees_eq_twice_card_edges G
  sorry

def pruferConstructStep (G : SimpleGraph (Fin (n + 2))) (m : Fin (n + 2)) (p : List (Fin (n + 2))) :
  SimpleGraph (Fin (n + 2)) := sorry

/-- For each node set its degree to the number of times it appears in the sequence plus 1 -/
def degreeList (p : List (Fin (n + 2))) : List ℕ :=
  (List.range (n + 2)).map fun i => List.count i p + 1

/-lemma degreeList_length (p : List (Fin (n + 2))) (hp : List.length p = n) :
  (degreeList p).length = n + 2 := by sorry-/

def graphConstructStep (G : SimpleGraph (Fin (n + 2))) (m : Fin (n + 2)) (d : List ℕ) :
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
