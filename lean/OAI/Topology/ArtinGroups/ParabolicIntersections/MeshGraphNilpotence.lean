import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshGraphWeights
import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshNormalization

namespace OAI

/-! Finite mesh path bounds, including disconnected positive Cartan graphs. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
open Matrix
variable {V R : Type} [Fintype V] (G : SimpleGraph V) [Ring R] [Algebra ℂ R]

theorem connected_mesh_paths_vanish (hG : G.Connected)
    (hcartan : ((2 : ℝ) • (1 : Matrix V V ℝ)-G.adjMatrix ℝ).PosDef)
    (B : ∀ u v, G.Adj u v → R)
    (hmesh : ∀ v, (∑ u : {u : V // G.Adj u v},
      B v u.val u.property.symm * B u.val v u.property)=0) :
    ∃ N : ℕ, 0<N ∧ ∀ v p, meshPathEvaluate G B N v p=0 := by
  by_cases hedge : ∃ u v, G.Adj u v
  · obtain ⟨μ,d,hμ,hd0,hd2,heigen⟩ := mesh_graph_positive_weights G hG hedge hcartan
    exact allPlus_mesh_paths_vanish G μ hμ d hd0 hd2 heigen B hmesh
  · refine ⟨1,by omega,?_⟩
    intro v p
    exact (hedge ⟨p.1.val,v,p.1.property⟩).elim

omit [Fintype V] [Algebra ℂ R] in
lemma meshPathEvaluate_longer (B : ∀ u v, G.Adj u v → R) (N : ℕ)
    (hN : ∀ v p, meshPathEvaluate G B N v p=0) :
    ∀ n, N≤n → ∀ v p, meshPathEvaluate G B n v p=0 := by
  intro n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => exact hN
  | succ k ih =>
    intro v p
    change meshPathEvaluate G B (N+k) p.1.val p.2 * B p.1.val v p.1.property=0
    rw [ih (by omega),zero_mul]

omit [Fintype V] in
def meshPathInComponent (C : G.ConnectedComponent) :
    (n : ℕ) → (v : C) → MeshPaths G n v.val → MeshPaths C.toSimpleGraph n v
  | 0, _, _ => PUnit.unit
  | n+1, v, p =>
    let u : C := ⟨p.1.val,C.mem_supp_of_adj_mem_supp v.property p.1.property.symm⟩
    ⟨⟨u,p.1.property⟩,meshPathInComponent C n u p.2⟩

omit [Fintype V] [Algebra ℂ R] in
lemma meshPathInComponent_evaluate (C : G.ConnectedComponent)
    (B : ∀ u v, G.Adj u v → R) : ∀ n v p,
    meshPathEvaluate C.toSimpleGraph (fun u v h => B u.val v.val h) n v
      (meshPathInComponent G C n v p)=meshPathEvaluate G B n v.val p := by
  intro n
  induction n with
  | zero => intro v p; rfl
  | succ n ih =>
    intro v p
    dsimp only [meshPathInComponent,meshPathEvaluate]
    rw [ih]

omit [Fintype V] in
lemma mesh_component_cartan (C : G.ConnectedComponent)
    (hcartan : ((2 : ℝ) • (1 : Matrix V V ℝ)-G.adjMatrix ℝ).PosDef) :
    let _ : DecidableEq C := Classical.decEq C
    ((2 : ℝ) • (1 : Matrix C C ℝ)-C.toSimpleGraph.adjMatrix ℝ).PosDef := by
  let : DecidableEq C := Classical.decEq C
  have h := hcartan.submatrix (e := ((↑) : C → V)) Subtype.val_injective
  convert h using 1
  ext u v
  by_cases huv : u=v
  · subst v
    simp [Matrix.submatrix_apply]
  · have hval : u.val≠v.val := fun hh => huv (Subtype.ext hh)
    simp [Matrix.submatrix_apply,SimpleGraph.adjMatrix_apply,
      SimpleGraph.ConnectedComponent.toSimpleGraph,SimpleGraph.induce,huv,hval]
    rfl

omit [Fintype V] in
def meshComponentNeighborEquiv (C : G.ConnectedComponent) (v : C) :
    {u : C // C.toSimpleGraph.Adj u v} ≃ {u : V // G.Adj u v.val} where
  toFun u := ⟨u.val.val,u.property⟩
  invFun u := ⟨⟨u.val,C.mem_supp_of_adj_mem_supp v.property u.property.symm⟩,u.property⟩
  left_inv u := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv u := by apply Subtype.ext; rfl

/-- Every finite graph with positive definite Cartan form has a finite
all-plus mesh path bound, whether or not the graph is connected. -/
theorem positive_cartan_mesh_paths_vanish
    (hcartan : ((2 : ℝ) • (1 : Matrix V V ℝ)-G.adjMatrix ℝ).PosDef)
    (B : ∀ u v, G.Adj u v → R)
    (hmesh : ∀ v, (∑ u : {u : V // G.Adj u v},
      B v u.val u.property.symm * B u.val v u.property)=0) :
    ∃ N : ℕ, 0<N ∧ ∀ v p, meshPathEvaluate G B N v p=0 := by
  have hC (C : G.ConnectedComponent) : ∃ N : ℕ, 0<N ∧
      ∀ v p, meshPathEvaluate C.toSimpleGraph (fun u v h => B u.val v.val h) N v p=0 := by
    apply connected_mesh_paths_vanish C.toSimpleGraph C.connected_toSimpleGraph
      (mesh_component_cartan G C hcartan)
    intro v
    calc
      _ = ∑ u : {u : V // G.Adj u v.val}, B v.val u.val u.property.symm *
          B u.val v.val u.property := by
        apply Fintype.sum_equiv (meshComponentNeighborEquiv G C v)
        intro u
        rfl
      _ = 0 := hmesh v.val
  let n : G.ConnectedComponent → ℕ := fun C => (hC C).choose
  have hn (C : G.ConnectedComponent) : ∀ v p,
      meshPathEvaluate C.toSimpleGraph (fun u v h => B u.val v.val h) (n C) v p=0 :=
    (hC C).choose_spec.2
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let N := Finset.univ.sup n+1
  refine ⟨N,by dsimp [N]; omega,?_⟩
  intro v p
  let C := G.connectedComponentMk v
  have hv : v∈C := by exact (C.mem_supp_iff v).mpr rfl
  have hbound : n C≤N := by
    have hle := Finset.le_sup (f := n) (Finset.mem_univ C)
    dsimp [N]
    omega
  have hz := meshPathEvaluate_longer C.toSimpleGraph (fun u v h => B u.val v.val h)
    (n C) (hn C) N hbound ⟨v,hv⟩ (meshPathInComponent G C N ⟨v,hv⟩ p)
  rwa [meshPathInComponent_evaluate] at hz

end HarmonicArtin.ParabolicIntersections

end OAI
