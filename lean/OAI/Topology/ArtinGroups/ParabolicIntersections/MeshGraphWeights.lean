import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshPerron

namespace OAI

/-! Positive mesh weights for a connected graph with positive Cartan form. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
open Matrix
variable {V : Type} [Fintype V] (G : SimpleGraph V)

lemma mesh_adjacency_sum (y : V → ℝ) (v : V) :
    (G.adjMatrix ℝ *ᵥ y) v=∑ u : {u : V // G.Adj u v}, y u := by
  rw [G.adjMatrix_mulVec_apply]
  exact Finset.sum_subtype (G.neighborFinset v) (by intro u; simp [G.adj_comm]) y

lemma mesh_connected_eigenvector_pos (hG : G.Connected) (d : ℝ)
    (y : V → ℝ) (hy : y≠0) (hnonneg : ∀ v, 0≤y v)
    (heigen : G.adjMatrix ℝ *ᵥ y=d • y) : ∀ v, 0<y v := by
  have hzero_adj {u v : V} (hadj : G.Adj u v) (hu : y u=0) : y v=0 := by
    have hs : (∑ w : {w : V // G.Adj w u}, y w)=0 := by
      have h := congrFun heigen u
      rw [mesh_adjacency_sum] at h
      simpa only [Pi.smul_apply,smul_eq_mul,hu,mul_zero] using h
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun (w : {w : V // G.Adj w u}) _ => hnonneg w.val)).mp hs
      ⟨v,hadj.symm⟩ (Finset.mem_univ _)
  have hzero_path {u v : V} (p : G.Walk u v) : y u=0 → y v=0 := by
    induction p with
    | nil => exact id
    | @cons a b c hab p ih => exact fun ha => ih (hzero_adj hab ha)
  intro u
  by_contra hpos
  have hu : y u=0 := le_antisymm (le_of_not_gt hpos) (hnonneg u)
  apply hy
  funext v
  exact hzero_path (hG.preconnected u v).some hu

/-- Positive definiteness of `2I-B` gives exactly the spectral interval
needed by the essential-path argument, on each nontrivial component. -/
theorem mesh_graph_positive_weights (hG : G.Connected)
    (hedge : ∃ u v, G.Adj u v)
    (hcartan : ((2 : ℝ) • (1 : Matrix V V ℝ)-G.adjMatrix ℝ).PosDef) :
    ∃ (μ : V → ℝ) (d : ℝ), (∀ v, 0<μ v) ∧ 0<d ∧ d<2 ∧
      ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=d*μ v := by
  let : Nonempty V := hG.nonempty
  have hsym : (G.adjMatrix ℝ).IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    exact G.isSymm_adjMatrix
  have hentries : ∀ u v, 0≤G.adjMatrix ℝ u v := by
    intro u v
    simp only [SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  obtain ⟨d,μ,hne,hnonneg,heigen⟩ := mesh_nonnegative_top_eigenvector (G.adjMatrix ℝ) hsym hentries
  have hμ := mesh_connected_eigenvector_pos G hG d μ hne hnonneg heigen
  have heq (v : V) : (∑ u : {u : V // G.Adj u v}, μ u)=d*μ v := by
    have h := congrFun heigen v
    simpa only [mesh_adjacency_sum,Pi.smul_apply,smul_eq_mul] using h
  obtain ⟨u,v,huv⟩ := hedge
  have hsum : 0<(∑ w : {w : V // G.Adj w v}, μ w) := by
    exact Finset.sum_pos' (fun w _ => (hμ w).le)
      ⟨⟨u,huv⟩,Finset.mem_univ _,hμ u⟩
  have hd : 0<d := by
    rw [heq] at hsum
    exact (mul_pos_iff.mp hsum).resolve_right (by intro h; exact (not_lt_of_ge (hμ v).le) h.2) |>.1
  have hform := hcartan.dotProduct_mulVec_pos hne
  simp only [star_trivial,sub_mulVec,smul_mulVec,one_mulVec,heigen,
    dotProduct_sub,dotProduct_smul,smul_eq_mul] at hform
  have hsq : 0≤μ ⬝ᵥ μ := Finset.sum_nonneg (fun i _ => mul_self_nonneg (μ i))
  have hd2 : d<2 := by
    by_contra h
    have hm : d*(μ ⬝ᵥ μ)≥2*(μ ⬝ᵥ μ) := mul_le_mul_of_nonneg_right (le_of_not_gt h) hsq
    linarith
  exact ⟨μ,d,hμ,hd,hd2,heq⟩

end HarmonicArtin.ParabolicIntersections

end OAI
