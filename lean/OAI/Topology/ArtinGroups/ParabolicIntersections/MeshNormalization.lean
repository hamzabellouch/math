import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshPathEvaluation

namespace OAI

/-! Passage from the weighted essential-path relations to all-plus meshes. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V R : Type} [Fintype V] (G : SimpleGraph V) [Ring R] [Algebra ℂ R]

lemma mesh_normalization_weight (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    Real.sqrt (a/b)*(Real.sqrt a)⁻¹*(Real.sqrt b)⁻¹=b⁻¹ := by
  rw [Real.sqrt_div ha.le]
  have hsa := ne_of_gt (Real.sqrt_pos.mpr ha)
  have hsb := ne_of_gt (Real.sqrt_pos.mpr hb)
  calc
    _ = ((Real.sqrt b)^2)⁻¹ := by field_simp
    _ = b⁻¹ := by rw [Real.sq_sqrt hb.le]

noncomputable def meshRescale (μ : V → ℝ) (B : ∀ u v, G.Adj u v → R)
    (u v : V) (h : G.Adj u v) : R :=
  ((Real.sqrt (μ v))⁻¹ : ℂ) • B u v h

lemma meshRescale_relation (μ : V → ℝ) (hμ : ∀ v, 0<μ v)
    (B : ∀ u v, G.Adj u v → R)
    (hmesh : ∀ v, (∑ u : {u : V // G.Adj u v},
      B v u.val u.property.symm * B u.val v u.property)=0) (v : V) :
    (∑ u : {u : V // G.Adj u v}, (Real.sqrt (μ u/μ v) : ℂ) •
      (meshRescale G μ B v u.val u.property.symm * meshRescale G μ B u.val v u.property))=0 := by
  have hc (u : {u : V // G.Adj u v}) :
      (Real.sqrt (μ u/μ v) : ℂ) * ((Real.sqrt (μ v))⁻¹ : ℂ) *
        ((Real.sqrt (μ u))⁻¹ : ℂ)=(μ v)⁻¹ := by
    calc
      _ = (Real.sqrt (μ u/μ v) : ℂ) * ((Real.sqrt (μ u))⁻¹ : ℂ) *
          ((Real.sqrt (μ v))⁻¹ : ℂ) := by ring
      _ = _ := by exact_mod_cast mesh_normalization_weight (μ u) (μ v) (hμ u) (hμ v)
  simp only [meshRescale,smul_mul_assoc,mul_smul_comm,smul_smul]
  simp only [←mul_assoc,hc]
  rw [←Finset.smul_sum,hmesh,smul_zero]

noncomputable def meshPathScale (μ : V → ℝ) :
    (n : ℕ) → (v : V) → MeshPaths G n v → ℂ
  | 0, _, _ => 1
  | n+1, v, p => meshPathScale μ n p.1.val p.2 * ((Real.sqrt (μ v))⁻¹ : ℂ)

omit [Fintype V] in
lemma meshPathScale_ne_zero (μ : V → ℝ) (hμ : ∀ v, 0<μ v) :
    ∀ n v p, meshPathScale G μ n v p≠0 := by
  intro n
  induction n with
  | zero => intro v p; exact one_ne_zero
  | succ n ih =>
    intro v p
    change meshPathScale G μ n p.1.val p.2 * ((Real.sqrt (μ v))⁻¹ : ℂ)≠0
    apply mul_ne_zero (ih p.1.val p.2)
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (hμ v))))

omit [Fintype V] in
lemma meshRescale_evaluate (μ : V → ℝ) (B : ∀ u v, G.Adj u v → R) :
    ∀ n v p, meshPathEvaluate G (meshRescale G μ B) n v p=
      meshPathScale G μ n v p • meshPathEvaluate G B n v p := by
  intro n
  induction n with
  | zero => intro v p; exact (one_smul ℂ (1 : R)).symm
  | succ n ih =>
    intro v p
    change meshPathEvaluate G (meshRescale G μ B) n p.1.val p.2 *
      (((Real.sqrt (μ v))⁻¹ : ℂ) • B p.1.val v p.1.property)=_
    rw [ih,smul_mul_assoc,mul_smul_comm,smul_smul]
    rfl

/-- Unweighted all-plus mesh relations suffice for the same finite path
bound. The rescaling factors are explicitly proved nonzero. -/
theorem allPlus_mesh_paths_vanish (μ : V → ℝ) (hμ : ∀ v, 0<μ v)
    (δ : ℝ) (hδ0 : 0<δ) (hδ2 : δ<2)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v)
    (B : ∀ u v, G.Adj u v → R)
    (hmesh : ∀ v, (∑ u : {u : V // G.Adj u v},
      B v u.val u.property.symm * B u.val v u.property)=0) :
    ∃ N : ℕ, 0<N ∧ ∀ v p, meshPathEvaluate G B N v p=0 := by
  obtain ⟨N,hN,hzero⟩ := weighted_mesh_paths_vanish G μ hμ δ hδ0 hδ2 heigen
    (meshRescale G μ B) (meshRescale_relation G μ hμ B hmesh)
  refine ⟨N,hN,?_⟩
  intro v p
  have h := hzero v p
  rw [meshRescale_evaluate] at h
  exact (smul_eq_zero.mp h).resolve_left (meshPathScale_ne_zero G μ hμ N v p)

end HarmonicArtin.ParabolicIntersections

end OAI
