import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshProjectionCutoff
import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshMatrixAction

namespace OAI

/-! Weighted mesh relations annihilate sufficiently long actual paths. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V R : Type} [Fintype V] (G : SimpleGraph V)
variable [Ring R] [Algebra ℂ R]

def meshPathEvaluate (B : ∀ u v, G.Adj u v → R) :
    (n : ℕ) → (v : V) → MeshPaths G n v → R
  | 0, _, _ => 1
  | n+1, v, p => meshPathEvaluate B n p.1.val p.2 * B p.1.val v p.1.property

omit [Fintype V] [Algebra ℂ R] in
lemma meshPathEvaluate_insert (B : ∀ u v, G.Adj u v → R) (n : ℕ) (v : V)
    (u : {u : V // G.Adj u v}) (p : MeshPaths G n v) :
    meshPathEvaluate G B (n+2) v (meshInsertBacktrack G u p)=
      meshPathEvaluate G B n v p * B v u.val u.property.symm * B u.val v u.property := rfl

lemma meshApply_contraction_adjoint (μ : V → ℝ) (n : ℕ) (v : V)
    (f : MeshPaths G (n+2) v → R) (p : MeshPaths G n v) :
    meshApply (meshContractionMatrix G μ n v).conjTranspose f p=
      ∑ u : {u : V // G.Adj u v}, (Real.sqrt (μ u/μ v) : ℂ) •
        f (meshInsertBacktrack G u p) := by
  change (∑ q, star (∑ u : {u : V // G.Adj u v},
    if q=meshInsertBacktrack G u p then (Real.sqrt (μ u/μ v) : ℂ) else 0) • f q)=_
  simp only [star_sum,apply_ite star,star_zero,Complex.star_def,Complex.conj_ofReal,
    Finset.sum_smul,ite_smul,zero_smul]
  rw [Finset.sum_comm]
  simp

lemma meshPathEvaluate_contracts (μ : V → ℝ) (B : ∀ u v, G.Adj u v → R)
    (hmesh : ∀ v, (∑ u : {u : V // G.Adj u v},
      (Real.sqrt (μ u/μ v) : ℂ) • (B v u.val u.property.symm * B u.val v u.property))=0)
    (n : ℕ) (v : V) :
    meshApply (meshContractionMatrix G μ n v).conjTranspose
      (meshPathEvaluate G B (n+2) v)=0 := by
  funext p
  rw [meshApply_contraction_adjoint]
  simp only [meshPathEvaluate_insert,Pi.zero_apply]
  calc
    _ = meshPathEvaluate G B n v p *
        (∑ u : {u : V // G.Adj u v}, (Real.sqrt (μ u/μ v) : ℂ) •
          (B v u.val u.property.symm * B u.val v u.property)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [mul_assoc,mul_smul_comm]
    _ = 0 := by rw [hmesh,mul_zero]

lemma meshPathEvaluate_extend (B : ∀ u v, G.Adj u v → R) {m n : ℕ}
    (A : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ)
    (hA : ∀ v, meshApply (A v) (meshPathEvaluate G B m v)=meshPathEvaluate G B n v)
    (v : V) : meshApply (meshExtendMatrix G A v) (meshPathEvaluate G B (m+1) v)=
      meshPathEvaluate G B (n+1) v := by
  let L (u : {u : V // G.Adj u v}) : R →ₗ[ℂ] R := {
    toFun := fun x => x*B u.val v u.property
    map_add' := fun x y => add_mul x y _
    map_smul' := fun a x => smul_mul_assoc a x _ }
  change meshApply (meshExtendMatrix G A v)
    (fun p => L p.1 (meshPathEvaluate G B m p.1.val p.2))=_
  rw [meshApply_extend]
  funext q
  rw [hA]
  rfl

/-- Every recursively defined projection acts as the identity after
evaluation in an algebra satisfying the weighted mesh relations. -/
theorem meshPathEvaluate_projection (μ : V → ℝ) (δ : ℝ)
    (B : ∀ u v, G.Adj u v → R)
    (hmesh : ∀ v, (∑ u : {u : V // G.Adj u v},
      (Real.sqrt (μ u/μ v) : ℂ) • (B v u.val u.property.symm * B u.val v u.property))=0) :
    ∀ n v, meshApply (meshProjection G μ δ n v) (meshPathEvaluate G B n v)=
      meshPathEvaluate G B n v := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro v; rw [meshProjection_zero,meshApply_one]
  | one => intro v; rw [meshProjection_one,meshApply_one]
  | more n _ ih =>
    intro v
    let Q := meshExtendMatrix G (meshProjection G μ δ (n+1)) v
    let C := meshContractionMatrix G μ n v
    let f := meshPathEvaluate G B (n+2) v
    have hQ : meshApply Q f=f := meshPathEvaluate_extend G B _ ih v
    have hQstar : Q.conjTranspose=Q := by
      simp only [Q,meshExtend_adjoint,meshProjection_selfAdjoint]
    have hkill : meshApply (C*Q).conjTranspose f=0 := by
      rw [Matrix.conjTranspose_mul,hQstar,meshApply_mul,hQ]
      exact meshPathEvaluate_contracts G μ B hmesh n v
    rw [meshProjection_step,meshApply_sub,meshApply_smul,meshApply_mul]
    change meshApply Q f - _ • meshApply (C*Q) (meshApply (C*Q).conjTranspose f)=f
    rw [hQ,hkill,meshApply_zero_right,smul_zero,sub_zero]

/-- A single finite path length vanishes in every algebra satisfying the
weighted mesh relations. The proof uses the actual finite path matrices. -/
theorem weighted_mesh_paths_vanish (μ : V → ℝ) (hμ : ∀ v, 0<μ v)
    (δ : ℝ) (hδ0 : 0<δ) (hδ2 : δ<2)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v)
    (B : ∀ u v, G.Adj u v → R)
    (hmesh : ∀ v, (∑ u : {u : V // G.Adj u v},
      (Real.sqrt (μ u/μ v) : ℂ) • (B v u.val u.property.symm * B u.val v u.property))=0) :
    ∃ N : ℕ, 0<N ∧ ∀ v p, meshPathEvaluate G B N v p=0 := by
  obtain ⟨N,hN,hzero⟩ := meshProjection_eventually_zero G μ hμ δ hδ0 hδ2 heigen
  refine ⟨N,hN,?_⟩
  intro v p
  have h := meshPathEvaluate_projection G μ δ B hmesh N v
  rw [hzero,meshApply_zero] at h
  exact (congrFun h p).symm

end HarmonicArtin.ParabolicIntersections

end OAI
