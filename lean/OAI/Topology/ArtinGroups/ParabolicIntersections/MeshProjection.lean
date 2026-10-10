import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshNaturality
import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshQuantum
import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshTrace

namespace OAI

/-! Jones--Wenzl projections on the actual finite path spaces. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} [Fintype V] (G : SimpleGraph V)

/-- The correction formula removes precisely the final contraction from
the already projected prefix. Only positive-index quantum integers occur
as denominators before the cutoff. -/
noncomputable def meshProjection (μ : V → ℝ) (δ : ℝ) :
    (n : ℕ) → (v : V) → Matrix (MeshPaths G n v) (MeshPaths G n v) ℂ
  | 0, _ => 1
  | 1, _ => 1
  | n+2, v =>
    let Q := meshExtendMatrix G (meshProjection μ δ (n+1)) v
    let T := meshContractionMatrix G μ n v * Q
    Q - (((meshQuantum δ (n+2)/meshQuantum δ (n+1))⁻¹ : ℝ) : ℂ) •
      (T.conjTranspose*T)

lemma meshProjection_zero (μ : V → ℝ) (δ : ℝ) (v : V) :
    meshProjection G μ δ 0 v=1 := rfl

lemma meshProjection_one (μ : V → ℝ) (δ : ℝ) (v : V) :
    meshProjection G μ δ 1 v=1 := rfl

lemma meshProjection_step (μ : V → ℝ) (δ : ℝ) (n : ℕ) (v : V) :
    meshProjection G μ δ (n+2) v =
      let Q := meshExtendMatrix G (meshProjection G μ δ (n+1)) v
      let T := meshContractionMatrix G μ n v*Q
      Q - (((meshQuantum δ (n+2)/meshQuantum δ (n+1))⁻¹ : ℝ) : ℂ) •
        (T.conjTranspose*T) := rfl

/-- Self-adjointness uses only the real coefficients in the recursion;
it holds even beyond the range in which the matrices are projections. -/
theorem meshProjection_selfAdjoint (μ : V → ℝ) (δ : ℝ) :
    ∀ n v, (meshProjection G μ δ n v).conjTranspose=meshProjection G μ δ n v := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro v; rw [meshProjection_zero,Matrix.conjTranspose_one]
  | one => intro v; rw [meshProjection_one,Matrix.conjTranspose_one]
  | more n _ ih =>
    intro v
    have hQ : (meshExtendMatrix G (meshProjection G μ δ (n+1)) v).conjTranspose=
        meshExtendMatrix G (meshProjection G μ δ (n+1)) v := by
      simp only [meshExtend_adjoint,ih]
    rw [meshProjection_step,Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,
      Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hQ]
    simp only [Complex.star_def,Complex.conj_ofReal]

/-- One step of the actual recursion, once its scalar identity has been
established from the preceding path identities. -/
theorem meshProjection_correct (μ : V → ℝ) (δ : ℝ) (n : ℕ) (v : V)
    (hden : meshQuantum δ (n+2)/meshQuantum δ (n+1)≠0)
    (hQstar : (meshExtendMatrix G (meshProjection G μ δ (n+1)) v).conjTranspose=
      meshExtendMatrix G (meshProjection G μ δ (n+1)) v)
    (hQsq : meshExtendMatrix G (meshProjection G μ δ (n+1)) v *
      meshExtendMatrix G (meshProjection G μ δ (n+1)) v=
      meshExtendMatrix G (meshProjection G μ δ (n+1)) v)
    (hscalar : meshContractionMatrix G μ n v *
      meshExtendMatrix G (meshProjection G μ δ (n+1)) v *
      (meshContractionMatrix G μ n v).conjTranspose =
      ((meshQuantum δ (n+2)/meshQuantum δ (n+1) : ℝ) : ℂ) • meshProjection G μ δ n v)
    (himage : meshProjection G μ δ n v * (meshContractionMatrix G μ n v *
      meshExtendMatrix G (meshProjection G μ δ (n+1)) v)=
      meshContractionMatrix G μ n v * meshExtendMatrix G (meshProjection G μ δ (n+1)) v) :
    (meshProjection G μ δ (n+2) v).conjTranspose=meshProjection G μ δ (n+2) v ∧
      meshProjection G μ δ (n+2) v * meshProjection G μ δ (n+2) v=
        meshProjection G μ δ (n+2) v ∧
      meshProjection G μ δ (n+2) v * meshExtendMatrix G (meshProjection G μ δ (n+1)) v=
        meshProjection G μ δ (n+2) v ∧
      meshContractionMatrix G μ n v * meshProjection G μ δ (n+2) v=0 ∧
      Matrix.trace (meshProjection G μ δ (n+2) v)=
        Matrix.trace (meshExtendMatrix G (meshProjection G μ δ (n+1)) v)-
          Matrix.trace (meshProjection G μ δ n v) := by
  let Q := meshExtendMatrix G (meshProjection G μ δ (n+1)) v
  let C := meshContractionMatrix G μ n v
  change Q.conjTranspose=Q at hQstar
  change Q*Q=Q at hQsq
  have hTQ : (C*Q)*Q=C*Q := by rw [Matrix.mul_assoc,hQsq]
  have hTT : (C*Q)*(C*Q).conjTranspose=
      ((meshQuantum δ (n+2)/meshQuantum δ (n+1) : ℝ) : ℂ) • meshProjection G μ δ n v := by
    rw [Matrix.conjTranspose_mul,hQstar,Matrix.mul_assoc,←Matrix.mul_assoc Q,hQsq,
      ←Matrix.mul_assoc]
    exact hscalar
  obtain ⟨hstar,hsq,hnest,hkill,htrace⟩ := mesh_projection_correction Q (C*Q)
    (meshProjection G μ δ n v) (meshQuantum δ (n+2)/meshQuantum δ (n+1))
    hden hQstar hQsq hTQ hTT himage
  rw [meshProjection_step]
  dsimp only
  refine ⟨hstar,hsq,hnest,?_,htrace⟩
  have hleft : Q*(Q-(((meshQuantum δ (n+2)/meshQuantum δ (n+1))⁻¹ : ℝ) : ℂ) •
      ((C*Q).conjTranspose*(C*Q)))=
      Q-(((meshQuantum δ (n+2)/meshQuantum δ (n+1))⁻¹ : ℝ) : ℂ) •
        ((C*Q).conjTranspose*(C*Q)) := by
    have h := congrArg Matrix.conjTranspose hnest
    rw [Matrix.conjTranspose_mul,hQstar,hstar] at h
    exact h
  change C*(Q-(((meshQuantum δ (n+2)/meshQuantum δ (n+1))⁻¹ : ℝ) : ℂ) •
    ((C*Q).conjTranspose*(C*Q)))=0
  rw [←hleft,←Matrix.mul_assoc]
  exact hkill

lemma meshProjection_extend_step (μ : V → ℝ) (δ : ℝ) (n : ℕ) (v : V)
    (hstar : ∀ w, (meshProjection G μ δ (n+1) w).conjTranspose=
      meshProjection G μ δ (n+1) w) :
    let R := meshExtendMatrix G (meshExtendMatrix G (meshProjection G μ δ (n+1))) v
    let D := meshExtendMatrix G (meshContractionMatrix G μ n) v
    meshExtendMatrix G (meshProjection G μ δ (n+2)) v =
      R-(((meshQuantum δ (n+2)/meshQuantum δ (n+1))⁻¹ : ℝ) : ℂ) •
        (R*D.conjTranspose*D*R) := by
  dsimp only
  have hRstar : (meshExtendMatrix G (meshExtendMatrix G
      (meshProjection G μ δ (n+1))) v).conjTranspose=
      meshExtendMatrix G (meshExtendMatrix G (meshProjection G μ δ (n+1))) v := by
    simp only [meshExtend_adjoint,hstar]
  rw [funext (meshProjection_step G μ δ n)]
  simp only [meshExtend_sub,meshExtend_smul,
    meshExtend_mul,←meshExtend_adjoint,Matrix.conjTranspose_mul]
  rw [hRstar]
  simp only [Matrix.mul_assoc]

lemma meshProjection_scalar_zero (μ : V → ℝ) (hμ : ∀ v, 0<μ v) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v) (v : V) :
    meshContractionMatrix G μ 0 v * meshExtendMatrix G (meshProjection G μ δ 1) v *
      (meshContractionMatrix G μ 0 v).conjTranspose =
      ((meshQuantum δ 2/meshQuantum δ 1 : ℝ) : ℂ) • meshProjection G μ δ 0 v := by
  have hPone : meshProjection G μ δ 1=fun v =>
      (1 : Matrix (MeshPaths G 1 v) (MeshPaths G 1 v) ℂ) :=
    funext (meshProjection_one G μ δ)
  have hq : meshQuantum δ 2/meshQuantum δ 1=δ := by norm_num [meshQuantum]
  rw [hq,meshProjection_zero,hPone,meshExtend_one,Matrix.mul_one]
  exact meshContraction_loop G μ hμ δ heigen 0 v

lemma meshProjection_scalar_succ (μ : V → ℝ) (hμ : ∀ v, 0<μ v) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v)
    (n : ℕ) (hq : meshQuantum δ (n+2)≠0)
    (hstar : ∀ w, (meshProjection G μ δ (n+1) w).conjTranspose=
      meshProjection G μ δ (n+1) w)
    (hsq : ∀ w, meshProjection G μ δ (n+1) w * meshProjection G μ δ (n+1) w=
      meshProjection G μ δ (n+1) w) (v : V) :
    meshContractionMatrix G μ (n+1) v *
      meshExtendMatrix G (meshProjection G μ δ (n+2)) v *
      (meshContractionMatrix G μ (n+1) v).conjTranspose =
      ((meshQuantum δ (n+3)/meshQuantum δ (n+2) : ℝ) : ℂ) •
        meshProjection G μ δ (n+1) v := by
  rw [meshProjection_extend_step G μ δ n v hstar]
  have h := mesh_scalar_step (meshContractionMatrix G μ (n+1) v)
    (meshExtendMatrix G (meshContractionMatrix G μ n) v)
    (meshProjection G μ δ (n+1) v)
    (meshExtendMatrix G (meshExtendMatrix G (meshProjection G μ δ (n+1))) v)
    (δ : ℂ) (((meshQuantum δ (n+2)/meshQuantum δ (n+1))⁻¹ : ℝ) : ℂ)
    (hsq v) (meshContraction_naturality G μ (meshProjection G μ δ (n+1)) v)
    (meshContraction_naturality_adjoint G μ (meshProjection G μ δ (n+1)) v)
    (meshContraction_loop G μ hμ δ heigen (n+1) v)
    (by simpa only [meshExtend_adjoint] using meshContraction_adjacent G μ hμ n v)
    (meshContraction_adjacent_right G μ hμ n v)
  rw [←Complex.ofReal_sub,meshQuantum_ratio_step δ n hq] at h
  exact h

end HarmonicArtin.ParabolicIntersections

end OAI
