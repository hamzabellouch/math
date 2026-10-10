import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshProjection

namespace OAI

/-! The Jones--Wenzl induction before the first nonpositive quantum integer. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} [Fintype V] (G : SimpleGraph V)

structure MeshProjectionStage (μ : V → ℝ) (δ : ℝ) (n : ℕ) : Prop where
  lower_star : ∀ v, (meshProjection G μ δ n v).conjTranspose=meshProjection G μ δ n v
  lower_square : ∀ v, meshProjection G μ δ n v*meshProjection G μ δ n v=meshProjection G μ δ n v
  upper_star : ∀ v, (meshProjection G μ δ (n+1) v).conjTranspose=meshProjection G μ δ (n+1) v
  upper_square : ∀ v, meshProjection G μ δ (n+1) v*meshProjection G μ δ (n+1) v=
    meshProjection G μ δ (n+1) v
  nested : ∀ v, meshProjection G μ δ (n+1) v*meshExtendMatrix G (meshProjection G μ δ n) v=
    meshProjection G μ δ (n+1) v
  scalar : ∀ v, meshContractionMatrix G μ n v *
    meshExtendMatrix G (meshProjection G μ δ (n+1)) v *
    (meshContractionMatrix G μ n v).conjTranspose =
    ((meshQuantum δ (n+2)/meshQuantum δ (n+1) : ℝ) : ℂ) • meshProjection G μ δ n v
  trace_recurrence : n≠0 → ∀ v, Matrix.trace (meshProjection G μ δ (n+1) v)=
    Matrix.trace (meshExtendMatrix G (meshProjection G μ δ n) v)-
      Matrix.trace (meshProjection G μ δ (n-1) v)

theorem meshProjectionStage_zero (μ : V → ℝ) (hμ : ∀ v, 0<μ v) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v) :
    MeshProjectionStage G μ δ 0 where
  lower_star v := by simp only [meshProjection_zero,Matrix.conjTranspose_one]
  lower_square v := by simp only [meshProjection_zero,Matrix.one_mul]
  upper_star v := by
    change (1 : Matrix (MeshPaths G 1 v) (MeshPaths G 1 v) ℂ).conjTranspose=1
    exact Matrix.conjTranspose_one
  upper_square v := by
    change (1 : Matrix (MeshPaths G 1 v) (MeshPaths G 1 v) ℂ)*1=1
    exact Matrix.one_mul 1
  nested v := by
    rw [funext (meshProjection_zero G μ δ),meshExtend_one]
    exact Matrix.mul_one _
  scalar := meshProjection_scalar_zero G μ hμ δ heigen
  trace_recurrence hn := (hn rfl).elim

theorem meshProjectionStage_succ (μ : V → ℝ) (hμ : ∀ v, 0<μ v) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v)
    (n : ℕ) (h : MeshProjectionStage G μ δ n)
    (hq₁ : meshQuantum δ (n+1)≠0) (hq₂ : meshQuantum δ (n+2)≠0) :
    MeshProjectionStage G μ δ (n+1) := by
  have hQstar (v : V) :
      (meshExtendMatrix G (meshProjection G μ δ (n+1)) v).conjTranspose=
        meshExtendMatrix G (meshProjection G μ δ (n+1)) v := by
    simp only [meshExtend_adjoint,h.upper_star]
  have hQsq (v : V) : meshExtendMatrix G (meshProjection G μ δ (n+1)) v *
      meshExtendMatrix G (meshProjection G μ δ (n+1)) v=
        meshExtendMatrix G (meshProjection G μ δ (n+1)) v := by
    rw [←meshExtend_mul]
    simp only [h.upper_square]
  have himage (v : V) : meshProjection G μ δ n v *
      (meshContractionMatrix G μ n v * meshExtendMatrix G (meshProjection G μ δ (n+1)) v)=
      meshContractionMatrix G μ n v * meshExtendMatrix G (meshProjection G μ δ (n+1)) v := by
    let R := meshExtendMatrix G (meshExtendMatrix G (meshProjection G μ δ n)) v
    let Q := meshExtendMatrix G (meshProjection G μ δ (n+1)) v
    let C := meshContractionMatrix G μ n v
    have hRstar : R.conjTranspose=R := by simp only [R,meshExtend_adjoint,h.lower_star]
    have hQR : Q*R=Q := by
      dsimp only [Q,R]
      rw [←meshExtend_mul]
      simp only [h.nested]
    have hRQ : R*Q=Q := by
      have hh := congrArg Matrix.conjTranspose hQR
      rw [Matrix.conjTranspose_mul,hRstar,hQstar] at hh
      exact hh
    have hCR : C*R=meshProjection G μ δ n v*C :=
      meshContraction_naturality G μ (meshProjection G μ δ n) v
    change meshProjection G μ δ n v*(C*Q)=C*Q
    rw [←Matrix.mul_assoc,←hCR,Matrix.mul_assoc,hRQ]
  have hnew (v : V) := meshProjection_correct G μ δ n v
    (div_ne_zero hq₂ hq₁) (hQstar v) (hQsq v) (h.scalar v) (himage v)
  exact {
    lower_star := h.upper_star
    lower_square := h.upper_square
    upper_star := fun v => (hnew v).1
    upper_square := fun v => (hnew v).2.1
    nested := fun v => (hnew v).2.2.1
    scalar := meshProjection_scalar_succ G μ hμ δ heigen n hq₂ h.upper_star h.upper_square
    trace_recurrence := fun _ v => by
      rw [show n+1-1=n by omega]
      exact (hnew v).2.2.2.2 }

/-- Every stage strictly before the quantum cutoff is an actual
orthogonal projection, with the required nesting and scalar identity. -/
theorem meshProjectionStage_before_cutoff (μ : V → ℝ) (hμ : ∀ v, 0<μ v) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v)
    (H : ℕ) (hpos : ∀ n, 0 < n → n < H → 0 < meshQuantum δ n) :
    ∀ n, n+1<H → MeshProjectionStage G μ δ n := by
  intro n
  induction n with
  | zero => intro _; exact meshProjectionStage_zero G μ hμ δ heigen
  | succ n ih =>
    intro hn
    apply meshProjectionStage_succ G μ hμ δ heigen n (ih (by omega))
    · exact ne_of_gt (hpos (n+1) (by omega) (by omega))
    · exact ne_of_gt (hpos (n+2) (by omega) (by omega))

end HarmonicArtin.ParabolicIntersections

end OAI
