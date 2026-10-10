import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshProjectionAlgebra
import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshPathSpaces

namespace OAI

/-! Positive weighted traces detect vanishing of all endpoint projections. -/
namespace HarmonicArtin.ParabolicIntersections
open scoped ComplexOrder
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} [Fintype V]

noncomputable def meshWeightedTrace {D : V → Type} [∀ v, Fintype (D v)]
    (μ : V → ℝ) (P : ∀ v, Matrix (D v) (D v) ℂ) : ℂ :=
  ∑ v, (μ v : ℂ)*Matrix.trace (P v)

lemma meshWeightedTrace_nonneg {D : V → Type} [∀ v, Fintype (D v)]
    (μ : V → ℝ) (hμ : ∀ v, 0≤μ v) (P : ∀ v, Matrix (D v) (D v) ℂ)
    (hstar : ∀ v, (P v).conjTranspose=P v) (hsq : ∀ v, P v*P v=P v) :
    0≤(meshWeightedTrace μ P).re := by
  simp only [meshWeightedTrace,Complex.re_sum,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact Finset.sum_nonneg (fun v _ => mul_nonneg (hμ v)
    (mesh_projection_trace (P v) (hstar v) (hsq v)).1)

/-- Strict positivity of the vertex weights turns a zero weighted trace
of orthogonal projections into the vanishing of each projection. -/
theorem meshWeightedTrace_zero {D : V → Type} [∀ v, Fintype (D v)]
    (μ : V → ℝ) (hμ : ∀ v, 0<μ v) (P : ∀ v, Matrix (D v) (D v) ℂ)
    (hstar : ∀ v, (P v).conjTranspose=P v) (hsq : ∀ v, P v*P v=P v)
    (hz : meshWeightedTrace μ P=0) : ∀ v, P v=0 := by
  have hpos : ∀ v, (P v).PosSemidef := by
    intro v
    have h := Matrix.posSemidef_conjTranspose_mul_self (P v)
    rwa [hstar v,hsq v] at h
  have ht : ∀ v, 0≤(Matrix.trace (P v)).re := fun v =>
    (Complex.nonneg_iff.mp (hpos v).trace_nonneg).1
  have hsum : (∑ v, μ v*(Matrix.trace (P v)).re)=0 := by
    have h := congrArg Complex.re hz
    simpa only [meshWeightedTrace,Complex.re_sum,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.zero_re] using h
  have heach := Finset.sum_eq_zero_iff_of_nonneg
    (fun v (_ : v∈Finset.univ) => mul_nonneg (hμ v).le (ht v))
  intro v
  have hv : μ v*(Matrix.trace (P v)).re=0 := heach.mp hsum v (Finset.mem_univ v)
  have hreal : (Matrix.trace (P v)).re=0 :=
    (mul_eq_zero.mp hv).resolve_left (ne_of_gt (hμ v))
  have himag : (Matrix.trace (P v)).im=0 :=
    (Complex.nonneg_iff.mp (hpos v).trace_nonneg).2.symm
  have htrace : Matrix.trace (P v)=0 := Complex.ext hreal himag
  exact (mesh_projection_trace (P v) (hstar v) (hsq v)).2.mp htrace

variable (G : SimpleGraph V)

lemma meshExtend_trace {n : ℕ}
    (P : ∀ v, Matrix (MeshPaths G n v) (MeshPaths G n v) ℂ) (v : V) :
    Matrix.trace (meshExtendMatrix G P v)=
      ∑ u : {u : V // G.Adj u v}, Matrix.trace (P u.val) := by
  exact Matrix.trace_blockDiagonal' _

/-- Reversal of an oriented edge exchanges the two endpoint sums. -/
def meshEdgeFlip : (Σ v : V, {u : V // G.Adj u v}) ≃
    (Σ v : V, {u : V // G.Adj u v}) where
  toFun p := ⟨p.2.val,⟨p.1,p.2.property.symm⟩⟩
  invFun p := ⟨p.2.val,⟨p.1,p.2.property.symm⟩⟩
  left_inv := by rintro ⟨v,⟨u,h⟩⟩; rfl
  right_inv := by rintro ⟨v,⟨u,h⟩⟩; rfl

/-- Extension multiplies the weighted trace by the Perron eigenvalue. -/
lemma meshWeightedTrace_extend (μ : V → ℝ) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v)
    {n : ℕ} (P : ∀ v, Matrix (MeshPaths G n v) (MeshPaths G n v) ℂ) :
    meshWeightedTrace μ (meshExtendMatrix G P)=
      (δ : ℂ)*meshWeightedTrace μ P := by
  unfold meshWeightedTrace
  simp_rw [meshExtend_trace]
  conv_lhs => simp only [Finset.mul_sum]
  rw [←Fintype.sum_sigma (fun p : Σ v : V, {u : V // G.Adj u v} =>
    (μ p.1 : ℂ)*Matrix.trace (P p.2.val))]
  calc
    (∑ p : Σ v : V, {u : V // G.Adj u v},
        (μ p.1 : ℂ)*Matrix.trace (P p.2.val)) =
      ∑ p : Σ v : V, {u : V // G.Adj u v},
        (μ p.2.val : ℂ)*Matrix.trace (P p.1) := by
          apply Fintype.sum_equiv (meshEdgeFlip G)
          intro p
          rfl
    _ = ∑ v, (∑ u : {u : V // G.Adj u v}, (μ u : ℂ))*Matrix.trace (P v) := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_mul]
    _ = (δ : ℂ)*∑ v, (μ v : ℂ)*Matrix.trace (P v) := by
      simp_rw [←Complex.ofReal_sum,heigen,Complex.ofReal_mul,mul_assoc]
      rw [Finset.mul_sum]

end HarmonicArtin.ParabolicIntersections

end OAI
