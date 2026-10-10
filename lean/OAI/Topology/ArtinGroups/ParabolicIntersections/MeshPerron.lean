import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshSpectralUpper

namespace OAI

/-! Nonnegative top eigenvectors, without a Perron--Frobenius axiom. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
open Matrix
variable {V : Type} [Fintype V]

lemma mesh_quadratic_abs_le (A : Matrix V V ℝ) (hA : ∀ i j, 0≤A i j)
    (x : V → ℝ) : x ⬝ᵥ (A *ᵥ x) ≤ (fun i => |x i|) ⬝ᵥ (A *ᵥ fun i => |x i|) := by
  simp only [dotProduct,mulVec,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h := mul_le_mul_of_nonneg_left (le_abs_self (x i*x j)) (hA i j)
  simpa only [abs_mul,mul_assoc,mul_left_comm,mul_comm] using h

lemma mesh_abs_top_eigenvector (A : Matrix V V ℝ) (hA : ∀ i j, 0≤A i j)
    (d : ℝ) (hupper : (d • (1 : Matrix V V ℝ)-A).PosSemidef)
    (x : V → ℝ) (heigen : A *ᵥ x=d • x) :
    A *ᵥ (fun i => |x i|)=d • (fun i => |x i|) := by
  let y : V → ℝ := fun i => |x i|
  have hsq : y ⬝ᵥ y=x ⬝ᵥ x := by
    simp only [dotProduct,y,←sq,sq_abs]
  have hq := mesh_quadratic_abs_le A hA x
  have hx : x ⬝ᵥ (A *ᵥ x)=d*(x ⬝ᵥ x) := by
    rw [heigen,dotProduct_smul,smul_eq_mul]
  have he : y ⬝ᵥ ((d • (1 : Matrix V V ℝ)-A) *ᵥ y)=d*(y ⬝ᵥ y)-y ⬝ᵥ (A *ᵥ y) := by
    rw [sub_mulVec,smul_mulVec,one_mulVec,dotProduct_sub,dotProduct_smul,smul_eq_mul]
  have hnonneg := hupper.dotProduct_mulVec_nonneg y
  simp only [star_trivial] at hnonneg
  have hz : y ⬝ᵥ ((d • (1 : Matrix V V ℝ)-A) *ᵥ y)=0 := by
    change x ⬝ᵥ (A *ᵥ x)≤y ⬝ᵥ (A *ᵥ y) at hq
    rw [he,hsq] at hnonneg ⊢
    linarith
  have hzero := hupper.dotProduct_mulVec_zero_iff.mp (by simpa only [star_trivial] using hz)
  rw [sub_mulVec,smul_mulVec,one_mulVec] at hzero
  exact (sub_eq_zero.mp hzero).symm

theorem mesh_nonnegative_top_eigenvector [Nonempty V] (A : Matrix V V ℝ)
    (hA : A.IsHermitian) (hpos : ∀ i j, 0≤A i j) :
    ∃ (d : ℝ) (y : V → ℝ), y≠0 ∧ (∀ i, 0≤y i) ∧ A *ᵥ y=d • y := by
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ hA.eigenvalues Finset.univ_nonempty
  let d := hA.eigenvalues j
  let x : V → ℝ := fun i => hA.eigenvectorBasis j i
  have hx : x≠0 := by
    exact (WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero j)
  have hupper : (d • (1 : Matrix V V ℝ)-A).PosSemidef :=
    mesh_spectral_upper hA d (fun i => hj i (Finset.mem_univ i))
  refine ⟨d,fun i => |x i|,?_,fun i => abs_nonneg _,?_⟩
  · intro hz
    apply hx
    funext i
    exact abs_eq_zero.mp (congrFun hz i)
  · exact mesh_abs_top_eigenvector A hpos d hupper x (hA.mulVec_eigenvectorBasis j)

end HarmonicArtin.ParabolicIntersections

end OAI
