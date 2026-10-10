import OAI.RepresentationTheory.VertexAlgebra.BoundedIntertwinerNorm

namespace OAI

noncomputable section
namespace StronglyRationalVOA.BoundedIntertwiner
universe u v w
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {ι : Type w} [Fintype ι]

abbrev SumSpace (ι : Type w) (H : Type u) := PiLp 2 (fun _ : ι => H)

def row (T : ι → H →L[ℂ] K) : SumSpace ι H →L[ℂ] K :=
  ∑ i, (T i).comp (PiLp.proj 2 (fun _ : ι => H) i)
omit [CompleteSpace H] [CompleteSpace K] in
@[simp] theorem row_apply (T : ι → H →L[ℂ] K) (x : SumSpace ι H) :
    row T x = ∑ i, T i (x i) := by simp [row]

def column (T : ι → H →L[ℂ] K) : K →L[ℂ] SumSpace ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (T i).adjoint))
omit [Fintype ι] in
@[simp] theorem column_apply (T : ι → H →L[ℂ] K) (x : K) (i : ι) :
    column T x i = (T i).adjoint x := rfl

theorem row_adjoint (T : ι → H →L[ℂ] K) : (row T).adjoint = column T := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply, column_apply, row_apply, inner_sum]
  exact Finset.sum_congr rfl (fun i _ => ContinuousLinearMap.adjoint_inner_left (T i) (y i) x)

def diagonal (D : H →L[ℂ] H) : SumSpace ι H →L[ℂ] SumSpace ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => D.comp (PiLp.proj 2 (fun _ : ι => H) i)))
omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem diagonal_apply (D : H →L[ℂ] H) (x : SumSpace ι H) (i : ι) :
    diagonal D x i = D (x i) := rfl

omit [CompleteSpace H] in
theorem norm_diagonal_le (D : H →L[ℂ] H) : ‖diagonal (ι := ι) D‖ ≤ ‖D‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => by
    simpa only [diagonal_apply, mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (D.le_opNorm (x i)) 2)

 
theorem norm_sum_le (T : ι → H →L[ℂ] K) (D : H →L[ℂ] H)
    (h : ∀ i j, Commute ((T i).adjoint.comp (T j)) D) (x : ι → H) :
    ‖∑ i, T i (D (x i))‖ ≤ ‖D‖ * ‖∑ i, T i (x i)‖ := by
  have hc : Commute ((row T).adjoint.comp (row T)) (diagonal D) := by
    rw [row_adjoint]
    change _ * _ = _ * _
    ext y i
    simp only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply,
      column_apply, diagonal_apply]
    simp only [row_apply, diagonal_apply, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun F : H →L[ℂ] H => F (y j)) (h i j).eq
  let y : SumSpace ι H := WithLp.toLp 2 x
  have hn := norm_map_le_of_gram_commutes (row T) (diagonal D) hc y
  have hd := norm_diagonal_le (ι := ι) D
  have hn' := hn.trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
  simpa only [row_apply, diagonal_apply, y, PiLp.toLp_apply] using hn'
end StronglyRationalVOA.BoundedIntertwiner

end

end OAI
