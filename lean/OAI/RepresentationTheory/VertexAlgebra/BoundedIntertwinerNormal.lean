import OAI.RepresentationTheory.VertexAlgebra.BoundedIntertwinerRepresentation
import OAI.RepresentationTheory.VertexAlgebra.BoundedWOTDensity

namespace OAI

noncomputable section
namespace StronglyRationalVOA.BoundedIntertwiner
open Filter Topology
universe u v w
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {ι : Type w}
variable (B : StarSubalgebra ℂ (H →L[ℂ] H)) (T : ι → H →L[ℂ] K)
  (hDense : DenseRange (core T))
  (hGram : ∀ (b : B) i j, Commute ((T i).adjoint.comp (T j)) (b : H →L[ℂ] H))

 

theorem representation_preserves_boundedWOT (F : Filter B) (b : B)
    (hbound : ∃ C : ℝ, ∀ᶠ a : B in F, ‖(a : H →L[ℂ] H)‖ ≤ C)
    (hweak : ∀ x y : H, Tendsto (fun a : B => inner ℂ x ((a : H →L[ℂ] H) y)) F
      (nhds (inner ℂ x ((b : H →L[ℂ] H) y)))) (x y : K) :
    Tendsto (fun a => inner ℂ x (representation B T hDense hGram a y)) F
      (nhds (inner ℂ x (representation B T hDense hGram b y))) := by
  apply tendsto_coeff_of_dense_of_eventual_bound (core T) hDense
  · obtain ⟨C, hC⟩ := hbound
    refine ⟨C, ?_⟩
    filter_upwards [hC] with a ha
    exact (representation_norm_le B T hDense hGram a).trans ha
  · intro u v
    classical
    have hexp (a : B) :
        inner ℂ (core T u) (representation B T hDense hGram a (core T v)) =
        ∑ i ∈ u.support, ∑ j ∈ v.support,
          inner ℂ ((T j).adjoint (T i (u i))) ((a : H →L[ℂ] H) (v j)) := by
      simp only [core_apply, map_sum, sum_inner, inner_sum, representation_intertwines]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact (ContinuousLinearMap.adjoint_inner_left (T j) _ _).symm
    simp_rw [hexp]
    exact tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ => hweak _ _))
end StronglyRationalVOA.BoundedIntertwiner

end

end OAI
