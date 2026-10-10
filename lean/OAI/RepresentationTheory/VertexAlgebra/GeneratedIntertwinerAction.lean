import OAI.RepresentationTheory.VertexAlgebra.Foundations
import OAI.RepresentationTheory.VertexAlgebra.BoundedIntertwinerNormal

namespace OAI

noncomputable section
namespace StronglyRationalVOA.BoundedIntertwiner
universe u v w z
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {ι : Type w} {γ : Type z}
variable (X : γ → H →L[ℂ] H) (Y : γ → K →L[ℂ] K) (rev : γ → γ)
  (hX : ∀ g, star (X g) = X (rev g)) (hY : ∀ g, star (Y g) = Y (rev g))
  (T : ι → H →L[ℂ] K) (hi : ∀ g i, (Y g).comp (T i) = (T i).comp (X g))
include hX hY hi

theorem adjoint_intertwines (g : γ) (i : ι) :
    (T i).adjoint.comp (Y g) = (X g).comp (T i).adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint (hi (rev g) i)
  rw [← hX g, ← hY g] at h
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_adjoint] using h

theorem gram_commutes_generator (g : γ) (i j : ι) :
    Commute ((T i).adjoint.comp (T j)) (X g) := by
  change ((T i).adjoint.comp (T j)).comp (X g) =
    (X g).comp ((T i).adjoint.comp (T j))
  rw [ContinuousLinearMap.comp_assoc, ← hi g j,
    ← ContinuousLinearMap.comp_assoc, adjoint_intertwines X Y rev hX hY T hi]
  exact ContinuousLinearMap.comp_assoc _ _ _

theorem gram_commutes_generated
    (b : (LocalOperatorAlgebra.generated (Set.range X)).toStarSubalgebra) (i j : ι) :
    Commute ((T i).adjoint.comp (T j)) (b : H →L[ℂ] H) := by
  have hg : (T i).adjoint.comp (T j) ∈ StarSubalgebra.centralizer ℂ (Set.range X) := by
    rw [StarSubalgebra.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    refine ⟨(gram_commutes_generator X Y rev hX hY T hi g i j).eq.symm, ?_⟩
    rw [hX]
    exact (gram_commutes_generator X Y rev hX hY T hi (rev g) i j).eq.symm
  have hb := b.property
  change (b : H →L[ℂ] H) ∈ StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (Set.range X) : Set (H →L[ℂ] H)) at hb
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp hb _ hg).1

variable (hDense : DenseRange (core T))

def generatedRepresentation :
    (LocalOperatorAlgebra.generated (Set.range X)).toStarSubalgebra →⋆ₐ[ℂ] (K →L[ℂ] K) :=
  representation _ T hDense (gram_commutes_generated X Y rev hX hY T hi)

theorem generatedRepresentation_generator (g : γ) :
    generatedRepresentation X Y rev hX hY T hi hDense
      ⟨X g, LocalOperatorAlgebra.subset_generated _ (Set.mem_range_self g)⟩ = Y g := by
  apply ext_of_total T hDense
  intro i x
  rw [generatedRepresentation, representation_intertwines]
  exact congrArg (fun D : H →L[ℂ] K => D x) (hi g i).symm
end StronglyRationalVOA.BoundedIntertwiner

end

end OAI
