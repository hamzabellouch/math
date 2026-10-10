import OAI.RepresentationTheory.VertexAlgebra.NormalUniqueness
import OAI.RepresentationTheory.VertexAlgebra.SelfAdjointHomExt

namespace OAI

noncomputable section
namespace StronglyRationalVOA.LocalOperatorAlgebra
open BicommutantDensity
universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

 

theorem normal_ext_generated (s : Set (H →L[ℂ] H))
    (π ρ : (generated s).toStarSubalgebra →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hπ : IsNormal (generated s) π) (hρ : IsNormal (generated s) ρ)
    (he : ∀ (x : H →L[ℂ] H) (hx : x ∈ s),
      π ⟨x, subset_generated s hx⟩ = ρ ⟨x, subset_generated s hx⟩) : π = ρ := by
  let N := generated s
  let B := (StarAlgebra.adjoin ℂ s).topologicalClosure
  let : IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := vonNeumann_isClosed N
  let : IsClosed (B : Set (H →L[ℂ] H)) := StarSubalgebra.isClosed_topologicalClosure _
  have hB : B ≤ N.toStarSubalgebra :=
    StarSubalgebra.topologicalClosure_adjoin_le_centralizer_centralizer ℂ s
  have hgen : N.toStarSubalgebra ≤ Bicommutant B := by
    apply generated_mono
    intro x hx
    exact StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ s hx)
  have hcπ : Continuous π :=
    AddMonoidHomClass.continuous_of_bound π 1 (fun a => by
      simpa only [one_mul, coe_nnnorm] using (NNReal.coe_le_coe.mpr (NonUnitalStarAlgHom.nnnorm_apply_le π a)))
  have hcρ : Continuous ρ :=
    AddMonoidHomClass.continuous_of_bound ρ 1 (fun a => by
      simpa only [one_mul, coe_nnnorm] using (NNReal.coe_le_coe.mpr (NonUnitalStarAlgHom.nnnorm_apply_le ρ a)))
  let E : StarSubalgebra ℂ (H →L[ℂ] H) := (StarAlgHom.equalizer π ρ).map N.toStarSubalgebra.subtype
  have hE : IsClosed (E : Set (H →L[ℂ] H)) := by
    change IsClosed (Subtype.val '' {a : N.toStarSubalgebra | π a = ρ a})
    exact ((vonNeumann_isClosed N).isClosedMap_subtype_val) _ (isClosed_eq hcπ hcρ)
  have hBE : B ≤ E := by
    apply StarSubalgebra.topologicalClosure_minimal _ hE
    apply StarAlgebra.adjoin_le
    intro x hx
    refine ⟨⟨x,subset_generated s hx⟩, ?_, rfl⟩
    exact he x hx
  have heB (b : B) : π ⟨b.val,hB b.property⟩ = ρ ⟨b.val,hB b.property⟩ := by
    obtain ⟨d,hd,heq⟩ := hBE b.property
    have hd' : π d = ρ d := hd
    have hde : d = ⟨b.val,hB b.property⟩ := Subtype.ext heq
    simpa only [hde] using hd'
  apply starAlgHom_ext_selfAdjoint
  intro D hD
  exact normal_eq_selfAdjoint N B hB hgen π ρ hπ hρ heB D
    (hD.map N.toStarSubalgebra.subtype)
end StronglyRationalVOA.LocalOperatorAlgebra

end

end OAI
