import OAI.Topology.CoarseAssembly.CoefficientIsometry
import OAI.Topology.CoarseAssembly.LocallyCompactAlgebra

namespace OAI

/-! # The Roe algebra map induced by a coefficient isometry -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X E H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PseudoMetricSpace X] in
theorem coefficientConjugation_compactEntries (V : E →ₗᵢ[ℂ] H)
    {T : Operator X E} (hc : CompactEntries T) :
    CompactEntries (operatorConjugation (coefficientIsometry V) T) := by
  intro x y
  rw [coefficientConjugation_entry]
  exact ((hc x y).comp_clm V.toContinuousLinearMap.adjoint).clm_comp V.toContinuousLinearMap

theorem coefficientConjugation_generator (V : E →ₗᵢ[ℂ] H)
    {T : Operator X E} (hT : Generator T) :
    Generator (operatorConjugation (coefficientIsometry V) T) := by
  obtain ⟨⟨r, hr, hp⟩, hc, hcs⟩ := hT
  refine ⟨⟨r, hr, coefficientConjugation_propagation V hp⟩,
    coefficientConjugation_compactEntries V hc, ?_⟩
  rw [← operatorConjugation_star]
  exact coefficientConjugation_compactEntries V hcs

theorem coefficientConjugation_mem_roe (V : E →ₗᵢ[ℂ] H)
    {T : Operator X E} (hT : T ∈ algebra (X := X) (H := E)) :
    operatorConjugation (coefficientIsometry V) T ∈ algebra (X := X) (H := H) := by
  let φ := operatorConjugationHom (coefficientIsometry (X := X) V)
  let S := (algebra (X := X) (H := H)).comap φ
  have hcont : Continuous φ := by
    show Continuous (fun T : Operator X E =>
      (coefficientIsometry V).toContinuousLinearMap.comp
        (T.comp (coefficientIsometry V).toContinuousLinearMap.adjoint))
    exact continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  have hclosed : IsClosed (S : Set (Operator X E)) := algebra_isClosed.preimage hcont
  have hle : NonUnitalStarAlgebra.adjoin ℂ {T : Operator X E | Generator T} ≤ S := by
    apply NonUnitalStarAlgebra.adjoin_le
    intro T hT
    exact generator_mem (coefficientConjugation_generator V hT)
  exact (NonUnitalStarSubalgebra.topologicalClosure_minimal _ hle hclosed) hT

def coefficientRoeHom (V : E →ₗᵢ[ℂ] H) :
    algebra (X := X) (H := E) →⋆ₙₐ[ℂ] algebra (X := X) (H := H) :=
  NonUnitalStarAlgHom.codRestrict
    ((operatorConjugationHom (coefficientIsometry V)).comp
      (NonUnitalStarSubalgebraClass.subtype _)) _
    (fun T => coefficientConjugation_mem_roe V T.property)

end CoarseAssembly.DiscreteRoe

end

end OAI
