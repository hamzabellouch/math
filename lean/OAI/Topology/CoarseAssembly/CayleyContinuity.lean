import OAI.Topology.CoarseAssembly.CayleyBoundary

namespace OAI

/-! # Norm continuity of the rational boundary representative -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A P : Type*} [CStarAlgebra A] [TopologicalSpace P]

theorem continuous_cayleyDenominator (F : P → A) (hF : ∀ p, IsSelfAdjoint (F p))
    (hcont : Continuous F) : Continuous (fun p => cayleyDenominator (F p) (hF p)) := by
  apply (Units.isOpenEmbedding_val (R := A)).isEmbedding.continuous_iff.mpr
  simp only [Function.comp_def, cayleyDenominator_val]
  convert! hcont.add (continuous_const : Continuous (fun _ : P => algebraMap ℂ A Complex.I))

theorem continuous_cayleyUnitary (F : P → A) (hF : ∀ p, IsSelfAdjoint (F p))
    (hcont : Continuous F) : Continuous (fun p => (cayleyUnitary (F p) (hF p) : A)) := by
  have hb := continuous_cayleyDenominator F hF hcont
  simp only [cayleyUnitary_val]
  exact (Units.continuous_val.comp hb).star.mul (Units.continuous_coe_inv.comp hb)

theorem continuous_rationalBoundaryUnitary (F : P → A) (hF : ∀ p, IsSelfAdjoint (F p))
    (hcont : Continuous F) :
    Continuous (fun p => (rationalBoundaryUnitary (F p) (hF p) : A)) := by
  have hc := continuous_cayleyUnitary F hF hcont
  simp only [rationalBoundaryUnitary, Unitary.coe_neg, Submonoid.coe_mul]
  convert! (hc.mul hc).neg

end CoarseAssembly.Analytic

end

end OAI
