import OAI.Topology.CoarseAssembly.LocalizationNormContinuity

namespace OAI

/-! # Norm continuity for representation-varying finite localization -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {T X H : Type*} [TopologicalSpace T] [Fintype X] [DecidableEq X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem continuous_partitionMap (a : T → X → H →L[ℂ] H)
    (ha : ∀ x, Continuous (fun t => a t x)) :
    Continuous (fun t => partitionMap (a t)) := by
  unfold partitionMap
  apply continuous_finsetSum
  intro x _
  exact continuous_const.clm_comp (ha x)

theorem continuous_partitionCompression (a : T → X → H →L[ℂ] H)
    (ha : ∀ x, Continuous (fun t => a t x)) (F : T → H →L[ℂ] H)
    (hF : Continuous F) : Continuous (fun t => partitionCompression (a t) (F t)) := by
  simp only [partitionCompression_eq_sum]
  apply continuous_finsetSum
  intro x _
  exact (ContinuousLinearMap.adjoint.continuous.comp (ha x)).clm_comp
    (hF.clm_comp (ha x))

theorem continuous_localizedSpatialOperator (a : T → X → H →L[ℂ] H)
    (ha : ∀ x, Continuous (fun t => a t x))
    (hp : ∀ t, ∑ x, (a t x).adjoint.comp (a t x) = 1)
    (F : T → H →L[ℂ] H) (hF : Continuous F) :
    Continuous (fun t => localizedSpatialOperator (a t) (hp t) (F t)) := by
  simp only [localizedSpatialOperator_eq, partitionConjugate]
  have hP := continuous_partitionMap a ha
  have hC := continuous_partitionCompression a ha F hF
  have hPa := ContinuousLinearMap.adjoint.continuous.comp hP
  exact (continuous_const.add (hP.clm_comp (hC.clm_comp hPa))).sub
    (hP.clm_comp (continuous_const.clm_comp hPa))

end CoarseAssembly.DiscreteRoe

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X]

theorem continuous_ripsSpatialOperator (r : ℝ) (h : OddHomotopy C(Point X r, ℂ))
    (hπ : ∀ t, (h.eval t).representation 1 = 1) :
    Continuous (fun t => (show Operator X h.space from ripsSpatialOperator r (h.eval t) (hπ t))) := by
  exact continuous_localizedSpatialOperator
    (fun t => (show X → End h.space from representedSqrt r (h.eval t)))
    (fun x => h.continuous_representation (sqrtCoordinate r x))
    (fun t => representedSqrt_partition r (h.eval t) (hπ t))
    h.operator h.continuous_operator

theorem continuous_ampleRipsOperator (r : ℝ) (h : OddHomotopy C(Point X r, ℂ))
    (hπ : ∀ t, (h.eval t).representation 1 = 1) :
    Continuous (fun t => ampleRipsOperator r (h.eval t) (hπ t)) := by
  have hR := continuous_ripsSpatialOperator r h hπ
  change Continuous (fun t => 1 +
    (coefficientIsometry (X := X) (ampleIsometry h.space)).toContinuousLinearMap.comp
      (((show Operator X h.space from ripsSpatialOperator r (h.eval t) (hπ t)) - 1).comp
        (coefficientIsometry (X := X) (ampleIsometry h.space)).toContinuousLinearMap.adjoint))
  exact continuous_const.add (continuous_const.clm_comp
    ((hR.sub continuous_const).clm_comp continuous_const))

end CoarseAssembly.Rips

end

end OAI
