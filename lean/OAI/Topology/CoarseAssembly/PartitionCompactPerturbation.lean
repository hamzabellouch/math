import OAI.Topology.CoarseAssembly.RipsLocalization
import OAI.Topology.CoarseAssembly.AmpleRipsFamily

namespace OAI

/-! # Compact perturbations through the actual localization operators -/

noncomputable section

namespace CoarseAssembly

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isometricExtension_sub (V : E →ₗᵢ[ℂ] H) (F G : E →L[ℂ] E) :
    isometricExtension V F - isometricExtension V G = operatorConjugation V (F - G) := by
  unfold isometricExtension
  change (1 + operatorConjugationHom V (F - 1)) -
    (1 + operatorConjugationHom V (G - 1)) = operatorConjugationHom V (F - G)
  have he : (F - 1) - (G - 1) = F - G := by abel
  calc
    _ = operatorConjugationHom V (F - 1) - operatorConjugationHom V (G - 1) := by abel
    _ = operatorConjugationHom V ((F - 1) - (G - 1)) := (map_sub _ _ _).symm
    _ = _ := by rw [he]

theorem isometricExtension_sub_compact (V : E →ₗᵢ[ℂ] H) (F G : E →L[ℂ] E)
    (hFG : IsCompactOperator (F - G)) :
    IsCompactOperator (isometricExtension V F - isometricExtension V G) := by
  rw [isometricExtension_sub]
  exact (hFG.comp_clm V.toContinuousLinearMap.adjoint).clm_comp V.toContinuousLinearMap

namespace DiscreteRoe

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem partitionCompression_sub (a : X → H →L[ℂ] H) (F G : H →L[ℂ] H) :
    partitionCompression a F - partitionCompression a G = partitionCompression a (F - G) := by
  rw [partitionCompression_eq_sum, partitionCompression_eq_sum,
    partitionCompression_eq_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]

theorem partitionCompression_sub_compact (a : X → H →L[ℂ] H) (F G : H →L[ℂ] H)
    (hFG : IsCompactOperator (F - G)) :
    IsCompactOperator (partitionCompression a F - partitionCompression a G) := by
  rw [partitionCompression_sub, partitionCompression_eq_sum]
  exact (compactOperator (RingHom.id ℂ) H H).sum_mem
    (fun x _ => (hFG.comp_clm (a x)).clm_comp (a x).adjoint)

theorem localizedSpatialOperator_sub_compact (a : X → H →L[ℂ] H)
    (hpart : ∑ x, (a x).adjoint.comp (a x) = 1) (F G : H →L[ℂ] H)
    (hFG : IsCompactOperator (F - G)) :
    IsCompactOperator (localizedSpatialOperator a hpart F - localizedSpatialOperator a hpart G) :=
  isometricExtension_sub_compact _ _ _ (partitionCompression_sub_compact a F G hFG)

end DiscreteRoe

namespace Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X]

theorem ripsSpatialOperator_compactPerturb (r : ℝ) (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (K : End c.space)
    (hK : IsCompactOperator K) (hKs : IsCompactOperator (star K : End c.space)) :
    IsCompactOperator
      ((show Operator X c.space from ripsSpatialOperator r (c.compactPerturb K hK hKs) hπ) -
        ripsSpatialOperator r c hπ) := by
  change IsCompactOperator
    (localizedSpatialOperator (representedSqrt r c) (representedSqrt_partition r c hπ)
      (c.operator + K) -
    localizedSpatialOperator (representedSqrt r c) (representedSqrt_partition r c hπ) c.operator)
  apply localizedSpatialOperator_sub_compact
  simpa only [add_sub_cancel_left] using hK

theorem ampleRipsOperator_compactPerturb (r : ℝ) (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (K : End c.space)
    (hK : IsCompactOperator K) (hKs : IsCompactOperator (star K : End c.space)) :
    IsCompactOperator
      (ampleRipsOperator r (c.compactPerturb K hK hKs) hπ - ampleRipsOperator r c hπ) := by
  change IsCompactOperator
    (isometricExtension (coefficientIsometry (ampleIsometry c.space))
      (ripsSpatialOperator r (c.compactPerturb K hK hKs) hπ) -
    isometricExtension (coefficientIsometry (ampleIsometry c.space)) (ripsSpatialOperator r c hπ))
  exact isometricExtension_sub_compact _ _ _ (ripsSpatialOperator_compactPerturb r c hπ K hK hKs)

end Rips

end CoarseAssembly

end

end OAI
