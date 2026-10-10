import OAI.Topology.CoarseAssembly.SigmaCycleRestriction
import OAI.Topology.CoarseAssembly.UniformCycleNormalization

namespace OAI

/-! # The circle-family class without a countable-additivity assumption -/

noncomputable section

namespace CoarseAssembly

open Analytic
open scoped ZeroAtInfty

def windingCircleCycle : OddCycle C(WindingCircle, ℂ) :=
  negativeCircleCycle.precomp
    (ContinuousMap.compStarAlgHom' ℂ ℂ
      ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm :
        C(Circle, WindingCircle))).toNonUnitalStarAlgHom

theorem windingCircleCycle_class :
    cycleClass C₀(WindingCircle, ℂ) (windingCircleCycle.precomp compactFunctionForget) =
      circleFundamental := by
  unfold circleFundamental negativeCircleClass pushforward windingCircleCycle
  rw [precomp_cycleClass, OddCycle.precomp_comp, OddCycle.precomp_comp]
  congr 2

theorem windingCircleCycle_norm : ‖windingCircleCycle.operator‖ ≤ 1 :=
  involution_norm_le_one _ negativeCircleOperator_selfAdjoint negativeCircleOperator_sq

def circleSigmaCycle : OddCycle C₀(Sigma CircleFamily, ℂ) :=
  sigmaCycle CircleFamily (fun _ => windingCircleCycle) 1 (by norm_num)
    (fun _ => windingCircleCycle_norm) (fun _ => negativeCircleOperator_selfAdjoint)
    (fun _ => negativeCircleOperator_sq)

/-- The particular product class needed by the counterexample is an actual cycle. -/
def explicitCircleFamily : LocallyFiniteK1 (Sigma CircleFamily) :=
  cycleClass C₀(Sigma CircleFamily, ℂ) circleSigmaCycle

theorem explicitCircleFamily_coordinate (j : ℕ) :
    restrictComponent (sigmaComponent CircleFamily j) (sigmaComponent_open CircleFamily j)
      explicitCircleFamily = circleFundamental := by
  exact (sigmaCycle_coordinate CircleFamily (fun _ => windingCircleCycle) 1 (by norm_num)
    (fun _ => windingCircleCycle_norm) (fun _ => negativeCircleOperator_selfAdjoint)
    (fun _ => negativeCircleOperator_sq) j).trans windingCircleCycle_class

end CoarseAssembly

end

end OAI
