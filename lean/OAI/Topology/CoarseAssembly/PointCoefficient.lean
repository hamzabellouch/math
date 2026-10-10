import OAI.Topology.CoarseAssembly.SupportedNormalization
import OAI.Topology.CoarseAssembly.CompactHomotopy

namespace OAI

/-! # The odd analytic coefficient group of a point

All scalar Fredholm cycles vanish by explicit operator normalization. The
constant-function and evaluation maps identify the point coefficient algebra
with the scalars, so its odd group vanishes as well.
-/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped ZeroAtInfty

def pointConstants : ℂ →⋆ₙₐ[ℂ] C₀(Unit, ℂ) where
  toFun z := compactFunctionLift (ContinuousMap.const Unit z)
  map_zero' := by ext x; rfl
  map_add' _ _ := by ext x; rfl
  map_mul' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl
  map_star' _ := by ext x; rfl

def pointEvaluation : C₀(Unit, ℂ) →⋆ₙₐ[ℂ] ℂ where
  toFun a := a ()
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

theorem pointConstants_evaluation : pointConstants.comp pointEvaluation =
    NonUnitalStarAlgHom.id ℂ C₀(Unit, ℂ) := by
  ext a x
  cases x
  rfl

theorem point_cycleClass_zero (c : OddCycle C₀(Unit, ℂ)) :
    cycleClass C₀(Unit, ℂ) c = 0 := by
  have h := congrArg (precomp pointEvaluation) (scalar_cycleClass_zero (c.precomp pointConstants))
  simpa only [precomp_cycleClass, map_zero, OddCycle.precomp_comp,
    pointConstants_evaluation, OddCycle.precomp_id] using h

theorem subsingleton_of_cycleClass_zero {A : Type} [NonUnitalCStarAlgebra A]
    (hzero : ∀ c : OddCycle A, cycleClass A c = 0) : Subsingleton (OddK A) := by
  have h : AddMonoidHom.id (OddK A) = 0 := by
    apply hom_ext
    intro c
    exact hzero c
  refine ⟨fun x y => ?_⟩
  have hx : x = 0 := DFunLike.congr_fun h x
  have hy : y = 0 := DFunLike.congr_fun h y
  exact hx.trans hy.symm

theorem point_odd_zero : Subsingleton (LocallyFiniteK1 Unit) :=
  subsingleton_of_cycleClass_zero point_cycleClass_zero

end CoarseAssembly.Analytic

end

end OAI
