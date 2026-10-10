import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.RowCertificates

namespace OAI

/-! Three Row Density. -/

section

noncomputable section
open scoped Topology

namespace Saxl.ThreeRow

abbrev Parameters := Fin 13 → ℂ
abbrev Coordinates := Fin 12 → ℂ

def idx (k : Fin 4) (i : Fin 3) : Fin 13 := ⟨3*k.val+i.val, by omega⟩

def gram (z : Parameters) (i j : Fin 3) : ℂ :=
  z 12 * (z (idx 2 i) * z (idx 3 j) + z (idx 2 j) * z (idx 3 i)) -
    (z (idx 0 i) * z (idx 1 j) + z (idx 0 j) * z (idx 1 i))

def parameterMap (z : Parameters) : Coordinates :=
  ![gram z 0 0, gram z 0 1, gram z 0 2, gram z 1 1, gram z 1 2, gram z 2 2,
    z 6, z 7, z 8, z 9, z 10, z 11]

def basePoint : Parameters := ![1,0,0,0,1,0,0,0,1,0,0,1,1]

abbrev proj (i : Fin 13) : Parameters →L[ℂ] ℂ := ContinuousLinearMap.proj i

def gramDeriv (z : Parameters) (i j : Fin 3) : Parameters →L[ℂ] ℂ :=
  (z 12) •
    (z (idx 2 i) • proj (idx 3 j) + z (idx 3 j) • proj (idx 2 i) +
     (z (idx 2 j) • proj (idx 3 i) + z (idx 3 i) • proj (idx 2 j))) +
    (z (idx 2 i) * z (idx 3 j) + z (idx 2 j) * z (idx 3 i)) • proj 12 -
    (z (idx 0 i) • proj (idx 1 j) + z (idx 1 j) • proj (idx 0 i) +
     (z (idx 0 j) • proj (idx 1 i) + z (idx 1 i) • proj (idx 0 j)))

lemma gram_hasStrictFDerivAt (z : Parameters) (i j : Fin 3) :
    HasStrictFDerivAt (fun z => gram z i j) (gramDeriv z i j) z := by
  have h (k : Fin 13) := hasStrictFDerivAt_apply (𝕜 := ℂ) k z
  exact ((h 12).mul (((h (idx 2 i)).mul (h (idx 3 j))).add
    ((h (idx 2 j)).mul (h (idx 3 i))))).sub
      (((h (idx 0 i)).mul (h (idx 1 j))).add ((h (idx 0 j)).mul (h (idx 1 i))))

def parameterDeriv (z : Parameters) : Parameters →L[ℂ] Coordinates :=
  ContinuousLinearMap.pi
    ![gramDeriv z 0 0, gramDeriv z 0 1, gramDeriv z 0 2, gramDeriv z 1 1,
      gramDeriv z 1 2, gramDeriv z 2 2, proj 6, proj 7, proj 8, proj 9, proj 10, proj 11]

lemma parameterMap_hasStrictFDerivAt (z : Parameters) :
    HasStrictFDerivAt parameterMap (parameterDeriv z) z := by
  apply hasStrictFDerivAt_pi.mpr
  intro i
  fin_cases i
  all_goals first
    | exact gram_hasStrictFDerivAt z 0 0
    | exact gram_hasStrictFDerivAt z 0 1
    | exact gram_hasStrictFDerivAt z 0 2
    | exact gram_hasStrictFDerivAt z 1 1
    | exact gram_hasStrictFDerivAt z 1 2
    | exact gram_hasStrictFDerivAt z 2 2
    | exact hasStrictFDerivAt_apply (𝕜 := ℂ) _ z

def differentialLift (w : Coordinates) : Parameters :=
  ![-w 1, -w 3/2, w 7+w 10-w 4, -w 0/2, 0, w 6+w 9-w 2,
    w 6, w 7, w 8, w 9, w 10, w 11, w 5/2-w 8-w 11]

lemma differential_lift (w : Coordinates) :
    parameterDeriv basePoint (differentialLift w) = w := by
  funext i
  fin_cases i <;>
    norm_num [parameterDeriv, gramDeriv, basePoint, differentialLift,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, proj, idx, Matrix.cons_val]
  ring

lemma parameterDeriv_surjective : Function.Surjective (parameterDeriv basePoint) :=
  fun w => ⟨differentialLift w, differential_lift w⟩

theorem joint_density (F : Coordinates → ℂ)
    (hF : AnalyticOnNhd ℂ F Set.univ)
    (hzero : ∀ z : Parameters, z 12 ≠ 0 → F (parameterMap z) = 0) :
    ∀ w, F w = 0 := by
  have hopen := (parameterMap_hasStrictFDerivAt basePoint).map_nhds_eq_of_surj
    (LinearMap.range_eq_top.mpr parameterDeriv_surjective)
  have ht : ∀ᶠ z : Parameters in 𝓝 basePoint, z 12 ≠ 0 := by
    apply (isOpen_ne_fun (continuous_apply 12) continuous_const).mem_nhds
    change (1 : ℂ) ≠ 0
    exact one_ne_zero
  have hz : ∀ᶠ w in 𝓝 (parameterMap basePoint), F w = 0 := by
    rw [← hopen, Filter.eventually_map]
    exact ht.mono hzero
  have heq := hF.eq_of_eventuallyEq
    (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : Coordinates => (0 : ℂ)) Set.univ) hz
  intro w
  exact congrFun heq w

end Saxl.ThreeRow
end
end

end OAI
