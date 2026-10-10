import OAI.Topology.CoarseAssembly.CocyclePathLifting
import Mathlib.Topology.Instances.AddCircle.Real

namespace OAI

/-! # Parametrizing a closed path by the circle

The interval endpoints are identified using Mathlib's quotient-circle
construction. The resulting continuous map agrees with the path on the
entire closed interval, including its identified endpoint.
-/

noncomputable section

namespace CoarseAssembly

open unitInterval

abbrev WindingCircle := AddCircle (1 : ℝ)

variable {Y : Type*} [TopologicalSpace Y] {y : Y}

theorem circle_parameter_surjective : Function.Surjective
    (fun t : unitInterval => ((t : ℝ) : WindingCircle)) := by
  intro z
  have hz : z ∈ (Set.univ : Set WindingCircle) := Set.mem_univ _
  rw [← AddCircle.coe_image_Icc_eq (1 : ℝ) 0] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  exact ⟨⟨t, by simpa using ht⟩, rfl⟩

def loopCircle (γ : Path y y) : C(WindingCircle, Y) where
  toFun := AddCircle.liftIco 1 0 γ.extend
  continuous_toFun := AddCircle.liftIco_zero_continuous (by simp)
    γ.continuous_extend.continuousOn

theorem loopCircle_apply_lt (γ : Path y y) (t : unitInterval) (ht : (t : ℝ) < 1) :
    loopCircle γ (t : ℝ) = γ t := by
  change AddCircle.liftIco 1 0 γ.extend (t : ℝ) = γ t
  rw [AddCircle.liftIco_zero_coe_apply ⟨t.2.1, ht⟩, Path.extend_apply]

theorem loopCircle_apply (γ : Path y y) (t : unitInterval) :
    loopCircle γ (t : ℝ) = γ t := by
  rcases lt_or_eq_of_le t.2.2 with ht | ht
  · exact loopCircle_apply_lt γ t ht
  · have ht' : t = 1 := Subtype.ext ht
    subst t
    change loopCircle γ ((1 : ℝ) : WindingCircle) = γ 1
    rw [AddCircle.coe_period]
    have hzero := loopCircle_apply_lt γ 0 (by norm_num)
    simpa using hzero

theorem loopCircle_integerLift {f : Y → WindingCircle} (γ : Path y y) {n : ℤ}
    (L : IntegerPathLift f γ n) (t : unitInterval) :
    f (loopCircle γ (t : ℝ)) = (L.path t : WindingCircle) := by
  rw [loopCircle_apply]
  exact L.commutes t

theorem loopCircle_postcompose {Z : Type*} [TopologicalSpace Z]
    (f : C(Y, Z)) (γ : Path y y) :
    loopCircle (γ.map f.continuous) = f.comp (loopCircle γ) := by
  ext z
  obtain ⟨t, rfl⟩ := circle_parameter_surjective z
  simp only [ContinuousMap.comp_apply, loopCircle_apply]
  rfl

end CoarseAssembly

end

end OAI
