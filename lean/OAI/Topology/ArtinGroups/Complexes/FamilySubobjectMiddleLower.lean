import Mathlib
import OAI.Topology.ArtinGroups.Complexes.SubobjectMiddleLowerBound

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
open Matrix

variable {V A T K:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Fintype T]
attribute [local instance] Classical.decEq Classical.propDecidable

lemma family_subobject_middle_lower_bound {B H:Type*} [Fintype H]
    (M:H→FiniteModel Q (K:=K)) (Y:BasedComplex Q (K:=K) T)
    {q d:ℤ} (hM:∀h i,((M h).complex.placement i).level=q)
    (hY:∀i,(Y.placement i).level=d)
    (F:B→H→FiniteModel Q (K:=K)) (hF:∀b h i,((F b h).complex.placement i).level=q)
    (ι:∀b h,TermwiseSplitInjection Q (F b h).complex (M h).complex)
    (active:Set V) (hsF:∀b h i,((F b h).complex.placement i).color∈active)
    (hsY:∀α∈active,∀c,coefficientSocle Q Y α c=⊥)
    (ω:H→ℝ) (hω:∀h,0≤ω h) (e:V→ℝ)
    (he:e∈convexHull ℝ (Set.range fun b=>∑h,ω h • generatorVector Q (F b h).complex)) :
    generatorVector Q Y ⬝ᵥ ((unfoldedCartan Q).mulVec
      (e-∑h,ω h • generatorVector Q (M h).complex))≤
      ∑h,ω h*(totalHomDimension Q Y (M h).complex (q-d+1):ℝ) := by
  let L:(V→ℝ)→ₗ[ℝ]ℝ:=
    { toFun:=fun x=>generatorVector Q Y ⬝ᵥ ((unfoldedCartan Q).mulVec x)
      map_add':=fun x y=>by simp only [mulVec_add,dotProduct_add]
      map_smul':=fun r x=>by simp only [mulVec_smul,dotProduct_smul,smul_eq_mul,RingHom.id_apply] }
  let m:V→ℝ:=∑h,ω h • generatorVector Q (M h).complex
  let D:ℝ:=∑h,ω h*(totalHomDimension Q Y (M h).complex (q-d+1):ℝ)
  have hbound (b:B):L (∑h,ω h • generatorVector Q (F b h).complex)-L m≤D := by
    have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun h _=>mul_le_mul_of_nonneg_left
      (subobject_middle_lower_bound Q (M h).complex (F b h).complex Y
        (hM h) (hF b h) hY (ι b h) active (hsF b h) hsY) (hω h))
    change (∑h,ω h*L (generatorVector Q (F b h).complex-generatorVector Q (M h).complex))≤D at hh
    simp only [map_sub,mul_sub,Finset.sum_sub_distrib] at hh
    simpa only [m,map_sum,map_smul,smul_eq_mul,RingHom.id_apply] using hh
  have hinc:Set.range (fun b=>∑h,ω h • generatorVector Q (F b h).complex)⊆L ⁻¹' Set.Iic (D+L m) := by
    rintro x ⟨b,rfl⟩
    exact sub_le_iff_le_add.mp (hbound b)
  have hh:=convexHull_min hinc ((convex_Iic (D+L m)).linear_preimage L) he
  change L (e-m)≤D
  rw [map_sub]
  exact sub_le_iff_le_add.mpr hh

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
