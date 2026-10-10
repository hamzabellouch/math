import Mathlib
import OAI.Topology.ArtinGroups.Complexes.TermwiseSplitInjection

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
open Matrix

variable {V A I J T K:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [Fintype T] [DecidableEq I] [DecidableEq J] [DecidableEq T]

omit [DecidableEq J] [DecidableEq T] in
lemma subobject_middle_lower_bound (M:BasedComplex Q (K:=K) J)
    (S:BasedComplex Q (K:=K) I) (Y:BasedComplex Q (K:=K) T)
    {q d:ℤ} (hM:∀i,(M.placement i).level=q)
    (hS:∀i,(S.placement i).level=q) (hY:∀i,(Y.placement i).level=d)
    (ι:TermwiseSplitInjection Q S M) (active:Set V)
    (hsS:∀i,(S.placement i).color∈active)
    (hsY:∀α∈active,∀c,coefficientSocle Q Y α c=⊥) :
    generatorVector Q Y ⬝ᵥ ((unfoldedCartan Q).mulVec
      (generatorVector Q S-generatorVector Q M)) ≤
        (totalHomDimension Q Y M (q-d+1):ℝ) := by
  rw [mulVec_sub,dotProduct_sub,pure_cartan_euler Q Y S hY hS,
    pure_cartan_euler Q Y M hY hM]
  have hz:=pure_total_coefficient_homDimension_zero_of_socle_zero Q S Y hS hY active hsS hsY
  have hm:=pure_total_coefficient_homDimension_mono Q Y S M hY hS hM ι
  have hm':(totalHomDimension Q Y S (q-d):ℝ)≤totalHomDimension Q Y M (q-d):=by
    exact_mod_cast hm
  have hn:(0:ℝ)≤totalHomDimension Q Y S (q-d+1):=Nat.cast_nonneg _
  have hp:(0:ℝ)≤totalHomDimension Q M Y (d-q):=Nat.cast_nonneg _
  rw [hz,Nat.cast_zero]
  linarith

omit [DecidableEq J] [DecidableEq T] in
lemma convex_subobject_middle_lower_bound {B:Type*}
    (M:BasedComplex Q (K:=K) J) (Y:BasedComplex Q (K:=K) T)
    {q d:ℤ} (hM:∀i,(M.placement i).level=q) (hY:∀i,(Y.placement i).level=d)
    (F: B→FiniteModel Q (K:=K))
    (hF:∀b i,((F b).complex.placement i).level=q)
    (ι:∀b,TermwiseSplitInjection Q (F b).complex M) (active:Set V)
    (hsF:∀b i,((F b).complex.placement i).color∈active)
    (hsY:∀α∈active,∀c,coefficientSocle Q Y α c=⊥)
    (e:V→ℝ) (he:e∈convexHull ℝ (Set.range fun b=>generatorVector Q (F b).complex)) :
    generatorVector Q Y ⬝ᵥ ((unfoldedCartan Q).mulVec (e-generatorVector Q M)) ≤
      (totalHomDimension Q Y M (q-d+1):ℝ) := by
  let L:(V→ℝ)→ₗ[ℝ]ℝ :=
    { toFun:=fun x=>generatorVector Q Y ⬝ᵥ ((unfoldedCartan Q).mulVec x)
      map_add':=fun x y=>by simp only [mulVec_add,dotProduct_add]
      map_smul':=fun r x=>by simp only [mulVec_smul,dotProduct_smul,smul_eq_mul,RingHom.id_apply] }
  let c:ℝ:=(totalHomDimension Q Y M (q-d+1):ℝ)+L (generatorVector Q M)
  have h: Set.range (fun b=>generatorVector Q (F b).complex) ⊆ L ⁻¹' Set.Iic c := by
    rintro x ⟨b,rfl⟩
    have hh:=subobject_middle_lower_bound Q M (F b).complex Y hM (hF b) hY
      (ι b) active (hsF b) hsY
    change L (generatorVector Q (F b).complex)≤c
    dsimp only [L,c,LinearMap.coe_mk,AddHom.coe_mk]
    simpa only [mulVec_sub,dotProduct_sub,sub_le_iff_le_add] using hh
  have hh:=convexHull_min h ((convex_Iic c).linear_preimage L) he
  change L e≤c at hh
  change L (e-generatorVector Q M)≤_
  rw [map_sub]
  exact sub_le_iff_le_add.mpr hh

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
