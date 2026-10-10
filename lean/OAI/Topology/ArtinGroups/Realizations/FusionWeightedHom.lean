import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionOrbitModel
import OAI.Topology.ArtinGroups.Complexes.HomDimensionRetract

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "O" => fusionOrbitModel m d hd hdiag

theorem fusionOrbit_summand_secondary_bound (w:List (V × Bool)) (s:V)
    (L H:FusionLabel m) {T:Type*} [Fintype T] (M:BasedComplex Q (K:=ℂ) T)
    (U:Set (FusionVertex (V:=V) m)) (q k:ℤ)
    (hM:∀ i,(M.placement i).level=q) (hU:∀ i,(M.placement i).color∈U)
    (ι:Map Q M (Y w s L q)) (π:Map Q (Y w s L q) M)
    (hret:ι.matrix*π.matrix=projectiveIdentity Q M.placement)
    (hcap:(O w s L).complex.CappedOn Q U q) (hk:k<q) :
    totalHomDimension Q M (Y w s H k) (k-q) ≤
      totalHomDimension Q (Y w s H (k-1)) M (q-k+1) := by
  exact cappedSummand_total_bound Q (O w s L).complex (O w s H).complex
    (fusionOrbitModel_minimal m d hd hdiag w s L)
    (fusionOrbitModel_minimal m d hd hdiag w s H) M U q k hM hU ι π hret hcap
    (fun n v h=>fusionOrbitModel_negative_homDimension m d hd hdiag w s s L H n v (by omega))

theorem fusionOrbit_summand_middle (w:List (V × Bool)) (s:V)
    (L H:FusionLabel m) {T:Type*} [Fintype T] (M:BasedComplex Q (K:=ℂ) T)
    (q k:ℤ) (ι:Map Q M (Y w s L q)) (π:Map Q (Y w s L q) M)
    (hret:ι.matrix*π.matrix=projectiveIdentity Q M.placement) :
    totalHomDimension Q M (Y w s H k) (k-q+1)=0 := by
  apply Nat.eq_zero_of_le_zero
  have h:=totalHomDimension_retract_source Q M (Y w s L q) (Y w s H k) ι π hret (k-q+1)
  rwa [fusionOrbitLayer_middle] at h

noncomputable def fusionWeightedHom {T R:FusionLabel m → Type*}
    [∀ L,Fintype (T L)] [∀ H,Fintype (R H)]
    (P:∀ L,BasedComplex Q (K:=ℂ) (T L)) (F:∀ H,BasedComplex Q (K:=ℂ) (R H)) (t:ℤ) : ℝ :=
  ∑ L,∑ H,fusionWeight m L*fusionWeight m H*(totalHomDimension Q (P L) (F H) t:ℝ)

lemma fusionWeightedHom_nonneg (hm:∀ e,2 ≤ m e) {T R:FusionLabel m → Type*}
    [∀ L,Fintype (T L)] [∀ H,Fintype (R H)]
    (P:∀ L,BasedComplex Q (K:=ℂ) (T L)) (F:∀ H,BasedComplex Q (K:=ℂ) (R H)) (t:ℤ) :
    0≤fusionWeightedHom m d hd P F t := by
  apply Finset.sum_nonneg
  intro L _
  apply Finset.sum_nonneg
  intro H _
  exact mul_nonneg (mul_pos (fusionWeight_pos m hm L) (fusionWeight_pos m hm H)).le (Nat.cast_nonneg _)

theorem fusionOrbit_weighted_secondary_bound (hm:∀ e,2 ≤ m e)
    (w:List (V × Bool)) (s:V) {T:FusionLabel m → Type*} [∀ L,Fintype (T L)]
    (M:∀ L,BasedComplex Q (K:=ℂ) (T L)) (U:Set (FusionVertex (V:=V) m)) (q k:ℤ)
    (hM:∀ L i,((M L).placement i).level=q) (hU:∀ L i,((M L).placement i).color∈U)
    (ι:∀ L,Map Q (M L) (Y w s L q)) (π:∀ L,Map Q (Y w s L q) (M L))
    (hret:∀ L,(ι L).matrix*(π L).matrix=projectiveIdentity Q (M L).placement)
    (hcap:∀ L,(O w s L).complex.CappedOn Q U q) (hk:k<q) :
    fusionWeightedHom m d hd M (fun H=>Y w s H k) (k-q) ≤
      fusionWeightedHom m d hd (fun H=>Y w s H (k-1)) M (q-k+1) := by
  unfold fusionWeightedHom
  rw [Finset.sum_comm (f:=fun H L=>fusionWeight m H*fusionWeight m L*
    (totalHomDimension Q (Y w s H (k-1)) (M L) (q-k+1):ℝ))]
  apply Finset.sum_le_sum
  intro L _
  apply Finset.sum_le_sum
  intro H _
  rw [mul_comm (fusionWeight m H) (fusionWeight m L)]
  apply mul_le_mul_of_nonneg_left _ (mul_pos (fusionWeight_pos m hm L) (fusionWeight_pos m hm H)).le
  exact_mod_cast fusionOrbit_summand_secondary_bound m d hd hdiag w s L H (M L) U q k
    (hM L) (hU L) (ι L) (π L) (hret L) (hcap L) hk

end HarmonicArtin

end OAI
