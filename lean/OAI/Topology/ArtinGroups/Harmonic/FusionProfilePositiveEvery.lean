import Mathlib
import OAI.Topology.ArtinGroups.Complexes.CoefficientTopDual
import OAI.Topology.ArtinGroups.Harmonic.FusionOrbitMultiplicity

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (hm:∀ e,2 ≤ m e)
include hm

lemma fusion_profile_positive_every_label (a:FusionLabel m → FusionLabel m → ℕ)
    (ha:∃ c:ℝ,0≤c ∧ ∀ L,(∑ H,fusionWeight m H*(a H L:ℝ))=c*fusionWeight m L)
    {H₀ L₀:FusionLabel m} (h₀:0<a H₀ L₀) (L:FusionLabel m) : ∃ H,0<a H L := by
  obtain ⟨c,_,h⟩:=ha
  have hsum:0 < ∑ H,fusionWeight m H*(a H L₀:ℝ) := by
    apply lt_of_lt_of_le (mul_pos (fusionWeight_pos m hm H₀) (show (0:ℝ)<(a H₀ L₀:ℝ) by exact_mod_cast h₀))
    exact Finset.single_le_sum (fun H _=>mul_nonneg (fusionWeight_pos m hm H).le (Nat.cast_nonneg (a H L₀)))
      (Finset.mem_univ H₀)
  rw [h] at hsum
  have hcpos:0<c := (mul_pos_iff_of_pos_right (fusionWeight_pos m hm L₀)).mp hsum
  have htarget:0 < ∑ H,fusionWeight m H*(a H L:ℝ) := by
    rw [h]
    exact mul_pos hcpos (fusionWeight_pos m hm L)
  by_contra hn
  push Not at hn
  have hz:∀ H,a H L=0:=fun H=>Nat.eq_zero_of_le_zero (hn H)
  simp only [hz,Nat.cast_zero,MulZeroClass.mul_zero,Finset.sum_const_zero,lt_self_iff_false] at htarget

variable (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "O" => fusionPacketOrbit m d hd hdiag

theorem fusionOrbit_top_socle_Hom_pos (w:List (V × Bool)) (s v:V) (q k b c:ℤ)
    {L₀ H₀ L₁ H₁:FusionLabel m}
    (ht:0<classLayerTopDimension Q q (v,L₀) b (O w s H₀))
    (hs:0<classLayerSocleDimension Q k (v,L₁) c (O w s H₁)) :
    0<fusionOrbitLayerHom m d hd hdiag w s q k := by
  obtain ⟨H,htH⟩:=fusion_profile_positive_every_label m hm
    (fun H L=>classLayerTopDimension Q q (v,L) b (O w s H))
    (fusionPacketOrbit_top_proportional m d hd hdiag hm w s v q b) ht L₁
  have finrank_ne_bot {I:Type} [Fintype I] (P:Submodule ℂ (I → ℂ))
      (hp:0<Module.finrank ℂ P) : P≠⊥ := by
    intro hz
    rw [hz,finrank_bot] at hp
    exact (lt_irrefl 0 hp)
  have htne:coefficientTopDual Q (Y w s H q) (v,L₁) b ≠ ⊥ := by
    exact finrank_ne_bot _ htH
  have hsne:coefficientSocle Q (Y w s H₁ k) (v,L₁) c ≠ ⊥ := by
    exact finrank_ne_bot _ hs
  have hh:=pure_top_socle_totalHomDimension_pos Q (Y w s H q) (Y w s H₁ k)
    (fun i=>i.property) (fun i=>i.property) (v,L₁) b c htne hsne
  have hn (L T:FusionLabel m) : 0≤fusionWeight m L*fusionWeight m T*
      (totalHomDimension Q (Y w s L q) (Y w s T k) (k-q):ℝ) :=
    mul_nonneg (mul_pos (fusionWeight_pos m hm L) (fusionWeight_pos m hm T)).le (Nat.cast_nonneg _)
  apply Finset.sum_pos'
  · intro L _
    exact Finset.sum_nonneg (fun T _=>hn L T)
  · refine ⟨H,Finset.mem_univ H,Finset.sum_pos' (fun T _=>hn H T) ?_⟩
    refine ⟨H₁,Finset.mem_univ H₁,?_⟩
    exact mul_pos (mul_pos (fusionWeight_pos m hm H) (fusionWeight_pos m hm H₁)) (by exact_mod_cast hh)

theorem fusionOrbit_top_zero_of_Hom_zero (w:List (V × Bool)) (s v:V) (q k c:ℤ)
    {L H:FusionLabel m} (hs:0<classLayerSocleDimension Q k (v,L) c (O w s H))
    (hh:fusionOrbitLayerHom m d hd hdiag w s q k=0) :
    ∀ L' H' b,classLayerTopDimension Q q (v,L') b (O w s H')=0 := by
  intro L' H' b
  by_contra ht
  have hp:=fusionOrbit_top_socle_Hom_pos m hm d hd hdiag w s v q k b c (Nat.pos_of_ne_zero ht) hs
  rw [hh] at hp
  exact (lt_irrefl 0 hp)

end HarmonicArtin

end OAI
