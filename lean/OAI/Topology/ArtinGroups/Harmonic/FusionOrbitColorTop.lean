import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionProfilePositiveEvery
import OAI.Topology.ArtinGroups.Harmonic.FusionColorRegion
import OAI.Topology.ArtinGroups.Complexes.ColorRestrictionTopZero

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
include hm
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "O" => fusionPacketOrbit m d hd hdiag

theorem fusionOrbitColor_top_socle_Hom_pos (w:List (V×Bool)) (s v:V) (q k b c:ℤ)
    (U:Set V) (hv:v∈U)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U))
    {L₀ H₀ L₁ H₁:FusionLabel m}
    (ht:0<classLayerTopDimension Q q (v,L₀) b (O w s H₀))
    (hs:0<classLayerSocleDimension Q k (v,L₁) c (O w s H₁)) :
    0<fusionWeightedHom m d hd
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L)
      (fun H=>Y w s H k) (k-q) := by
  obtain ⟨H,htH⟩:=fusion_profile_positive_every_label m hm
    (fun H L=>classLayerTopDimension Q q (v,L) b (O w s H))
    (fusionPacketOrbit_top_proportional m d hd hdiag hm w s v q b) ht L₁
  have hn {I:Type} [Fintype I] (P:Submodule ℂ (I→ℂ))
      (hp:0<Module.finrank ℂ P):P≠⊥ := by
    intro hz
    rw [hz,finrank_bot] at hp
    exact (lt_irrefl 0 hp)
  have htne:coefficientTopDual Q
      (fusionOrbitColorLayer m d hd hdiag w s q U hb H) (v,L₁) b≠⊥ := by
    intro hz
    have hfull:=colorRestriction_top_zero Q (Y w s H q) q (fusionColorRegion m U)
      (fun i=>i.property) (hb H) (v,L₁) hv b hz
    exact hn _ htH hfull
  have hsne:coefficientSocle Q (Y w s H₁ k) (v,L₁) c≠⊥:=hn _ hs
  have hh:=pure_top_socle_totalHomDimension_pos Q
    (fusionOrbitColorLayer m d hd hdiag w s q U hb H) (Y w s H₁ k)
    (fun i=>i.val.property) (fun i=>i.property) (v,L₁) b c htne hsne
  have hnon (L T:FusionLabel m):0≤fusionWeight m L*fusionWeight m T*
      (totalHomDimension Q (fusionOrbitColorLayer m d hd hdiag w s q U hb L)
        (Y w s T k) (k-q):ℝ):=
    mul_nonneg (mul_pos (fusionWeight_pos m hm L) (fusionWeight_pos m hm T)).le (Nat.cast_nonneg _)
  apply Finset.sum_pos'
  · intro L _
    exact Finset.sum_nonneg (fun T _=>hnon L T)
  · refine ⟨H,Finset.mem_univ H,Finset.sum_pos' (fun T _=>hnon H T) ?_⟩
    refine ⟨H₁,Finset.mem_univ H₁,?_⟩
    exact mul_pos (mul_pos (fusionWeight_pos m hm H) (fusionWeight_pos m hm H₁)) (by exact_mod_cast hh)

theorem fusionOrbitColor_top_zero_of_Hom_zero (w:List (V×Bool)) (s v:V) (q k c:ℤ)
    (U:Set V) (hv:v∈U)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U))
    {L H:FusionLabel m} (hs:0<classLayerSocleDimension Q k (v,L) c (O w s H))
    (hh:fusionWeightedHom m d hd
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L)
      (fun H=>Y w s H k) (k-q)=0) :
    ∀ L' H' b,classLayerTopDimension Q q (v,L') b (O w s H')=0 := by
  intro L' H' b
  by_contra ht
  have hp:=fusionOrbitColor_top_socle_Hom_pos m d hd hdiag hm w s v q k b c U hv hb
    (Nat.pos_of_ne_zero ht) hs
  rw [hh] at hp
  exact lt_irrefl 0 hp

end HarmonicArtin

end OAI
