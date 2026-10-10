import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionColorRegion
import OAI.Topology.ArtinGroups.Quivers.ClosedNeighborhood

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

theorem fusionOrbitColor_secondary_bound (w:List (V×Bool)) (s:V) (q k:ℤ) (U:Set V)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U))
    (hcap:∀ L,ClassCapOn Q (O w s L) (fusionColorRegion m U) q) (hk:k<q) :
    fusionWeightedHom m d hd
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L) (fun H=>Y w s H k) (k-q) ≤
    fusionWeightedHom m d hd (fun H=>Y w s H (k-1))
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L) (q-k+1) := by
  let T:=fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L
  let incl L:=blockInclusionMap Q (Y w s L q) _
    (pure_color_block Q _ _ (fun i=>i.property) (hb L))
  let proj L:=blockProjectionMap Q (Y w s L q) _
    (pure_color_block Q _ _ (fun i=>i.property) (hb L))
  have hret:∀ L,(incl L).matrix*(proj L).matrix=projectiveIdentity Q (T L).placement := by
    intro L
    convert block_inclusion_projection Q (Y w s L q)
      {i | ((Y w s L q).placement i).color∈fusionColorRegion m U} using 1
    · rfl
    · apply Matrix.ext
      intro i j
      simp only [projectiveIdentity,Matrix.diagonal_apply]
      by_cases h:i=j <;> simp only [h,ite_true,ite_false]
      rfl
  exact fusionOrbit_weighted_secondary_bound m d hd hdiag hm w s T (fusionColorRegion m U)
    q k (fun L i=>i.val.property) (fun L i=>i.property) incl proj
    (fun L=>by
      convert hret L using 1 <;> congr 1
      exact Subsingleton.elim _ _) hcap hk

lemma fusionOrbitColor_Hom_zero_of_previous (w:List (V×Bool)) (s:V) (q k:ℤ) (U:Set V)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U))
    (hcap:∀ L,ClassCapOn Q (O w s L) (fusionColorRegion m U) q) (hk:k<q)
    (hz:fusionWeightedHom m d hd (fun H=>Y w s H (k-1))
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L) (q-k+1)=0) :
    fusionWeightedHom m d hd
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q U hb L) (fun H=>Y w s H k) (k-q)=0 := by
  apply le_antisymm
  · exact (fusionOrbitColor_secondary_bound m d hd hdiag hm w s q k U hb hcap hk).trans_eq hz
  · exact fusionWeightedHom_nonneg m d hd hm _ _ _

end HarmonicArtin

end OAI
