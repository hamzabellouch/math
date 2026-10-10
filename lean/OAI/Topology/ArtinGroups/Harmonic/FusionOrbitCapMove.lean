import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionProfilePositiveEvery
import OAI.Topology.ArtinGroups.Complexes.UpperBound

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (hm:∀ e,2 ≤ m e)
  (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s) (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag

include hm in

theorem fusionOrbit_cap_move_of_Hom_zero
    (w:List (V×Bool)) (s v:V) (q k c:ℤ)
    (hcap:∀ H:FusionLabel m,ClassUpperBound Q q (O w s H))
    {L H:FusionLabel m} (hs:0<classLayerSocleDimension Q k (v,L) c (O w s H))
    (hh:fusionOrbitLayerHom m d hd hdiag w s q k=0) :
    ∀ T:FusionLabel m,ClassUpperBound Q q (O ((v,true)::w) s T) := by
  intro T
  have ht:=fusionOrbit_top_zero_of_Hom_zero m hm d hd hdiag w s v q k c hs hh
  exact classPacketPerm_cap_of_top_zero Q
    (fusionQuiver_no_loops m d hd hdiag) (fun a:FusionLabel m=>(v,a))
    (fusionColor_orthogonal m d hd hdiag v) (O w s T) (hcap T)
    (fun a b=>ht a T b)

end HarmonicArtin

end OAI
