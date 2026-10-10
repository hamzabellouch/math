import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionPacketOrbit
import OAI.Topology.ArtinGroups.Harmonic.FusionExpressionOrbit
import OAI.Topology.ArtinGroups.Harmonic.CanonicalFusionLow

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd

include hm

theorem canonicalFusionLow_count_proportional (w:List V) (z:List (V×Bool))
    (s v:V) (q k:ℤ) : ∃ c:ℝ,0≤c ∧ ∀ L,
    (∑ H,fusionWeight m H*(classLevelArray Q
      (canonicalFusionLow m d hd hdiag w q (classLayer Q q (fusionPacketOrbit m d hd hdiag z s H)))
       ((v,L),k):ℝ))=c*fusionWeight m L := by
  simpa only [fusionExpressionOrbit,canonicalFusionExpression_action,fusionPacketOrbit] using
    fusionExpressionOrbit_count_proportional m d hd hdiag hm
      (canonicalFusionExpression w z q) s v k

end HarmonicArtin

end OAI
