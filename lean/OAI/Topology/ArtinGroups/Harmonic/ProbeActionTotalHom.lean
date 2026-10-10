import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.MapPacket
import OAI.Topology.ArtinGroups.Complexes.TotalHomDimensionReading

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open ReversibleQuiver.ProbeEmbedding

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "aw" => sourceArtinAction M (K:=K)
local notation "bw" => sourceProbeAction M (K:=K)

lemma sourceProbeAction_total_hom_reading (g:Artin M) (x:FiniteHomotopyClass Q (K:=K))
    (α:(S⊕Unit)×FusionLabel m) (b:Bool) (t:ℤ) :
    totalHomDimension R
      (minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex
      (minimalClassModel R (classMap Q x)).complex t=
      classLevelArray Q (aw g x) (α,t-1) := by
  refine totalHomDimension_of_reading R _ _ (classGeneratorArray Q (aw g x)) α ?_ t
  intro degree internal
  exact (minimalClassModel_homDimension R _ _ degree internal).trans
    (sourceProbeAction_hom_reading M g x α b degree internal)

end HarmonicArtin

end OAI
