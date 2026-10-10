import Mathlib
import OAI.Topology.ArtinGroups.Functors.TermwiseSplitInjection
import OAI.Topology.ArtinGroups.Harmonic.MapPacket
import OAI.Topology.ArtinGroups.Complexes.TotalHomDimensionReading
import OAI.Topology.ArtinGroups.Realizations.QuotientFinrankKer

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

lemma sourceProbeAction_embedded_hom_reading {I:Type} [Fintype I]
    (g:Artin M) (E:BasedComplex Q (K:=K) I)
    (α:(S⊕Unit)×FusionLabel m) (b:Bool) (n v:ℤ) :
    homDimension R
      (minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex
      (complex Q E) n v=
      classGeneratorArray Q (aw g (classOfComplex Q E)) ⟨α,n,v-1⟩ := by
  change classHomDimension R n v
    (classOfComplex R (minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex)
    (classOfComplex R (complex Q E))=_
  rw [← classMap_complex]
  have hy : classOfComplex R (minimalClassModel R
      (bw g⁻¹ (initialClass R (.inr (α,b))))).complex =
      bw g⁻¹ (initialClass R (.inr (α,b))) := minimalClassModel_class R _
  rw [hy,sourceProbeAction_hom_reading]

lemma sourceProbeAction_embedded_total_reading {I:Type} [Fintype I]
    (g:Artin M) (E:BasedComplex Q (K:=K) I)
    (α:(S⊕Unit)×FusionLabel m) (b:Bool) (t:ℤ) :
    totalHomDimension R
      (minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex
      (complex Q E) t=
      classLevelArray Q (aw g (classOfComplex Q E)) (α,t-1) := by
  apply totalHomDimension_of_reading
  exact sourceProbeAction_embedded_hom_reading M g E α b

lemma sourceProbeAction_layer_middle_le {I:Type} [Fintype I]
    (g:Artin M) (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (α:(S⊕Unit)×FusionLabel m) (b:Bool) (l q:ℤ) :
    totalHomDimension R
      ((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
        (minimalClassModel_minimal R _) l)
      (complex Q (E.pureLayer Q hE q)) (q-l+1)≤
      classLevelArray Q (aw g (classOfComplex Q E)) (α,q-l) := by
  have h:=middleLayer_totalHomDimension_le R
    (minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex
    (complex Q E) (minimalClassModel_minimal R _) (complex_minimal Q hE) l q
  rw [pureLayer_complex Q E hE q,sourceProbeAction_embedded_total_reading M g E α b] at h
  simp only [add_sub_cancel_right] at h
  exact h

end HarmonicArtin

end OAI
