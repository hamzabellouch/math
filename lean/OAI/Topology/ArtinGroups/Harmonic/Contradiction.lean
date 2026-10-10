import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.IsolatedIterationData
import OAI.Topology.ArtinGroups.Harmonic.Stage

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {M:CoxeterMatrix S}
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d

namespace IsolatedIterationData
variable (D:IsolatedIterationData M)

theorem contradiction (hI:D.I.Nonempty) (hq:0<D.q)
    (hframe:∀ z,D.valid z→μ z D.s 0 (.inr ())=1)
    (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z) : False := by
  obtain ⟨b,hb⟩:=finiteFamily_lowerBound Q (O z D.s)
  obtain ⟨z',hz',hc',hb',hs⟩:=D.saturate z hz hc b 0 hq hb
  have hf:(Sum.inr () : S⊕Unit)∉Sum.inl '' D.I := by
    rintro ⟨i,hi,he⟩
    exact Sum.inl_ne_inr he
  obtain ⟨i,hi⟩:=hI
  have ha:∃ u∈Sum.inl '' D.I,C (.inr ()) u<0 := by
    refine ⟨.inl i,⟨i,hi,rfl⟩,?_⟩
    have hC : C = framedCartan M := by
      convert fusionFoldedCartan_eq_framedCartan M using 1
      congr 1
      exact Subsingleton.elim _ _
    rw [hC]
    change (-1:ℝ)<0
    norm_num
  have hh:=(D.separation z' hz' hc' 0 hs).1 (.inr ()) hf ha
  rw [hframe z' hz'] at hh
  exact one_ne_zero hh

end IsolatedIterationData
end HarmonicArtin

end OAI
