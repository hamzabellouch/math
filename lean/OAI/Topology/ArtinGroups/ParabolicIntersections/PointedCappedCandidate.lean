import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCap
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedGroupProbeEuler
import OAI.Topology.ArtinGroups.Harmonic.CappedCandidate
import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedInclusionRangeMono
import OAI.Topology.ArtinGroups.Harmonic.GroupProbeEuler

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=ℂ)
local notation "C" => fusionFoldedCartan m d

structure PointedCappedCandidate (T J:Set S) (z:Artin M) (q:ℤ) (p:S⊕Unit→ℝ) : Prop where
  subset : J⊆T
  spherical : IsSpherical M J
  cap : ∀H,ClassCapOn Q (pointedFamily M f z H)
    (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q
  harmonic : ∀j:J,(C *ᵥ p) (.inl (j:S))=0
  exterior : ∀v,v∉Sum.inl '' J→pointedMultiplicity M f z q v=p v
  negative : ∀s∈T,s∉J→(C *ᵥ p) (.inl s)<0
  representatives : ∀a∈artinParabolic M J,
    (∀H,ClassCapOn Q (pointedFamily M f (a*z) H)
      (Set.range (unfoldedInclusion M T)) q)→
    ∀j:J,p (.inl (j:S))≤ pointedMultiplicity M f (a*z) q (.inl (j:S))

namespace PointedCappedCandidate
variable {M} {f:S} {T J:Set S} {z:Artin M} {q:ℤ} {p:S⊕Unit→ℝ}

lemma cartan_nonpos (X:PointedCappedCandidate M f T J z q p) (s:S) (hs:s∈T) :
    (C *ᵥ p) (.inl s)≤0 := by
  by_cases hj:s∈J
  · exact (X.harmonic ⟨s,hj⟩).le
  · exact (X.negative s hs hj).le

lemma move (X:PointedCappedCandidate M f T J z q p) (a:Artin M) (ha:a∈artinParabolic M J)
    (hc:∀H,ClassCapOn Q (pointedFamily M f (a*z) H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q) :
    PointedCappedCandidate M f T J (a*z) q p := by
  refine ⟨X.subset,X.spherical,hc,X.harmonic,?_,X.negative,?_⟩
  · intro v hv
    rw [pointedMultiplicity_exterior_ordered M f J a ha z v hv q]
    exact X.exterior v hv
  · intro b hb hcap j
    have hh:=X.representatives (b*a) ((artinParabolic M J).mul_mem hb ha)
      (by simpa only [_root_.mul_assoc] using hcap) j
    simpa only [_root_.mul_assoc] using hh

lemma local_representatives (X:PointedCappedCandidate M f T J z q p)
    (a:Artin M) (ha:a∈artinParabolic M J)
    (hc:∀H,ClassCapOn Q (pointedFamily M f (a*z) H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q) :
    ∀j:J,p (.inl (j:S))≤ pointedMultiplicity M f (a*z) q (.inl (j:S)) := by
  apply X.representatives a ha
  have hh:=pointed_cap_closed_extend M f T J X.subset z a ha q X.cap hc
  exact fun H i hi=>hh H i (Or.inl hi)

lemma probe_euler (X:PointedCappedCandidate M f T J z q p)
    (g:Artin M) (hg:g∈artinParabolic M T)
    (α:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ)
    (hsoc:∀j:J,∀L c,classLayerSocleDimension R l (.inl (.inl j,L)) c
      (bw g⁻¹ (initialClass R (.inr (α,b))))=0) :
    let N:=((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
      (minimalClassModel_minimal R _) l);
    (if l=0 then fusionWeight m α.2*p α.1 else 0)-
      (fun β=>generatorVector R N (.inl β)) ⬝ᵥ fusionFold m (C *ᵥ p) ≤
      fusionWeight m α.2*pointedMultiplicity M f (g*z) (q-l) α.1 := by
  apply pointedGroup_probe_euler M f J T X.spherical z g hg q p
    (pointed_cap_closed_mono M f X.subset z q X.cap) X.harmonic X.exterior
    X.local_representatives α b l
  intro j L c
  exact Submodule.finrank_eq_zero.mp (hsoc j L c)

end PointedCappedCandidate
end HarmonicArtin.ParabolicIntersections

end OAI
