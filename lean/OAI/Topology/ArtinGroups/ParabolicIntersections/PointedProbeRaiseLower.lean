import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCappedCandidate
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCapSaturation
import OAI.Topology.ArtinGroups.Harmonic.ProbeRaiseLower
import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.CappedCandidate
import OAI.Topology.ArtinGroups.Harmonic.ProbeCoreTermNonpos
import OAI.Topology.ArtinGroups.Harmonic.WordArtinSubtypeMem

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

lemma pointedProbe_raise_lower (T J:Set S) (z g:Artin M) (q l:ℤ) (p:S⊕Unit→ℝ)
    (X:PointedCappedCandidate M f T J z q p) (hg:g∈artinParabolic M T) (hl:l<0)
    (hgz:∀H,ClassCapOn Q (pointedFamily M f (g*z) H)
      (Set.range (unfoldedInclusion M T)) q)
    (α:FusionVertex (V:=S⊕Unit) m) (ha:α∈Set.range (unfoldedInclusion M T)) (b:Bool)
    (hy:ClassLowerBound R l (bw g⁻¹ (initialClass R (.inr (α,b)))))
    (hsoc:∀j:J,∀L c,classLayerSocleDimension R l (.inl (.inl j,L)) c
      (bw g⁻¹ (initialClass R (.inr (α,b))))=0) :
    ClassLowerBound R (l+1) (bw g⁻¹ (initialClass R (.inr (α,b)))) := by
  obtain ⟨⟨s,L⟩,rfl⟩:=ha
  have hu:=X.probe_euler g hg (.inl (s:S),L) b l hsoc
  dsimp only at hu
  have hzero:=pointedMultiplicity_cap_zero M f T (g*z) q (q-l) (by omega) hgz s s.property
  rw [hzero,MulZeroClass.mul_zero,ite_eq_right (ne_of_lt hl),zero_sub] at hu
  intro i
  have hge:=hy i
  have hne:((minimalClassModel R (bw g⁻¹ (initialClass R (.inr ((Sum.inl (s:S),L),b))))).complex.placement i).level≠l := by
    intro he
    have hn:=sourceProbe_core_dot_neg_of_nonempty M (K:=ℂ) T J g⁻¹
      ((artinParabolic M T).inv_mem hg) (.inl (s:S),L) b l (ne_of_lt hl) p
      X.cartan_nonpos X.negative (fun j H c=>Submodule.finrank_eq_zero.mp (hsoc j H c)) ⟨⟨i,he⟩⟩
    dsimp only at hn hu
    linarith
  change l≤((minimalClassModel R (bw g⁻¹ (initialClass R (.inr ((Sum.inl (s:S),L),b))))).complex.placement i).level at hge
  change l+1≤((minimalClassModel R (bw g⁻¹ (initialClass R (.inr ((Sum.inl (s:S),L),b))))).complex.placement i).level
  omega

theorem pointedProbe_zero_saturation {B:Type*} [Finite B]
    (T J:Set S) (z h:Artin M) (q:ℤ) (p:S⊕Unit→ℝ)
    (X:PointedCappedCandidate M f T J z q p) (hh:h∈artinParabolic M T)
    (hzh:∀H,ClassCapOn Q (pointedFamily M f (h*z) H)
      (Set.range (unfoldedInclusion M T)) q)
    (α:B→FusionVertex (V:=S⊕Unit) m) (ha:∀r,α r∈Set.range (unfoldedInclusion M T))
    (b:B→Bool) :
    ∃ a∈artinParabolic M J,
      (∀H,ClassCapOn Q (pointedFamily M f (a*z) H)
        (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q) ∧
      (∀r,ClassLowerBound R 0 (bw (a*h⁻¹) (initialClass R (.inr (α r,b r))))) ∧
      ∀r (j:J) L c,classLayerSocleDimension R 0 (.inl (.inl j,L)) c
        (bw (a*h⁻¹) (initialClass R (.inr (α r,b r))))=0 := by
  have aux:∀n:ℕ,∀z h:Artin M,PointedCappedCandidate M f T J z q p→
      h∈artinParabolic M T→
      (∀H,ClassCapOn Q (pointedFamily M f (h*z) H) (Set.range (unfoldedInclusion M T)) q)→
      (∀r,ClassLowerBound R (-(n:ℤ)) (bw h⁻¹ (initialClass R (.inr (α r,b r)))))→
      ∃ a∈artinParabolic M J,
        (∀H,ClassCapOn Q (pointedFamily M f (a*z) H)
          (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q) ∧
        (∀r,ClassLowerBound R 0 (bw (a*h⁻¹) (initialClass R (.inr (α r,b r))))) ∧
        ∀r (j:J) L c,classLayerSocleDimension R 0 (.inl (.inl j,L)) c
          (bw (a*h⁻¹) (initialClass R (.inr (α r,b r))))=0 := by
    intro n
    induction n with
    | zero =>
      intro z h X hh hc hy
      apply pointedProbe_cap_saturation M f T J X.subset X.spherical z h hh q 0 (by omega)
        X.cap hc α ha b
      simpa only [Nat.cast_zero,neg_zero] using hy
    | succ n ih =>
      intro z h X hh hc hy
      obtain ⟨a,haJ,hcap,hlower,hsoc⟩:=pointedProbe_cap_saturation M f T J X.subset X.spherical z h hh q
        (-((n+1:ℕ):ℤ)) (by omega) X.cap hc α ha b hy
      have haT:=artinParabolic_mono M X.subset haJ
      have hhT:(h*a⁻¹)∈artinParabolic M T:=
        (artinParabolic M T).mul_mem hh ((artinParabolic M T).inv_mem haT)
      have he:(h*a⁻¹)*(a*z)=h*z:=by simp only [_root_.mul_assoc,inv_mul_cancel_left]
      have hei:(h*a⁻¹)⁻¹=a*h⁻¹:=by simp only [_root_.mul_inv_rev,inv_inv]
      have hraise:∀r,ClassLowerBound R (-(n:ℤ))
          (bw (h*a⁻¹)⁻¹ (initialClass R (.inr (α r,b r)))) := by
        intro r
        have hr:=pointedProbe_raise_lower M f T J (a*z) (h*a⁻¹) q (-((n+1:ℕ):ℤ)) p (X.move a haJ hcap)
          hhT (by omega) (by rw [he]; exact hc) (α r) (ha r) (b r)
          (by rw [hei]; exact hlower r) (by rw [hei]; exact hsoc r)
        convert hr using 1
        omega
      obtain ⟨a',ha',hcap',hlower',hsoc'⟩:=ih (a*z) (h*a⁻¹) (X.move a haJ hcap) hhT
        (by rw [he];exact hc) hraise
      refine ⟨a'*a,(artinParabolic M J).mul_mem ha' haJ,?_,?_,?_⟩
      · simpa only [_root_.mul_assoc] using hcap'
      · simpa only [hei,_root_.mul_assoc] using hlower'
      · simpa only [hei,_root_.mul_assoc] using hsoc'
  obtain ⟨l,hl⟩:=finiteFamily_lowerBound R (fun r=>bw h⁻¹ (initialClass R (.inr (α r,b r))))
  apply aux (-l).toNat z h X hh hzh
  intro r i
  have hh:=hl r i
  have hn:Int.ofNat (-l).toNat≥-l:=Int.self_le_toNat (-l)
  omega

end HarmonicArtin.ParabolicIntersections

end OAI
