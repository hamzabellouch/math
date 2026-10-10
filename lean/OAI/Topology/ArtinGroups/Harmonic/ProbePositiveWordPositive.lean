import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ProbePositiveWordAppend
import OAI.Topology.ArtinGroups.Harmonic.MaximalReducedMonoidPrefix

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops m (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "R" => probeQuiver Q
local notation "hnR" => probeQuiver_no_loops Q hn

lemma probePositiveWord_eq_of_positive (J:Set S) (u v:List J)
    (h:wordPositive (restrictedMatrix M J) u=wordPositive (restrictedMatrix M J) v)
    (x:FiniteHomotopyClass R (K:=K)) : probePositiveWord M J u x=probePositiveWord M J v x := by
  apply probePositiveWord_eq_of_restricted M J u v
  have he:=congrArg (positiveToArtin (restrictedMatrix M J)) h
  simpa only [positiveToArtin_word] using he

theorem probe_positive_monoid_top_factor (J:Set S) (hJ:IsSpherical M J)
    (x:FiniteHomotopyClass R (K:=K)) (t:ℤ)
    (hx:ClassTestUpper R x (Set.range (probeCoreInclusion M J)) t)
    (w:List J) (j:J) (ℓ:ℤ) (hlt:t<ℓ)
    (hy:ClassTestUpper R (probePositiveWord M J w x) (Set.range (probeCoreInclusion M J)) ℓ)
    (L:FusionLabel m) (c:ℤ)
    (htop:¬ClassTestExact R (probeCoreInclusion M J (j,L)) ℓ c (probePositiveWord M J w x)) :
    ∃v:List J,wordPositive (restrictedMatrix M J) w=
      positiveGenerator (restrictedMatrix M J) j*wordPositive (restrictedMatrix M J) v ∧ v.length+1=w.length := by
  let N:=restrictedMatrix M J
  let U:=Set.range (probeCoreInclusion M J)
  induction w using (measure (fun w:List J=>w.length)).wf.induction generalizing j ℓ L c with
  | h w ih=>
    cases w with
    | nil=>exact (htop (hx _ ⟨(j,L),rfl⟩ ℓ hlt c)).elim
    | cons s w=>
      obtain ⟨u,v,hu,he,hlen,hpos,hmax⟩:=maximal_reduced_monoid_prefix N s w
      have heword:wordPositive N (s::w)=wordPositive N (u++v) := by
        rw [wordPositive_append]; exact he
      have heact:probePositiveWord M J (s::w) x=
          probePositiveWord M J u (probePositiveWord M J v x) := by
        rw [probePositiveWord_eq_of_positive M J _ _ heword,probePositiveWord_append]
      have hvsmall:v.length<(s::w).length:=by omega
      let y:=probePositiveWord M J v x
      have hcap:ClassTestUpper R y U ℓ := by
        apply probePositiveWord_testUpper_reflect M J u
        rw [←heact]
        exact hy
      by_cases hj:N.toCoxeterSystem.IsReduced (j::u)
      · have hncap:¬ClassTestUpper R y U (ℓ-1) := by
          intro hc
          apply htop
          rw [heact]
          exact probe_reduced_ascent_top_exact M J hJ u j hu hj y (ℓ-1) ℓ (by omega) hc
            (by rw [←heact]; exact hy) L c
        have htopv:∃γ:J,∃L' c',¬ClassTestExact R (probeCoreInclusion M J (γ,L')) ℓ c' y := by
          by_contra hh
          apply hncap
          intro α hα l hl c'
          obtain ⟨⟨γ,L'⟩,rfl⟩:=hα
          by_cases heq:l=ℓ
          · subst l
            by_contra hnot
            exact hh ⟨γ,L',c',hnot⟩
          · exact hcap _ ⟨(γ,L'),rfl⟩ l (by omega) c'
        obtain ⟨γ,L',c',hγ⟩:=htopv
        obtain ⟨v',hv',hvlen⟩:=ih v hvsmall γ ℓ hlt hcap L' c' hγ
        have huγ:N.toCoxeterSystem.IsReduced (u++[γ]) := by
          by_contra hnot
          obtain ⟨u',_,he',_⟩:=reduced_monoid_right_factor N u γ hu hnot
          have hea:probePositiveWord M J u y=
              probePositiveWord M J u' (sourceProbePacket M γ y) := by
            have hw:wordPositive N u=wordPositive N (u'++[γ]):=by
              rw [wordPositive_append]; exact he'
            rw [probePositiveWord_eq_of_positive M J _ _ hw,probePositiveWord_append]
            rfl
          have hγcap:ClassTestUpper R (sourceProbePacket M γ y) U ℓ := by
            apply probePositiveWord_testUpper_reflect M J u'
            rw [←hea,←heact]
            exact hy
          exact hγ (sourceProbePacket_top_exact_of_cap M J γ y hγcap L' c')
        have hext:wordPositive N (s::w)=wordPositive N (u++[γ])*wordPositive N v' := by
          rw [he,hv',wordPositive_append]
          exact (_root_.mul_assoc _ _ _).symm
        have hlxt:(u++[γ]).length+v'.length=(s::w).length := by
          simp only [List.length_append,List.length_singleton]
          omega
        have hh:=hmax (u++[γ]) v' huγ hext hlxt
        simp only [List.length_append,List.length_singleton] at hh
        omega
      · obtain ⟨u',_,he',hlen'⟩:=reduced_monoid_left_factor N u j hu hj
        refine ⟨u'++v,?_,?_⟩
        · rw [he,he',wordPositive_append,_root_.mul_assoc]
        · simp only [List.length_append]
          omega

end HarmonicArtin

end OAI
