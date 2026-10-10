import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ProbeCoreInclusion
import OAI.Topology.ArtinGroups.Complexes.PositiveWordActionOrthogonal
import OAI.Topology.ArtinGroups.Harmonic.RestrictedArtinHom
import OAI.Topology.ArtinGroups.Harmonic.MaximalReducedPositivePrefix

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

lemma probePositiveWord_append (J:Set S) (u v:List J) (x:FiniteHomotopyClass R (K:=K)) :
    probePositiveWord M J (u++v) x=probePositiveWord M J u (probePositiveWord M J v x) := by
  simp only [probePositiveWord,List.map_append,wordArtin_append,map_mul,Equiv.Perm.mul_apply]

lemma probePositiveWord_eq_of_restricted (J:Set S) (u v:List J)
    (h:wordArtin (restrictedMatrix M J) u=wordArtin (restrictedMatrix M J) v)
    (x:FiniteHomotopyClass R (K:=K)) : probePositiveWord M J u x=probePositiveWord M J v x := by
  have he:=congrArg (restrictedArtinHom M J) h
  rw [restrictedArtinHom_word,restrictedArtinHom_word] at he
  unfold probePositiveWord
  rw [he]

lemma sourceProbePacket_top_exact_of_cap (J:Set S) (j:J)
    (x:FiniteHomotopyClass R (K:=K)) {t:ℤ}
    (h:ClassTestUpper R (sourceProbePacket M j x) (Set.range (probeCoreInclusion M J)) t)
    (L:FusionLabel m) (c:ℤ) : ClassTestExact R (probeCoreInclusion M J (j,L)) t c x := by
  rw [sourceProbePacket_as_packet] at h
  exact classPacketPerm_testExact_of_cap R hnR _ _ (Set.range (probeCoreInclusion M J)) (fun L=>⟨(j,L),rfl⟩) x h L c

theorem probe_positive_top_factor (J:Set S) (hJ:IsSpherical M J)
    (x:FiniteHomotopyClass R (K:=K)) (t:ℤ)
    (hx:ClassTestUpper R x (Set.range (probeCoreInclusion M J)) t)
    (w:List J) (j:J) (ℓ:ℤ) (hlt:t<ℓ)
    (hy:ClassTestUpper R (probePositiveWord M J w x) (Set.range (probeCoreInclusion M J)) ℓ)
    (L:FusionLabel m) (c:ℤ)
    (htop:¬ClassTestExact R (probeCoreInclusion M J (j,L)) ℓ c (probePositiveWord M J w x)) :
    ∃v:List J,wordArtin (restrictedMatrix M J) w=
      generator (restrictedMatrix M J) j*wordArtin (restrictedMatrix M J) v ∧ v.length+1=w.length := by
  let N:=restrictedMatrix M J
  let U:=Set.range (probeCoreInclusion M J)
  induction w using (measure (fun w:List J=>w.length)).wf.induction generalizing j ℓ L c with
  | h w ih=>
    cases w with
    | nil=>exact (htop (hx _ ⟨(j,L),rfl⟩ ℓ hlt c)).elim
    | cons s w=>
      obtain ⟨u,v,hu,he,hlen,hpos,hmax⟩:=maximal_reduced_positive_prefix N s w
      have heword:wordArtin N (s::w)=wordArtin N (u++v) := by
        rw [wordArtin_append]; exact he
      have heact:probePositiveWord M J (s::w) x=
          probePositiveWord M J u (probePositiveWord M J v x) := by
        rw [probePositiveWord_eq_of_restricted M J _ _ heword,probePositiveWord_append]
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
          obtain ⟨u',hu',he',hlen'⟩:=reduced_right_factor N u γ hu hnot
          have hea:probePositiveWord M J u y=
              probePositiveWord M J u' (sourceProbePacket M γ y) := by
            have hw:wordArtin N u=wordArtin N (u'++[γ]):=by
              rw [wordArtin_append]; exact he'
            rw [probePositiveWord_eq_of_restricted M J _ _ hw,probePositiveWord_append]
            rfl
          have hγcap:ClassTestUpper R (sourceProbePacket M γ y) U ℓ := by
            apply probePositiveWord_testUpper_reflect M J u'
            rw [←hea,←heact]
            exact hy
          exact hγ (sourceProbePacket_top_exact_of_cap M J γ y hγcap L' c')
        have hext:wordArtin N (s::w)=wordArtin N (u++[γ])*wordArtin N v' := by
          rw [he,hv',wordArtin_append]
          exact (_root_.mul_assoc _ _ _).symm
        have hlxt:(u++[γ]).length+v'.length=(s::w).length := by
          simp only [List.length_append,List.length_singleton]
          omega
        have hh:=hmax (u++[γ]) v' huγ hext hlxt
        simp only [List.length_append,List.length_singleton] at hh
        omega
      · obtain ⟨u',hu',he',hlen'⟩:=reduced_left_factor N u j hu hj
        refine ⟨u'++v,?_,?_⟩
        · rw [he,he',wordArtin_append,_root_.mul_assoc]
        · simp only [List.length_append]
          omega

end HarmonicArtin

end OAI
