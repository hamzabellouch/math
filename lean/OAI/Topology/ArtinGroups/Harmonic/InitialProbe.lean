import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ProbePositiveWordInitial
import OAI.Topology.ArtinGroups.Complexes.PositiveWordActionTest
import OAI.Topology.ArtinGroups.Harmonic.FusionZeroLabel

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "hnR" => probeQuiver_no_loops Q (fusionQuiver_no_loops m (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M))

noncomputable abbrev sourceInitialProbe (s:S) (L:FusionLabel m) (b:Bool) : FiniteHomotopyClass R (K:=K) :=
  initialClass R (.inr ((.inl s,L),b))

lemma sourceInitialProbe_cap (T:Set S) (s:S) (L:FusionLabel m) (b:Bool) :
    ClassTestUpper R (sourceInitialProbe M (K:=K) s L b) (Set.range (probeCoreInclusion M T)) 1 :=
  initialProbe_test_upper Q _ b _ (by rintro _ ⟨α,rfl⟩; exact ⟨_,rfl⟩)

lemma probePositiveWord_initial_top (T:Set S) (w:List T) (s:T) (hs:s∈w)
    (L:FusionLabel m) (b:Bool) :
    ∃l:ℤ,1<l ∧ ClassTestUpper R (probePositiveWord M T w (sourceInitialProbe M (K:=K) s L b))
      (Set.range (probeCoreInclusion M T)) l ∧
      ∃j:T,∃H c,¬ClassTestExact R (probeCoreInclusion M T (j,H)) l c
        (probePositiveWord M T w (sourceInitialProbe M (K:=K) s L b)) := by
  have he:∃n:ℕ,ClassTestUpper R (probePositiveWord M T w (sourceInitialProbe M (K:=K) s L b))
      (Set.range (probeCoreInclusion M T)) (1+n) := by
    rw [probePositiveWord_core_expanded]
    exact ⟨_,positiveWordAction_testUpper R hnR _ _ _ (probeCore_word_support M T w)
      1 (sourceInitialProbe_cap M T s L b)⟩
  have hn:¬ClassTestUpper R (probePositiveWord M T w (sourceInitialProbe M (K:=K) s L b))
      (Set.range (probeCoreInclusion M T)) 1 := by
    intro h
    exact probePositiveWord_initial_cap_not_mem M T w s L b h hs
  obtain ⟨l,hl,hcap,α,⟨⟨j,H⟩,rfl⟩,c,hc⟩:=exists_top_test R _ _ 1 he hn
  exact ⟨l,hl,hcap,j,H,c,hc⟩

lemma probePositiveWord_factor (T:Set S) (w v:List T) (j:T)
    (he:wordArtin (restrictedMatrix M T) w=
      generator (restrictedMatrix M T) j*wordArtin (restrictedMatrix M T) v)
    (x:FiniteHomotopyClass R (K:=K)) :
    probePositiveWord M T w x=sourceProbePacket M j (probePositiveWord M T v x) := by
  have hw:wordArtin (restrictedMatrix M T) w=wordArtin (restrictedMatrix M T) (j::v):=he
  rw [probePositiveWord_eq_of_restricted M T w (j::v) hw,probePositiveWord_cons]

theorem positive_equal_probe_fraction (T:Set S) (hT:IsSpherical M T) (V:Set S)
    (a b:List T)
    (he:∀s:T,(s:S)∈V→∀L d,
      probePositiveWord M T a (sourceInitialProbe M (K:=K) s L d)=
        probePositiveWord M T b (sourceInitialProbe M (K:=K) s L d)) :
    ∃u v:List T,(∀s∈u,(s:S)∉V) ∧ (∀s∈v,(s:S)∉V) ∧
      (wordArtin (restrictedMatrix M T) a)⁻¹*wordArtin (restrictedMatrix M T) b=
        (wordArtin (restrictedMatrix M T) u)⁻¹*wordArtin (restrictedMatrix M T) v := by
  let N:=restrictedMatrix M T
  induction a using (measure (fun a:List T=>a.length)).wf.induction generalizing b with
  | h a ih=>
    by_cases ha:∀s∈a,(s:S)∉V
    · refine ⟨a,b,ha,?_,rfl⟩
      intro s hs hsV
      let L:FusionLabel m:=fusionZeroLabel m
        (fun edge=>le_trans (by norm_num) (fusionLabelSize_ge_four M edge))
      have has:s∉a:=fun hs=>ha s hs hsV
      have hc:ClassTestUpper R (probePositiveWord M T a (sourceInitialProbe M (K:=K) s L false))
          (Set.range (probeCoreInclusion M T)) 1 := (probePositiveWord_initial_cap_iff M T a s L false).mpr has
      rw [he s hsV L false] at hc
      exact probePositiveWord_initial_cap_not_mem M T b s L false hc hs
    · simp only [not_forall,Classical.not_not] at ha
      obtain ⟨s,hs,hsV⟩:=ha
      let L:FusionLabel m:=fusionZeroLabel m
        (fun edge=>le_trans (by norm_num) (fusionLabelSize_ge_four M edge))
      let x:FiniteHomotopyClass R (K:=K):=sourceInitialProbe M (K:=K) s L false
      obtain ⟨l,hl,hcap,j,H,c,htop⟩:=probePositiveWord_initial_top M T a s hs L false (K:=K)
      have hx:ClassTestUpper R x (Set.range (probeCoreInclusion M T)) 1:=sourceInitialProbe_cap M T s L false
      obtain ⟨a',ha',hlen⟩:=probe_positive_top_factor M T hT x 1 hx a j l hl hcap H c htop
      have heab:probePositiveWord M T a x=probePositiveWord M T b x:=he s hsV L false
      rw [heab] at hcap htop
      obtain ⟨b',hb',hblen⟩:=probe_positive_top_factor M T hT x 1 hx b j l hl hcap H c htop
      have he':∀s:T,(s:S)∈V→∀L d,
          probePositiveWord M T a' (sourceInitialProbe M (K:=K) s L d)=
            probePositiveWord M T b' (sourceInitialProbe M (K:=K) s L d) := by
        intro s hs L d
        apply (sourceProbePacket M j).injective
        rw [←probePositiveWord_factor M T a a' j ha',←probePositiveWord_factor M T b b' j hb']
        exact he s hs L d
      obtain ⟨u,v,hu,hv,hfrac⟩:=ih a' (show a'.length<a.length by omega) b' he'
      refine ⟨u,v,hu,hv,?_⟩
      rw [←hfrac,ha',hb']
      group

end HarmonicArtin

end OAI
