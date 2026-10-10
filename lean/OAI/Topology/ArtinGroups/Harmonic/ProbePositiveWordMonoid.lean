import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.InitialProbe
import OAI.Topology.ArtinGroups.Harmonic.ProbePositiveWordPositive

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M

lemma probePositiveWord_monoid_factor (T:Set S) (w v:List T) (j:T)
    (he:wordPositive (restrictedMatrix M T) w=
      positiveGenerator (restrictedMatrix M T) j*wordPositive (restrictedMatrix M T) v)
    (x:FiniteHomotopyClass (probeQuiver (fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M))) (K:=K)) :
    probePositiveWord M T w x=sourceProbePacket M j (probePositiveWord M T v x) := by
  have hw:wordPositive (restrictedMatrix M T) w=wordPositive (restrictedMatrix M T) (j::v):=he
  rw [probePositiveWord_eq_of_positive M T w (j::v) hw,probePositiveWord_cons]

theorem positive_monoid_eq_of_probe_eq (T:Set S) (hT:IsSpherical M T) (a b:List T)
    (he:∀s:T,∀L d,probePositiveWord M T a (sourceInitialProbe M (K:=K) s L d)=
        probePositiveWord M T b (sourceInitialProbe M (K:=K) s L d)) :
    wordPositive (restrictedMatrix M T) a=wordPositive (restrictedMatrix M T) b := by
  induction a using (measure (fun a:List T=>a.length)).wf.induction generalizing b with
  | h a ih=>
    cases a with
    | nil=>
      have hb:b=[]:=by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro s hs
        let L:FusionLabel m:=fun e=>⟨0,by have :=fusionLabelSize_ge_four M e;omega⟩
        have hc:ClassTestUpper _ (probePositiveWord M T [] (sourceInitialProbe M (K:=K) s L false))
            (Set.range (probeCoreInclusion M T)) 1:=by
          exact (probePositiveWord_initial_cap_iff M T [] s L false).mpr (by simp)
        rw [he s L false] at hc
        exact probePositiveWord_initial_cap_not_mem M T b s L false hc hs
      rw [hb]
    | cons s a=>
      let L:FusionLabel m:=fun e=>⟨0,by have :=fusionLabelSize_ge_four M e;omega⟩
      let x:=sourceInitialProbe M (K:=K) s L false
      obtain ⟨l,hl,hcap,j,H,c,htop⟩:=probePositiveWord_initial_top M T (s::a) s (by simp) L false (K:=K)
      have hx:=sourceInitialProbe_cap M (K:=K) T s L false
      obtain ⟨a',ha',halen⟩:=probe_positive_monoid_top_factor M T hT x 1 hx (s::a) j l hl hcap H c htop
      rw [he s L false] at hcap htop
      obtain ⟨b',hb',hblen⟩:=probe_positive_monoid_top_factor M T hT x 1 hx b j l hl hcap H c htop
      have he':∀s:T,∀L d,probePositiveWord M T a' (sourceInitialProbe M (K:=K) s L d)=
          probePositiveWord M T b' (sourceInitialProbe M (K:=K) s L d):=by
        intro t L d
        apply (sourceProbePacket M j).injective
        rw [←probePositiveWord_monoid_factor M T (s::a) a' j ha',←probePositiveWord_monoid_factor M T b b' j hb']
        exact he t L d
      have hi:=ih a' (show a'.length<(s::a).length by omega) b' he'
      rw [ha',hb',hi]

theorem spherical_positive_words_reflect (T:Set S) (hT:IsSpherical M T) (a b:List T)
    (he:wordArtin M (a.map Subtype.val)=wordArtin M (b.map Subtype.val)) :
    wordPositive (restrictedMatrix M T) a=wordPositive (restrictedMatrix M T) b := by
  apply positive_monoid_eq_of_probe_eq (K:=ℚ) M T hT a b
  intro s L d
  simp only [probePositiveWord,he]

theorem spherical_positiveToAmbient_injective (T:Set S) (hT:IsSpherical M T) :
    Function.Injective ((restrictedArtinHom M T).comp (positiveToArtin (restrictedMatrix M T))) := by
  intro a b hab
  obtain ⟨u,rfl⟩:=PresentedMonoid.surjective_mk a
  obtain ⟨v,rfl⟩:=PresentedMonoid.surjective_mk b
  have ha:PresentedMonoid.mk (positiveBraidRelations (restrictedMatrix M T)) u=
      wordPositive (restrictedMatrix M T) (FreeMonoid.toList u):=by rw [wordPositive_mk,FreeMonoid.ofList_toList]
  have hb:PresentedMonoid.mk (positiveBraidRelations (restrictedMatrix M T)) v=
      wordPositive (restrictedMatrix M T) (FreeMonoid.toList v):=by rw [wordPositive_mk,FreeMonoid.ofList_toList]
  rw [ha,hb] at hab ⊢
  apply spherical_positive_words_reflect M T hT
  simpa only [MonoidHom.comp_apply,positiveToArtin_word,restrictedArtinHom_word] using hab

end HarmonicArtin

end OAI
