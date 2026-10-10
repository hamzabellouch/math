import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FamilySocleFiniteTermination
import OAI.Topology.ArtinGroups.Harmonic.IsolatedIterationData
import OAI.Topology.ArtinGroups.Harmonic.IntegerUpward
import OAI.Topology.ArtinGroups.Harmonic.BottomWordNil
import OAI.Topology.ArtinGroups.Realizations.WeightedCounts

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {M:CoxeterMatrix S}
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag

namespace IsolatedIterationData
variable (D:IsolatedIterationData M)

theorem stage (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
    (b t:ℤ) (ht:t<D.q) (hb:∀ H,ClassLowerBound Q b (O z D.s H))
    (hp:∀ k,k<t→D.openSocle z k) :
    ∃ z',D.valid z' ∧ D.capped z' ∧
      (∀ H,ClassLowerBound Q b (O z' D.s H)) ∧
      (∀ k,k<t+1→D.openSocle z' k) := by
  let x:=fun H=>classLayer Q t (O z D.s H)
  have hx:∀ H,ClassLowerBound Q t (x H):=fun _=>
    classLowerBound_of_representative Q _ (fun index=>le_of_eq index.property.symm)
  let P:List D.J→Prop:=fun w=>∃ z',D.valid z' ∧ D.capped z' ∧
    (∀ H,ClassLowerBound Q b (O z' D.s H)) ∧
    (∀ k,k<t→D.openSocle z' k) ∧
    ∀ H,classLayer Q t (O z' D.s H)=sourceBottomWord M D.J t w (x H)
  have hP:P [] := by
    refine ⟨z,hz,hc,hb,hp,fun H=>?_⟩
    rw [sourceBottomWord_nil,classLayer_idempotent]
  have step:∀ w,(restrictedMatrix M D.J).toCoxeterSystem.IsReduced w→P w→
      ∀ j:D.J,(∃ H L c,0<classLayerSocleDimension Q t (.inl j,L) c
        (sourceBottomWord M D.J t w (x H)))→P (j::w) := by
    intro w _ hPw j hs
    obtain ⟨z',hz',hc',hb',hp',he⟩:=hPw
    have hs':∃ H L c,0<classLayerSocleDimension Q t (.inl j,L) c (O z' D.s H) := by
      obtain ⟨H,L,c,hs⟩:=hs
      rw [← he H,classLayerSocleDimension_layer] at hs
      exact ⟨H,L,c,hs⟩
    have hm:=D.stage_move z' hz' hc' j b t ht hb' hp' hs'
    refine ⟨((.inl j,true)::z'),D.move z' hz' j,hm.1,hm.2.1,hm.2.2.1,fun H=>?_⟩
    rw [hm.2.2.2 H,he H,sourceBottomWord_cons M D.J t (x H) (hx H)]
  obtain ⟨w,_,hPw,hs⟩:=source_family_socle_finite_termination M D.J D.hJ t x hx P hP step
  obtain ⟨z',hz',hc',hb',hp',he⟩:=hPw
  refine ⟨z',hz',hc',hb',fun k hk=>?_⟩
  by_cases hkt:k<t
  · exact hp' k hkt
  · have hkt:k=t:=by omega
    subst k
    intro H α hα c
    obtain ⟨j,hj,heα⟩:=hα
    have hf:α.1=.inl j:=heα.symm
    have hsc:=hs H ⟨j,hj⟩ α.2 c
    rw [← he H,classLayerSocleDimension_layer] at hsc
    have hαeq:(Sum.inl j,α.2)=α:=Prod.ext hf.symm rfl
    rwa [hαeq] at hsc

theorem saturate (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
    (b t:ℤ) (ht:t<D.q) (hb:∀ H,ClassLowerBound Q b (O z D.s H)) :
    ∃ z',D.valid z' ∧ D.capped z' ∧
      (∀ H,ClassLowerBound Q b (O z' D.s H)) ∧ D.openSocle z' t := by
  let P:ℤ→Prop:=fun k=>∃ z',D.valid z' ∧ D.capped z' ∧
    (∀ H,ClassLowerBound Q b (O z' D.s H)) ∧ (∀ l,l<k+1→D.openSocle z' l)
  have hP:∀ k,k<t+1→P k := by
    refine integer_upward (P:=P) b (t+1) ?_ ?_
    · intro k hk
      exact ⟨z,hz,hc,hb,fun l hl=>D.socle_below z b l hb (by omega)⟩
    · intro k _ hkt hp
      obtain ⟨z',hz',hc',hb',hp'⟩:=hp
      apply D.stage z' hz' hc' b k (by omega) hb'
      intro l hl
      exact hp' l (by omega)
  obtain ⟨z',hz',hc',hb',hp'⟩:=hP t (by omega)
  exact ⟨z',hz',hc',hb',hp' t (by omega)⟩

end IsolatedIterationData
end HarmonicArtin

end OAI
