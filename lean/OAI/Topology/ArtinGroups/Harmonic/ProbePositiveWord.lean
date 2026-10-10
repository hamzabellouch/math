import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ProbePacket
import OAI.Topology.ArtinGroups.Harmonic.PositiveWord

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "R" => probeQuiver Q
local notation "hnR" => probeQuiver_no_loops Q hn

lemma sourceProbePacket_as_packet (s:S) :
    sourceProbePacket M (K:=K) s=classPacketPerm R hnR
      (fun L:FusionLabel m=>Sum.inl (Sum.inl s,L))
      (fun _ _ hab=>probe_orthogonal Q
        (fusionColor_orthogonal m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
          (.inl s) hab)) := by
  unfold sourceProbePacket fusionExpandedWord
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_map,Function.comp_def]
  convert classPacketPerm_toList R (K:=K) hnR (fun L:FusionLabel m=>Sum.inl (Sum.inl s,L))
    (fun _ _ hab=>probe_orthogonal Q
      (fusionColor_orthogonal m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
        (.inl s) hab)) using 1

noncomputable def probePositiveWord (J:Set S) (w:List J)
    (x:FiniteHomotopyClass R (K:=K)) : FiniteHomotopyClass R (K:=K) :=
  sourceProbeAction M (wordArtin M (w.map Subtype.val)) x

noncomputable def probeBottomWord (J:Set S) (q:ℤ) (w:List J)
    (x:FiniteHomotopyClass R (K:=K)) : FiniteHomotopyClass R (K:=K) :=
  classLayer R q (probePositiveWord M J w x)

lemma probePositiveWord_cons (J:Set S) (j:J) (w:List J) (x:FiniteHomotopyClass R (K:=K)) :
    probePositiveWord M J (j::w) x=sourceProbePacket M j (probePositiveWord M J w x) := by
  simp only [probePositiveWord,List.map_cons,wordArtin,List.prod_cons,map_mul,
    sourceProbeAction_generator,Equiv.Perm.mul_apply]

lemma probePositiveWord_expanded (J:Set S) (w:List J) (x:FiniteHomotopyClass R (K:=K)) :
    probePositiveWord M J w x=positiveWordAction R
      ((fusionExpandedWord m ((w.map Subtype.val).map Sum.inl)).map Sum.inl) x := by
  rw [positiveWordAction_eq_prod R hnR]
  unfold probePositiveWord wordArtin
  simp only [map_list_prod,List.map_map,sourceProbeAction_generator,Function.comp_def]
  have h:=sourceProbeWord_expand M (K:=K) (w.map Subtype.val)
  apply congrArg (fun p:Equiv.Perm (FiniteHomotopyClass R (K:=K))=>p x)
  simpa only [List.map_map, Function.comp_def] using h

lemma probePositiveWord_lowerBound (J:Set S) (w:List J) (x:FiniteHomotopyClass R (K:=K))
    (q:ℤ) (hx:ClassLowerBound R q x) :
    ClassLowerBound R q (probePositiveWord M J w x) := by
  rw [probePositiveWord_expanded]
  exact positiveWord_lower_bound R _ x hx

lemma probePositiveWord_reduced_eq (J:Set S) (u v:List J)
    (hu:(restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (hv:(restrictedMatrix M J).toCoxeterSystem.IsReduced v)
    (he:(restrictedMatrix M J).toCoxeterSystem.wordProd u=
      (restrictedMatrix M J).toCoxeterSystem.wordProd v)
    (x:FiniteHomotopyClass R (K:=K)) : probePositiveWord M J u x=probePositiveWord M J v x := by
  let f:J→Equiv.Perm (FiniteHomotopyClass R (K:=K)):=fun j=>sourceProbePacket M j
  have hb:∀ i j:J,((altList i j (restrictedMatrix M J i j)).map f).prod=
      ((altList j i (restrictedMatrix M J i j)).map f).prod := by
    intro i j
    have hh:=sourceProbePacket_braid M (K:=K) i j
    simpa only [← altList_map,List.map_map,Function.comp_def,restrictedMatrix_apply,f] using hh
  have hh:=reduced_word_property (restrictedMatrix M J).toCoxeterSystem f hb u v hu hv he
  have hperm:sourceProbeAction M (K:=K) (wordArtin M (u.map Subtype.val))=
      sourceProbeAction M (K:=K) (wordArtin M (v.map Subtype.val)) := by
    simpa only [wordArtin,map_list_prod,List.map_map,sourceProbeAction_generator,Function.comp_def,f] using hh
  exact congrArg (fun p=>p x) hperm

lemma probeBottomWord_cons_socle_zero (J:Set S) (q:ℤ) (x:FiniteHomotopyClass R (K:=K))
    (hx:ClassLowerBound R q x) (j:J) (w:List J) (L:FusionLabel m) (c:ℤ) :
    classLayerSocleDimension R q (.inl (.inl j,L)) c (probeBottomWord M J q (j::w) x)=0 := by
  rw [probeBottomWord,classLayerSocleDimension_layer,probePositiveWord_cons,sourceProbePacket_as_packet]
  exact classPacketPerm_bottom_socle_zero R hnR
    (fun L:FusionLabel m=>Sum.inl (Sum.inl (j:S),L))
    (fun a b hab=>probe_orthogonal Q
      (fusionColor_orthogonal m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (.inl j) hab))
    (probePositiveWord M J w x) (probePositiveWord_lowerBound M J w x q hx) L c

theorem probeBottomWord_socle_ascent (J:Set S) (q:ℤ) (x:FiniteHomotopyClass R (K:=K))
    (hx:ClassLowerBound R q x) (w:List J)
    (hw:(restrictedMatrix M J).toCoxeterSystem.IsReduced w) (j:J)
    (hs:∃ L c,0<classLayerSocleDimension R q (.inl (.inl j,L)) c (probeBottomWord M J q w x)) :
    (restrictedMatrix M J).toCoxeterSystem.IsReduced (j::w) := by
  let cs:=(restrictedMatrix M J).toCoxeterSystem
  have ha:¬cs.IsLeftDescent (cs.wordProd w) j := by
    intro hj
    obtain ⟨v,hv,hev⟩:=cs.exists_isReduced (cs.simple j*cs.wordProd w)
    have hprod:cs.wordProd (j::v)=cs.wordProd w := by
      rw [CoxeterSystem.wordProd_cons,← hev,cs.simple_mul_simple_cancel_left]
    have hred:cs.IsReduced (j::v) := by
      change cs.length (cs.wordProd (j::v))=v.length+1
      rw [hprod,← hv.eq,← hev]
      exact (cs.isLeftDescent_iff.mp hj).symm
    have he:=probePositiveWord_reduced_eq M J w (j::v) hw hred hprod.symm x
    obtain ⟨L,c,hsc⟩:=hs
    have hval:probeBottomWord M J q w x=probeBottomWord M J q (j::v) x := congrArg (classLayer R q) he
    rw [hval,probeBottomWord_cons_socle_zero M J q x hx j v L c] at hsc
    exact (Nat.lt_irrefl 0) hsc
  change cs.length (cs.simple j*cs.wordProd w)=w.length+1
  rw [cs.not_isLeftDescent_iff.mp ha,hw.eq]

theorem probe_family_socle_finite_termination {B:Type*}
    (J:Set S) (hJ:IsSpherical M J) (q:ℤ)
    (x:B→FiniteHomotopyClass R (K:=K)) (hx:∀ r,ClassLowerBound R q (x r))
    (P:List J→Prop) (hP:P [])
    (step:∀ w,(restrictedMatrix M J).toCoxeterSystem.IsReduced w→P w→
      ∀ j:J,(∃ r L c,0<classLayerSocleDimension R q (.inl (.inl j,L)) c
        (probeBottomWord M J q w (x r)))→P (j::w)) :
    ∃ w:List J,(restrictedMatrix M J).toCoxeterSystem.IsReduced w ∧ P w ∧
      ∀ r (j:J) L c,classLayerSocleDimension R q (.inl (.inl j,L)) c
        (probeBottomWord M J q w (x r))=0 := by
  let:Finite (restrictedMatrix M J).Group:=restricted_finite M J hJ
  let:=Fintype.ofFinite (restrictedMatrix M J).Group
  let cs:=(restrictedMatrix M J).toCoxeterSystem
  let B:=Finset.univ.sup cs.length
  let move:List J→J→Prop:=fun w j=>∃ r L c,
    0<classLayerSocleDimension R q (.inl (.inl j,L)) c (probeBottomWord M J q w (x r))
  have bound (w:List J) (hw:cs.IsReduced w) : w.length≤B := by
    rw [← hw.eq]
    exact Finset.le_sup (f:=cs.length) (Finset.mem_univ _)
  have extend (w:List J) (hw:cs.IsReduced w) (j:J) (hj:move w j) : cs.IsReduced (j::w) := by
    obtain ⟨r,L,c,h⟩:=hj
    exact probeBottomWord_socle_ascent M J q (x r) (hx r) w hw j ⟨L,c,h⟩
  obtain ⟨w,hw,hp,hz⟩:=bounded_word_saturation B cs.IsReduced P move
    (by simp [cs,CoxeterSystem.IsReduced]) hP bound extend step
  refine ⟨w,hw,hp,?_⟩
  intro r j L c
  apply Nat.eq_zero_of_not_pos
  intro hc
  exact hz j ⟨r,L,c,hc⟩

end HarmonicArtin

end OAI
