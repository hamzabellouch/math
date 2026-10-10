import Mathlib
import OAI.Topology.ArtinGroups.Complexes.ComplexPacketLowerBound
import OAI.Topology.ArtinGroups.Harmonic.ArtinActionWordArtin
import OAI.Topology.ArtinGroups.Complexes.LayerSocleDimensionLayer

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "aw" => sourceArtinAction M (K:=K)
local notation "T" => fusionPacketPerm m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (K:=K)

noncomputable def sourcePositiveWord (J:Set S) (w:List J)
    (x:FiniteHomotopyClass Q (K:=K)) : FiniteHomotopyClass Q (K:=K) :=
  aw (wordArtin M (w.map Subtype.val)) x

noncomputable def sourceBottomWord (J:Set S) (q:ℤ) (w:List J)
    (x:FiniteHomotopyClass Q (K:=K)) : FiniteHomotopyClass Q (K:=K) :=
  classLayer Q q (sourcePositiveWord M J w x)

lemma sourcePositiveWord_cons (J:Set S) (j:J) (w:List J) (x:FiniteHomotopyClass Q (K:=K)) :
    sourcePositiveWord M J (j::w) x=T (.inl j) (sourcePositiveWord M J w x) := by
  simp only [sourcePositiveWord,List.map_cons,wordArtin,List.map_cons,List.prod_cons,map_mul,
    sourceArtinAction_generator,Equiv.Perm.mul_apply]

lemma sourcePositiveWord_lowerBound (J:Set S) (w:List J) (x:FiniteHomotopyClass Q (K:=K))
    (q:ℤ) (hx:ClassLowerBound Q q x) :
    ClassLowerBound Q q (sourcePositiveWord M J w x) := by
  unfold sourcePositiveWord
  rw [sourceArtinAction_positiveWord]
  exact positiveWord_lower_bound Q _ x hx

lemma sourcePositiveWord_reduced_eq (J:Set S) (u v:List J)
    (hu:(restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (hv:(restrictedMatrix M J).toCoxeterSystem.IsReduced v)
    (he:(restrictedMatrix M J).toCoxeterSystem.wordProd u=
      (restrictedMatrix M J).toCoxeterSystem.wordProd v)
    (x:FiniteHomotopyClass Q (K:=K)) : sourcePositiveWord M J u x=sourcePositiveWord M J v x := by
  let f:J→Equiv.Perm (FiniteHomotopyClass Q (K:=K)):=fun j=>T (.inl j)
  have hb:∀ i j:J,((altList i j (restrictedMatrix M J i j)).map f).prod=
      ((altList j i (restrictedMatrix M J i j)).map f).prod := by
    intro i j
    have hh:=sourcePacket_braid M (K:=K) i j
    simpa only [← altList_map,List.map_map,Function.comp_def,restrictedMatrix_apply,f] using hh
  have hh:=reduced_word_property (restrictedMatrix M J).toCoxeterSystem f hb u v hu hv he
  have hperm:aw (wordArtin M (u.map Subtype.val))=aw (wordArtin M (v.map Subtype.val)) := by
    simpa only [wordArtin,map_list_prod,List.map_map,sourceArtinAction_generator,Function.comp_def,f] using hh
  exact congrArg (fun p=>p x) hperm

lemma sourceBottomWord_cons_socle_zero (J:Set S) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K))
    (hx:ClassLowerBound Q q x) (j:J) (w:List J) (L:FusionLabel m) (c:ℤ) :
    classLayerSocleDimension Q q (.inl j,L) c (sourceBottomWord M J q (j::w) x)=0 := by
  rw [sourceBottomWord,classLayerSocleDimension_layer,sourcePositiveWord_cons]
  convert classPacketPerm_bottom_socle_zero Q hn (fun L:FusionLabel m=>(Sum.inl (j:S),L))
    (fusionColor_orthogonal m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (.inl j))
    (sourcePositiveWord M J w x) (sourcePositiveWord_lowerBound M J w x q hx) L c using 1
  congr 9

theorem sourceBottomWord_socle_ascent (J:Set S) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K))
    (hx:ClassLowerBound Q q x) (w:List J)
    (hw:(restrictedMatrix M J).toCoxeterSystem.IsReduced w) (j:J)
    (hs:∃ L c,0<classLayerSocleDimension Q q (.inl j,L) c (sourceBottomWord M J q w x)) :
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
    have he:=sourcePositiveWord_reduced_eq M J w (j::v) hw hred hprod.symm x
    obtain ⟨L,c,hsc⟩:=hs
    have hval:sourceBottomWord M J q w x=sourceBottomWord M J q (j::v) x := congrArg (classLayer Q q) he
    rw [hval,sourceBottomWord_cons_socle_zero M J q x hx j v L c] at hsc
    exact (Nat.lt_irrefl 0) hsc
  change cs.length (cs.simple j*cs.wordProd w)=w.length+1
  rw [cs.not_isLeftDescent_iff.mp ha,hw.eq]

lemma bounded_word_saturation {R:Type*} (B:ℕ) (good inv:List R→Prop)
    (move:List R→R→Prop) (hgood:good []) (hinv:inv [])
    (bound:∀ w,good w→w.length≤B)
    (extend:∀ w,good w→∀ j,move w j→ good (j::w))
    (preserve:∀ w,good w→inv w→∀ j,move w j→inv (j::w)) :
    ∃ w,good w ∧ inv w ∧ ∀ j,¬move w j := by
  classical
  have go:∀ n:ℕ,∀ w:List R,B-w.length=n→ good w→inv w→
      ∃ v,good v ∧ inv v ∧ ∀ j,¬move v j := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih=>
      intro w hm hw hv
      by_cases hz:∀ j,¬move w j
      · exact ⟨w,hw,hv,hz⟩
      · push Not at hz
        obtain ⟨j,hj⟩:=hz
        have hw':=extend w hw j hj
        have hb:=bound (j::w) hw'
        have hlt:B-(j::w).length<n := by simp only [List.length_cons] at hb ⊢; omega
        exact ih _ hlt (j::w) rfl hw' (preserve w hw hv j hj)
  exact go B [] (by simp) hgood hinv

theorem source_socle_finite_termination (J:Set S) (hJ:IsSpherical M J) (q:ℤ)
    (x:FiniteHomotopyClass Q (K:=K)) (hx:ClassLowerBound Q q x)
    (P:List J→Prop) (hP:P [])
    (step:∀ w,(restrictedMatrix M J).toCoxeterSystem.IsReduced w→P w→
      ∀ j:J,(∃ L c,0<classLayerSocleDimension Q q (.inl j,L) c (sourceBottomWord M J q w x))→P (j::w)) :
    ∃ w:List J,(restrictedMatrix M J).toCoxeterSystem.IsReduced w ∧ P w ∧
      ∀ j:J,∀ L c,classLayerSocleDimension Q q (.inl j,L) c (sourceBottomWord M J q w x)=0 := by
  let:Finite (restrictedMatrix M J).Group:=restricted_finite M J hJ
  let:=Fintype.ofFinite (restrictedMatrix M J).Group
  let cs:=(restrictedMatrix M J).toCoxeterSystem
  let B:=Finset.univ.sup cs.length
  have bound (w:List J) (hw:cs.IsReduced w) : w.length≤B := by
    rw [← hw.eq]
    exact Finset.le_sup (f:=cs.length) (Finset.mem_univ _)
  let move:List J→J→Prop:=fun w j=>
    ∃ L c,0<classLayerSocleDimension Q q (.inl j,L) c (sourceBottomWord M J q w x)
  obtain ⟨w,hw,hp,hz⟩:=bounded_word_saturation B cs.IsReduced P move
    (by simp [cs,CoxeterSystem.IsReduced]) hP bound
    (fun w hw j hj=>sourceBottomWord_socle_ascent M J q x hx w hw j hj) step
  refine ⟨w,hw,hp,?_⟩
  intro j L c
  apply Nat.eq_zero_of_not_pos
  intro hc
  exact hz j ⟨L,c,hc⟩

end HarmonicArtin

end OAI
