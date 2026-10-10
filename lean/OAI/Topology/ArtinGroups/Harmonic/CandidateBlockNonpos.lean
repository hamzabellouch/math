import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FoldedSphericalPos
import OAI.Topology.ArtinGroups.Harmonic.ProbeOrbitAbsent
import OAI.Topology.ArtinGroups.Complexes.LevelArrayBelow

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=ℂ)
local notation "C" => fusionFoldedCartan m d

lemma sourceCandidate_block_nonpos (T J:Set S) (z h:Artin M)
    (hh:h∈artinParabolic M T) (q:ℤ) (p:S⊕Unit→ℝ)
    (X:SourceCappedCandidate M T J z q p) (Y:SourceCappedCandidate M T J (h*z) q p)
    (s t:S) (hs:s∈T) (hsJ:s∉J) (ht:t∈T) (htJ:t∉J)
    (L H:FusionLabel m) (b:Bool) (l:ℤ) (hl:l≤0) :
    classLevelArray R (bw h⁻¹ (initialClass R (.inr ((.inl s,L),b)))) (.inl (.inl t,H),l)=0 := by
  let α:FusionVertex (V:=S⊕Unit) m:=(.inl s,L)
  let β:FusionVertex (V:=S⊕Unit) m:=(.inl t,H)
  obtain ⟨a,ha,hcap,hlower,hsoc⟩:=sourceProbe_zero_saturation M T J z h q p X hh
    (fun H i hi=>Y.cap H i (Or.inl hi))
    (fun _:Unit=>α) (fun _=>⟨(⟨s,hs⟩,L),rfl⟩) (fun _=>b)
  have haT:=artinParabolic_mono M X.subset ha
  have hg:(h*a⁻¹)∈artinParabolic M T:=
    (artinParabolic M T).mul_mem hh ((artinParabolic M T).inv_mem haT)
  have hei:(h*a⁻¹)⁻¹=a*h⁻¹:=by simp only [_root_.mul_inv_rev,inv_inv]
  have he:(h*a⁻¹)*(a*z)=h*z:=by simp only [_root_.mul_assoc,inv_mul_cancel_left]
  have hβ:β∉Set.range (unfoldedInclusion M J):=by
    rintro ⟨⟨j,_⟩,he⟩
    have hj:(j:S)=t:=Sum.inl.inj (congrArg Prod.fst he)
    exact htJ (hj ▸ j.property)
  rw [←sourceProbe_block_left M J a h⁻¹ ha α β hβ b l]
  rcases lt_or_eq_of_le hl with hl|rfl
  · exact classLevelArray_below R _ 0 l (hlower ()) hl (.inl β)
  · have hu:=(X.move a ha hcap).probe_euler (h*a⁻¹) hg α b 0 (by rw [hei]; exact hsoc ())
    have hα:(Sum.inl s:S⊕Unit)∉Sum.inl '' J:=by
      rintro ⟨j,hj,he⟩
      exact hsJ (Sum.inl.inj he ▸ hj)
    dsimp only at hu
    rw [ite_eq_left rfl,sub_zero,he,Y.exterior (.inl s) hα,hei] at hu
    by_contra hz
    have hn:0<classLevelArray R (bw (a*h⁻¹) (initialClass R (.inr (α,b)))) (.inl β,0):=Nat.pos_of_ne_zero hz
    let N:=((minimalClassModel R (bw (a*h⁻¹) (initialClass R (.inr (α,b))))).complex.pureLayer R
      (minimalClassModel_minimal R _) 0)
    have hp:0<generatorVector R N (.inl β):=by
      rw [generatorVector_minimalLayer]
      exact_mod_cast hn
    have hg':a*h⁻¹∈artinParabolic M T:=by rw [←hei];exact (artinParabolic M T).inv_mem hg
    have hterm:generatorVector R N (.inl β)*fusionFold m (C *ᵥ p) β<0:=
      mul_neg_of_pos_of_neg hp (mul_neg_of_pos_of_neg (fusionWeight_pos m (fusionLabelSize_ge_two M) H)
        (X.negative t ht htJ))
    have hdot:(fun γ=>generatorVector R N (.inl γ)) ⬝ᵥ fusionFold m (C *ᵥ p)<0:=by
      apply Finset.sum_neg' (fun γ _=>sourceProbe_core_term_nonpos M (K:=ℂ) T (a*h⁻¹) hg' α γ b 0 p X.cartan_nonpos)
      exact ⟨β,Finset.mem_univ _,hterm⟩
    change _-(fun γ=>generatorVector R N (.inl γ)) ⬝ᵥ fusionFold m (C *ᵥ p)≤_ at hu
    linarith

theorem sourceCandidate_zero_block (T J J':Set S) (hT:IsSpherical M T) (z h:Artin M)
    (hh:h∈artinParabolic M T) (q:ℤ) (p p':S⊕Unit→ℝ)
    (X:SourceCappedCandidate M T J z q p) (Y:SourceCappedCandidate M T J' (h*z) q p') :
    p=p' ∧ J=J' ∧ ∀s∈T,s∉J→∀t∈T,t∉J→∀L H b l,
      classLevelArray R (bw h (initialClass R (.inr ((.inl s,L),b)))) (.inl (.inl t,H),l)=0 := by
  obtain ⟨rfl,rfl⟩:=sourceCandidate_numerical_unique M T J J' hT z h hh q p p' X Y
  refine ⟨rfl,rfl,?_⟩
  intro s hs hsJ t ht htJ L H b l
  by_cases hl:l≤0
  · have hz:=sourceCandidate_block_nonpos M T J (h*z) h⁻¹ ((artinParabolic M T).inv_mem hh)
      q p Y (by simpa only [inv_mul_cancel_left] using X) s t hs hsJ ht htJ L H b l hl
    simpa only [inv_inv] using hz
  · rw [sourceProbe_level_dual M T h hh (.inl s,L) (.inl t,H) b l]
    exact sourceCandidate_block_nonpos M T J z h hh q p X Y t s ht htJ hs hsJ H L (!b) (-l) (by omega)

end HarmonicArtin

end OAI
