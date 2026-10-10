import Mathlib
import OAI.Topology.ArtinGroups.Geometry.ConvexInclusion
import OAI.Topology.ArtinGroups.Functors.GeneratorVectorComplex
import OAI.Topology.ArtinGroups.Harmonic.ProbeActionEmbeddedHom
import OAI.Topology.ArtinGroups.Complexes.FamilySubobjectMiddleLower

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open ReversibleQuiver.ProbeEmbedding _root_.Matrix _root_.OAI.Matrix CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "R" => probeQuiver Q
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "aw" => sourceArtinAction M (K:=ℂ)
local notation "bw" => sourceProbeAction M (K:=ℂ)

lemma sourceProbe_convex_euler
    (J:Set S) (hJ:IsSpherical M J) (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit)
    (q:ℤ) (p:S⊕Unit→ℝ)
    (hconvex:(μ z s q-p)∈convexHull ℝ (Set.range (sourceConvexVector M J z s q)))
    (g:Artin M) (α:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ)
    (hsoc:∀j:J,∀L c,coefficientSocle R
      ((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
        (minimalClassModel_minimal R _) l) (.inl (.inl (j:S),L)) c=⊥) :
    let N:=((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
      (minimalClassModel_minimal R _) l);
    -(generatorVector R N ⬝ᵥ (unfoldedCartan R *ᵥ Sum.elim (fusionFold m p) (fun _=>0)))≤
      ∑H,fusionWeight m H*(classLevelArray Q (aw g (O z s H)) (α,q-l):ℝ) := by
  dsimp only
  let N:=((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
    (minimalClassModel_minimal R _) l)
  let E:(S⊕Unit→ℝ)→ₗ[ℝ](ProbeVertex (FusionVertex (V:=S⊕Unit) m)→ℝ):=
    { toFun:=fun v=>Sum.elim (fusionFold m v) (fun _=>0)
      map_add':=by intro x y; funext v; cases v <;> simp [fusionFold,_root_.mul_add]
      map_smul':=by intro r x; funext v; cases v <;> simp [fusionFold,_root_.mul_left_comm] }
  let B:= (restrictedMatrix M J).Group
  let F:B→FusionLabel m→FiniteModel R (K:=ℂ):=fun w H=>
    FiniteModel.ofComplex R (complex Q (sourceConvexModel M J z s q w H).complex)
  let D:FusionLabel m→FiniteModel R (K:=ℂ):=fun H=>FiniteModel.ofComplex R (complex Q (Y z s H q))
  have hsum (w:B):(∑H,fusionWeight m H • generatorVector R (F w H).complex)=
      E (sourceConvexVector M J z s q w) := by
    change (∑H,fusionWeight m H • generatorVector R (complex Q (sourceConvexModel M J z s q w H).complex))=_
    simp_rw [generatorVector_complex]
    have hh:=sourceConvexModel_counts M J hJ z s q w
    funext v
    cases v with
    | inl v=>simpa [E,fusionOrbitWeightedVector] using congrFun hh v
    | inr v=>simp [E]
  have hD:(∑H,fusionWeight m H • generatorVector R (D H).complex)=E (μ z s q) := by
    change (∑H,fusionWeight m H • generatorVector R (complex Q (Y z s H q)))=_
    simp_rw [generatorVector_complex]
    have hh:=fusionOrbitWeightedVector_eq m d hd hdiag hm z s q
    funext v
    cases v with
    | inl v=>simpa [E,fusionOrbitWeightedVector] using congrFun hh v
    | inr v=>simp [E]
  have he:E (μ z s q-p)∈convexHull ℝ (Set.range (fun w=>∑H,fusionWeight m H • generatorVector R (F w H).complex)) := by
    have hh:E (μ z s q-p)∈E '' convexHull ℝ (Set.range (sourceConvexVector M J z s q)):=⟨_,hconvex,rfl⟩
    rw [E.image_convexHull,← Set.range_comp] at hh
    simpa only [hsum,Function.comp_def] using hh
  have hh:=family_subobject_middle_lower_bound R D N
    (fun H i=>i.property) (fun i=>i.property) F
    (fun w H i=>sourceConvexModel_pure M J hJ z s q w H i)
    (fun w H=>termwiseSplitInjection Q (sourceConvexActualInclusion M J hJ z s q w H))
    (Sum.inl '' Set.range (unfoldedInclusion M J))
    (fun w H i=>⟨_,sourceConvexModel_support M J z s q w H i,rfl⟩)
    (by
      rintro β ⟨γ,⟨⟨j,L⟩,rfl⟩,rfl⟩ c
      exact hsoc j L c)
    (fusionWeight m) (fun H=>(fusionWeight_pos m hm H).le) (E (μ z s q-p)) he
  rw [hD,map_sub,sub_sub_cancel_left] at hh
  simp only [mulVec_neg,dotProduct_neg] at hh
  refine hh.trans ?_
  apply Finset.sum_le_sum
  intro H hH
  apply mul_le_mul_of_nonneg_left _ (fusionWeight_pos m hm H).le
  have hi:=sourceProbeAction_layer_middle_le M g (minimalClassModel Q (O z s H)).complex
    (minimalClassModel_minimal Q _) α b l q
  have hx:classOfComplex Q (minimalClassModel Q (O z s H)).complex=O z s H:=minimalClassModel_class Q _
  have hid : (minimalClassModel Q (O z s H)).decidableEq =
      Classical.decEq (minimalClassModel Q (O z s H)).Index := Subsingleton.elim _ _
  rw [hid] at hx
  have heq:=congrArg (fun x:FiniteHomotopyClass Q (K:=ℂ)=>classLevelArray Q (aw g x) (α,q-l)) hx
  have hfin:=hi.trans_eq heq
  exact_mod_cast hfin

end HarmonicArtin

end OAI
