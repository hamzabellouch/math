import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PacketWord
import OAI.Topology.ArtinGroups.Harmonic.ProbeActionLevelExterior
import OAI.Topology.ArtinGroups.Complexes.GeneratorVectorPos

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=K)
local notation "C" => fusionFoldedCartan m d

lemma sourceProbe_core_term_nonpos (T:Set S) (g:Artin M) (hg:g∈artinParabolic M T)
    (α β:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ) (p:S⊕Unit→ℝ)
    (hp:∀s∈T,(C *ᵥ p) (.inl s)≤0) :
    let N:=((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.pureLayer R
      (minimalClassModel_minimal R _) l);
    generatorVector R N (.inl β)*fusionFold m (C *ᵥ p) β≤0 := by
  dsimp only
  by_cases hb:β∈Set.range (unfoldedInclusion M T)
  · obtain ⟨⟨s,L⟩,rfl⟩:=hb
    apply mul_nonpos_of_nonneg_of_nonpos (generatorVector_nonneg R _ _)
    exact mul_nonpos_of_nonneg_of_nonpos (fusionWeight_pos m (fusionLabelSize_ge_two M) L).le
      (hp s s.property)
  · rw [sourceProbeOrbit_core_vector_off M T g hg α β b l hb,MulZeroClass.zero_mul]

lemma sourceProbe_core_dot_nonpos (T:Set S) (g:Artin M) (hg:g∈artinParabolic M T)
    (α:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ) (p:S⊕Unit→ℝ)
    (hp:∀s∈T,(C *ᵥ p) (.inl s)≤0) :
    let N:=((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.pureLayer R
      (minimalClassModel_minimal R _) l);
    (fun β=>generatorVector R N (.inl β)) ⬝ᵥ fusionFold m (C *ᵥ p)≤0 := by
  apply Finset.sum_nonpos
  intro β _
  exact sourceProbe_core_term_nonpos M T g hg α β b l p hp

lemma sourceProbe_core_dot_neg_of_nonempty (T J:Set S)
    (g:Artin M) (hg:g∈artinParabolic M T)
    (α:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ) (hl:l≠0) (p:S⊕Unit→ℝ)
    (hp:∀s∈T,(C *ᵥ p) (.inl s)≤0)
    (hneg:∀s∈T,s∉J→(C *ᵥ p) (.inl s)<0)
    (hsoc:∀j:J,∀L c,coefficientSocle R
      ((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.pureLayer R
        (minimalClassModel_minimal R _) l) (.inl (.inl (j:S),L)) c=⊥)
    (hN:Nonempty {i:(minimalClassModel R (bw g (initialClass R (.inr (α,b))))).Index //
      (((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.placement i).level=l)}) :
    let N:=((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.pureLayer R
      (minimalClassModel_minimal R _) l);
    (fun β=>generatorVector R N (.inl β)) ⬝ᵥ fusionFold m (C *ᵥ p)<0 := by
  dsimp only
  let N:=((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.pureLayer R
      (minimalClassModel_minimal R _) l)
  rcases hN with ⟨i₀⟩
  obtain ⟨i,_,hmax⟩:=Finset.exists_max_image Finset.univ (fun i=>(N.placement i).cochain) ⟨i₀,Finset.mem_univ _⟩
  have hs:=coefficientSocle_nonzero_at_max R N i (fun j=>hmax j (Finset.mem_univ j))
  have hpos:=generatorVector_pos_at R N i
  cases he:(N.placement i).color with
  | inr γ =>
    rcases γ with ⟨β,c⟩
    rw [he,sourceProbeOrbit_leaf_vector M T g hg α β b c l] at hpos
    simp [hl] at hpos
  | inl β =>
    have hb:β∈Set.range (unfoldedInclusion M T):=
      sourceProbeOrbit_support M T g hg α b i.val β he
    obtain ⟨⟨s,L⟩,hb⟩:=hb
    have he':(N.placement i).color=.inl (.inl (s:S),L):=he.trans (congrArg Sum.inl hb.symm)
    have hnot:(s:S)∉J := by
      intro hj
      rw [he'] at hs
      exact hs (hsoc ⟨s,hj⟩ L _)
    have ht:generatorVector R N (.inl (.inl (s:S),L))*fusionFold m (C *ᵥ p) (.inl (s:S),L)<0 := by
      rw [he'] at hpos
      apply mul_neg_of_pos_of_neg hpos
      exact mul_neg_of_pos_of_neg (fusionWeight_pos m (fusionLabelSize_ge_two M) L)
        (hneg s s.property hnot)
    apply Finset.sum_neg' (fun β _=>sourceProbe_core_term_nonpos M T g hg α β b l p hp)
    exact ⟨(.inl (s:S),L),Finset.mem_univ _,ht⟩

end HarmonicArtin

end OAI
