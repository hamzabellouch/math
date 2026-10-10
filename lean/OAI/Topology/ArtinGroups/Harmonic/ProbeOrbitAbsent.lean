import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.MapPacket
import OAI.Topology.ArtinGroups.Harmonic.PlacementLevelFiberSum
import OAI.Topology.ArtinGroups.Harmonic.ProbeActionLevelExterior
import OAI.Topology.ArtinGroups.Complexes.ProbeHomDimensionGenerator

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=K)

lemma sourceProbeOrbit_absent (T:Set S) (g:Artin M) (hg:g∈artinParabolic M T)
    (α β:FusionVertex (V:=S⊕Unit) m) (b c:Bool) (hbc:b≠c) :
    ∀i,((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.placement i).color≠.inr (β,c) := by
  intro i hi
  let x:=bw g (initialClass R (.inr (α,b)))
  let E:=minimalClassModel R x
  have hp:0<classGeneratorArray R x (E.complex.placement i) := by
    rw [← minimalClassModel_class R x,classGeneratorArray_of_minimal R _ (minimalClassModel_minimal R x)]
    rw [generatorArray_apply]
    change 0<Nat.card {j:E.Index // E.complex.placement j=E.complex.placement i}
    let : Nonempty {j:E.Index // E.complex.placement j=E.complex.placement i}:=⟨⟨i,rfl⟩⟩
    exact Nat.card_pos
  have hz:=sourceProbeAction_exterior M (K:=K) T g hg (initialClass R (.inr (α,b))) (E.complex.placement i)
    (by intro s hs L he; exact Sum.inl_ne_inr (he.trans hi))
  rw [sourceProbeInitial_array] at hz
  have hne:E.complex.placement i≠⟨.inr (α,b),0,0⟩:=by
    intro he
    have hh:=congrArg GeneratorPlacement.color he
    rw [hi] at hh
    exact hbc (congrArg Prod.snd (Sum.inr.inj hh)).symm
  rw [ite_eq_right hne] at hz
  change 0<classGeneratorArray R (bw g (initialClass R (.inr (α,b)))) _ at hp
  omega

lemma sourceProbe_generator_dual (T:Set S) (g:Artin M) (hg:g∈artinParabolic M T)
    (α β:FusionVertex (V:=S⊕Unit) m) (b:Bool) (n u:ℤ) :
    classGeneratorArray R (bw g (initialClass R (.inr (α,b)))) ⟨.inl β,n,u⟩=
      classGeneratorArray R (bw g⁻¹ (initialClass R (.inr (β,!b)))) ⟨.inl α,-n,-u⟩ := by
  have h₁:=probeClassHomDimension_generatorArray_flexible Q
    (bw g (initialClass R (.inr (α,b)))) β (!b)
    (sourceProbeOrbit_absent M T g hg α β b (!b) (by cases b <;> decide)) n (u+1)
  have h₂:=probeClassHomDimension_generatorArray_flexible Q
    (bw g⁻¹ (initialClass R (.inr (β,!b)))) α b
    (sourceProbeOrbit_absent M T g⁻¹ ((artinParabolic M T).inv_mem hg) β α (!b) b (by cases b <;> decide))
    (-n) (1-u)
  have hu:(u+1)-1=u:=by omega
  have hv:(1-u)-1= -u:=by omega
  rw [hu] at h₁
  rw [hv] at h₂
  rw [←h₁,←h₂,classHomDimension_dual]
  have he:=sourceProbeAction_homDimension M g (initialClass R (.inr (α,b)))
    (bw g⁻¹ (initialClass R (.inr (β,!b)))) (-n) (1-u)
  rw [map_inv,Equiv.Perm.inv_def,Equiv.apply_symm_apply] at he
  have ht:2-(u+1)=1-u:=by omega
  simpa only [ht,map_inv,Equiv.Perm.inv_def] using he

lemma sourceProbe_level_dual (T:Set S) (g:Artin M) (hg:g∈artinParabolic M T)
    (α β:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ) :
    classLevelArray R (bw g (initialClass R (.inr (α,b)))) (.inl β,l)=
      classLevelArray R (bw g⁻¹ (initialClass R (.inr (β,!b)))) (.inl α,-l) := by
  exact placementLevel_dual
    (classGeneratorArray R (bw g (initialClass R (.inr (α,b)))))
    (classGeneratorArray R (bw g⁻¹ (initialClass R (.inr (β,!b)))))
    (.inl β) (.inl α) (sourceProbe_generator_dual M T g hg α β b) l

lemma sourceProbe_block_left (J:Set S) (a g:Artin M) (ha:a∈artinParabolic M J)
    (α β:FusionVertex (V:=S⊕Unit) m) (hβ:β∉Set.range (unfoldedInclusion M J)) (b:Bool) (l:ℤ) :
    classLevelArray R (bw (a*g) (initialClass R (.inr (α,b)))) (.inl β,l)=
      classLevelArray R (bw g (initialClass R (.inr (α,b)))) (.inl β,l) := by
  rw [map_mul,Equiv.Perm.mul_apply]
  apply sourceProbeAction_level_exterior M J a ha
  intro s hs L he
  exact hβ ⟨(⟨s,hs⟩,L),Sum.inl.inj he⟩

end HarmonicArtin

end OAI
