import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionQuiverCartan
import OAI.Topology.ArtinGroups.Complexes.GeneratorVectorPureLayer
import OAI.Topology.ArtinGroups.Harmonic.FinsuppMapDomainFiber
import OAI.Topology.ArtinGroups.Complexes.PacketPermExterior
import OAI.Topology.ArtinGroups.Harmonic.ProbePacketExterior
import OAI.Topology.ArtinGroups.Quivers.ProbeCartanCore

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open ReversibleQuiver.ProbeEmbedding _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=K)

lemma sourceProbeAction_level_exterior (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (x:FiniteHomotopyClass R (K:=K)) (α:ProbeVertex (FusionVertex (V:=S⊕Unit) m))
    (hp:∀s∈J,∀L,Sum.inl (Sum.inl s,L)≠α) (l:ℤ) :
    classLevelArray R (bw g x) (α,l)=classLevelArray R x (α,l) := by
  apply finsupp_mapDomain_fiber
  intro p he
  apply sourceProbeAction_exterior M J g hg
  intro s hs L hh
  apply hp s hs L
  exact hh.trans (congrArg Prod.fst he)

lemma sourceProbeOrbit_leaf_level (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (α β:FusionVertex (V:=S⊕Unit) m) (b c:Bool) (l:ℤ) :
    classLevelArray R (bw g (initialClass R (.inr (α,b)))) (.inr (β,c),l)=
      if (α,b)=(β,c) ∧ l=0 then 1 else 0 := by
  rw [sourceProbeAction_level_exterior M J g hg _ _ (by intros; exact Sum.inl_ne_inr),
    classLevelArray_initial]
  simp only [Sum.inr.injEq]

lemma sourceProbeOrbit_leaf_vector (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (α β:FusionVertex (V:=S⊕Unit) m) (b c:Bool) (l:ℤ) :
    generatorVector R
      ((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.pureLayer R
        (minimalClassModel_minimal R _) l) (.inr (β,c))=
      if (α,b)=(β,c) ∧ l=0 then 1 else 0 := by
  rw [generatorVector_minimalLayer,sourceProbeOrbit_leaf_level M J g hg]
  split <;> norm_num

lemma sourceProbeOrbit_core_vector_off (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (α β:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ)
    (hb:β∉Set.range (unfoldedInclusion M J)) :
    generatorVector R
      ((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.pureLayer R
        (minimalClassModel_minimal R _) l) (.inl β)=0 := by
  rw [generatorVector_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply ite_eq_right
  intro he
  exact hb (sourceProbeOrbit_support M J g hg α b i.val β he)

lemma sourceProbeOrbit_cartan (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (α:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ) (p:S⊕Unit→ℝ) :
    let Y:=((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.pureLayer R
      (minimalClassModel_minimal R _) l)
    generatorVector R Y ⬝ᵥ (unfoldedCartan R *ᵥ Sum.elim (fusionFold m p) (fun _=>0))=
      (fun β=>generatorVector R Y (.inl β)) ⬝ᵥ
        fusionFold m (fusionFoldedCartan m d *ᵥ p)-
      if l=0 then fusionWeight m α.2*p α.1 else 0 := by
  dsimp only
  let Y:=((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.pureLayer R
    (minimalClassModel_minimal R _) l)
  have hpc:=probeCartan_pairing Q (generatorVector R Y) (fusionFold m p)
  have hpc' : generatorVector R Y ⬝ᵥ (unfoldedCartan R *ᵥ Sum.elim (fusionFold m p) (fun _=>0))=
      (fun β=>generatorVector R Y (.inl β)) ⬝ᵥ (unfoldedCartan Q *ᵥ fusionFold m p)-
        ∑β,∑c:Bool,generatorVector R Y (.inr (β,c))*fusionFold m p β := by
    convert hpc using 1 <;> congr 5 <;> exact Subsingleton.elim _ _
  have hc:(unfoldedCartan Q *ᵥ fusionFold m p)=
      fusionFold m (fusionFoldedCartan m d *ᵥ p) := by
    rw [fusionQuiver_cartan]
    exact fusion_intertwining m (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e)) d p
  apply hpc'.trans
  have hc': (fun β=>generatorVector R Y (.inl β)) ⬝ᵥ (unfoldedCartan Q *ᵥ fusionFold m p)=
      (fun β=>generatorVector R Y (.inl β)) ⬝ᵥ fusionFold m (fusionFoldedCartan m d *ᵥ p) :=
    congrArg ((fun β=>generatorVector R Y (.inl β)) ⬝ᵥ ·) hc
  apply congrArg₂ (·-·) hc'
  dsimp only [Y]
  simp only [sourceProbeOrbit_leaf_vector M J g hg]
  by_cases hl:l=0
  · simp [hl,Prod.mk.injEq,ite_and,ite_mul,fusionFold]
  · simp [hl]

end HarmonicArtin

end OAI
