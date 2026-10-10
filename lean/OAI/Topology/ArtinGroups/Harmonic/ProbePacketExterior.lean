import Mathlib
import OAI.Topology.ArtinGroups.Functors.ZigzagLinear
import OAI.Topology.ArtinGroups.Harmonic.ProbePacket
import OAI.Topology.ArtinGroups.Functors.TwistProdGeneratorExterior

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open ReversibleQuiver.ProbeEmbedding

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=K)

lemma sourceProbePacket_exterior (s:S) (x:FiniteHomotopyClass R (K:=K))
    (p:GeneratorPlacement (ProbeVertex (FusionVertex (V:=S⊕Unit) m)))
    (hp:∀L,Sum.inl (Sum.inl s,L)≠p.color) :
    classGeneratorArray R (sourceProbePacket M s x) p=classGeneratorArray R x p := by
  apply twistProd_generator_exterior Q hn
  intro a ha
  unfold fusionExpandedWord at ha
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_map] at ha
  obtain ⟨L,_,rfl⟩:=ha
  exact hp L

lemma sourceProbeAction_exterior (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (x:FiniteHomotopyClass R (K:=K))
    (p:GeneratorPlacement (ProbeVertex (FusionVertex (V:=S⊕Unit) m)))
    (hp:∀s∈J,∀L,Sum.inl (Sum.inl s,L)≠p.color) :
    classGeneratorArray R (bw g x) p=classGeneratorArray R x p := by
  let H:Subgroup (Artin M):=
    { carrier:={g|∀x,classGeneratorArray R (bw g x) p=classGeneratorArray R x p}
      one_mem':=by intro x; simp
      mul_mem':=by
        intro a b ha hb x
        simp only [map_mul,Equiv.Perm.mul_apply]
        exact (ha (bw b x)).trans (hb x)
      inv_mem':=by
        intro a ha x
        have h:=ha (bw a⁻¹ x)
        simpa only [map_inv,Equiv.Perm.inv_def,Equiv.apply_symm_apply] using h.symm }
  have hH:artinParabolic M J≤H:=(Subgroup.closure_le H).mpr (by
    rintro g ⟨s,hs,rfl⟩
    change ∀x,classGeneratorArray R (bw (generator M s) x) p=_
    intro x
    rw [sourceProbeAction_generator]
    exact sourceProbePacket_exterior M s x p (hp s hs))
  exact hH hg x

lemma sourceProbeInitial_array (α:ProbeVertex (FusionVertex (V:=S⊕Unit) m))
    (p:GeneratorPlacement (ProbeVertex (FusionVertex (V:=S⊕Unit) m))) :
    classGeneratorArray R (initialClass R (K:=K) α) p=if p=⟨α,0,0⟩ then 1 else 0 := by
  rw [initialClass,classGeneratorArray_of_minimal R _ (show (initialProjective R α).IsMinimal R from
    fun i j=>rfl)]
  change (initialProjective R α).generatorArray R p=_
  rw [generatorArray]
  simp only [initialProjective,Finset.univ_unique,Finset.sum_singleton,Finsupp.single_apply,eq_comm]

lemma sourceProbeOrbit_support (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (α:FusionVertex (V:=S⊕Unit) m) (b:Bool) :
    ∀i β,((minimalClassModel R (bw g (initialClass R (.inr (α,b))))).complex.placement i).color=.inl β→
      β∈Set.range (unfoldedInclusion M J) := by
  let y:=bw g (initialClass R (.inr (α,b)))
  let E:=minimalClassModel R y
  intro i β hi
  by_contra hout
  have hp:0<classGeneratorArray R y (E.complex.placement i) := by
    rw [← minimalClassModel_class R y,classGeneratorArray_of_minimal R _ (minimalClassModel_minimal R y),
      generatorArray_apply]
    change 0<Nat.card {j:E.Index // E.complex.placement j=E.complex.placement i}
    have :Nonempty {j:E.Index // E.complex.placement j=E.complex.placement i}:=⟨⟨i,rfl⟩⟩
    exact Nat.card_pos
  have hz:=sourceProbeAction_exterior M (K:=K) J g hg (initialClass R (.inr (α,b))) (E.complex.placement i)
    (by
      intro s hs L he
      apply hout
      exact ⟨(⟨s,hs⟩,L),Sum.inl.inj (he.trans hi)⟩)
  rw [sourceProbeInitial_array] at hz
  have hne:E.complex.placement i≠⟨.inr (α,b),0,0⟩:=by
    intro he
    have hh:=congrArg GeneratorPlacement.color he
    rw [hi] at hh
    exact Sum.inl_ne_inr hh
  rw [ite_eq_right hne] at hz
  change 0<classGeneratorArray R (bw g (initialClass R (.inr (α,b)))) _ at hp
  omega

end HarmonicArtin

end OAI
