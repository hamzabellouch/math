import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FiniteFusionEdge
import OAI.Topology.ArtinGroups.Harmonic.DimensionPosMultiplicityPos

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] in
lemma fusionLabelSize_ge_two (e:FiniteFusionEdge M) : 2 ≤ fusionLabelSize M e :=
  le_trans (by decide) (fusionLabelSize_ge_four M e)

def sourcePacketWord (w:List (S × Bool)) : List ((S ⊕ Unit) × Bool) :=
  w.map fun b=>(Sum.inl b.1,b.2)

noncomputable def sourcePacketMultiplicity (w:List (S × Bool)) (q:ℤ) : S ⊕ Unit → ℝ :=
  fusionOrbitMultiplicity (fusionLabelSize M) (coxeterFusionEdge M)
    (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (fusionLabelSize_ge_two M)
    (sourcePacketWord w) (.inr ()) q

lemma sourcePacket_frame (w:List (S × Bool)) :
    sourcePacketMultiplicity M w 0 (.inr ())=1 := by
  apply fusionOrbitMultiplicity_frame
  intro b hb
  obtain ⟨a,_,rfl⟩:=List.mem_map.mp hb
  exact Sum.inl_ne_inr

theorem sourcePacket_no_isolated_null_layer (w:List (S × Bool)) (q:ℤ)
    (I:Set S) (hI:I.Nonempty) (c:S ⊕ Unit → ℝ)
    (hc:∀ i∈I,0<c (.inl i))
    (hsupp:∀ b,b∉Sum.inl '' I → c b=0)
    (hnull:∀ i∈I,(framedCartan M *ᵥ c) (.inl i)=0)
    (hdata:∀ b,b∈Sum.inl '' I ∨
      (b∉Sum.inl '' I ∧ ∃ i∈I,framedCartan M b (.inl i)<0) →
      sourcePacketMultiplicity M w q b=c b) : False := by
  have hC : fusionFoldedCartan (fusionLabelSize M) (coxeterFusionEdge M) = framedCartan M := by
    convert fusionFoldedCartan_eq_framedCartan M using 1
    congr 1
    exact Subsingleton.elim _ _
  let U:Set (S ⊕ Unit):=Sum.inl '' I
  have hi (b:S ⊕ Unit) : b∈U ↔ ∃ i∈I,Sum.inl i=b := Iff.rfl
  have he: fusionOrbitColorMultiplicity (fusionLabelSize M) (coxeterFusionEdge M)
      (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (fusionLabelSize_ge_two M)
      (sourcePacketWord w) (.inr ()) q U=c := by
    funext b
    by_cases hb:b∈U
    · simp only [fusionOrbitColorMultiplicity,hb,ite_true]
      exact hdata b (Or.inl hb)
    · simp only [fusionOrbitColorMultiplicity,hb,ite_false]
      exact (hsupp b hb).symm
  apply fusionOrbit_no_isolated_null_layer (fusionLabelSize M) (coxeterFusionEdge M)
    (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (fusionLabelSize_ge_two M)
    (sourcePacketWord w) (.inr ()) q U
  · intro b hb
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp hb
    exact Sum.inl_ne_inr
  · rintro ⟨i,_,h⟩
    exact Sum.inl_ne_inr h
  · obtain ⟨i,hi⟩:=hI
    refine ⟨.inl i,⟨i,hi,rfl⟩,?_⟩
    rw [hC]
    norm_num [framedCartan]
  · intro v hv
    change 0<sourcePacketMultiplicity M w q v
    rw [hdata v (Or.inl hv)]
    obtain ⟨i,hi,rfl⟩:=hv
    exact hc i hi
  · intro v hv
    rw [he,hC]
    obtain ⟨i,hi,rfl⟩:=hv
    exact hnull i hi
  · intro b hb hbadj
    change sourcePacketMultiplicity M w q b=0
    have hd:sourcePacketMultiplicity M w q b=c b := by
      apply hdata
      right
      refine ⟨hb,?_⟩
      obtain ⟨v,⟨i,hi,rfl⟩,hneg⟩:=hbadj
      refine ⟨i,hi,?_⟩
      simpa only [hC] using hneg
    exact hd.trans (hsupp b hb)

end HarmonicArtin

end OAI
