import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeMinimumContainment
import OAI.Topology.ArtinGroups.ParabolicIntersections.InitialMinimum

namespace OAI

/-! The initial pointed-family stabilizer inside a frame-avoiding standard subgroup. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma initial_containing_subset (Y:Set S) (hf:f∉Y) :
    relativeContainingType M f 0 Y (sourceCoset M ∅ (spherical_empty M) 1) ⊆
      {i | i∈Y ∧ M i f=2} := by
  intro i hi
  rcases hi with hi|hi
  · exact (Set.notMem_empty i hi.1).elim
  · refine ⟨hi.1,?_⟩
    by_contra hm
    have hif:i≠f:=by rintro rfl;exact hf hi.1
    have hneg:=framedCartan_neg_of_label_ne_two M i f hif hm
    apply hi.2 0
    right
    refine ⟨.inl f,hneg,?_⟩
    rw [initial_profile]
    norm_num

/-- The only frame-avoiding words fixing the initial family are generated
by the colors that commute with the frame. -/
theorem pointed_initial_stabilizer_le (Y:Set S) (hf:f∉Y)
    (a:Artin M) (ha:a∈artinParabolic M Y)
    (hfix:pointedFamily M f a=pointedFamily M f 1) :
    a∈artinParabolic M {i | i∈Y ∧ M i f=2} := by
  let U:Set (S⊕Unit):=Sum.inl '' Y
  let P:RelativeVertex M Y 1:=relativeElement M Y 1 1 (rightCoset_self M Y 1)
  have hmin:RelativeMinimum M f U 0 P:=initial_height_minimum M f U 0 Y hf
  have hU:U⊆Set.range (Sum.inl:S→S⊕Unit):=by
    rintro _ ⟨i,_,rfl⟩
    exact ⟨i,rfl⟩
  have hfU:(.inl f:S⊕Unit)∉U:=by
    rintro ⟨i,hi,he⟩
    exact hf (Sum.inl.inj he ▸ hi)
  have hm:=relative_minimum_stabilizer_containment M f U 0
    (fun i hi=>⟨i,hi,rfl⟩) hU hfU (artinParabolic M {f}ᶜ).one_mem P hmin a ha
    (by simpa only [_root_.mul_one] using hfix)
  have hz:sourceCosetRepresentative M P.val=1:=by
    have h:=sourceCosetRepresentative_mem M P.val
    change sourceCosetRepresentative M P.val∈rightCoset M ∅ 1 at h
    rw [rightCoset_empty] at h
    exact h
  rw [hz,inv_one,_root_.mul_one,inv_one,conjugate_one] at hm
  exact artinParabolic_mono M (initial_containing_subset M f Y hf) hm

end HarmonicArtin.ParabolicIntersections

end OAI
