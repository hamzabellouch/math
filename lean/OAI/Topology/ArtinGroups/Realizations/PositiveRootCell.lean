import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PositiveMatchingTypeKey
import OAI.Topology.ArtinGroups.Realizations.NoncriticalPositiveCell

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

omit [Fintype S] in
lemma positiveDescentSet_one : PositiveDescentSet M 1=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨p,hp⟩:=hs
  have h:=congrArg (positiveDegree M) hp
  simp only [positiveDegree_one,positiveDegree_mul,positiveDegree_generator] at h
  omega

noncomputable def positiveRootCell : PositiveLiftedCell M :=
  (1,⟨∅,spherical_empty M⟩)

lemma positiveCellTop_eq_one_iff (a:PositiveLiftedCell M) :
    positiveCellTop M a=1 ↔ a=positiveRootCell M := by
  constructor
  · intro h
    have ht:=type_subset_positiveDescentSet M _ _ (sphericalLongest_spec M a.2) a.1
    change a.2.val⊆PositiveDescentSet M (positiveCellTop M a) at ht
    rw [h,positiveDescentSet_one] at ht
    have htype:a.2.val=∅:=Set.subset_empty_iff.mp ht
    have hd:=congrArg (positiveDegree M) h
    simp only [positiveCellTop,positiveDegree_mul,positiveDegree_one] at hd
    apply Prod.ext
    · exact (positiveDegree_zero_iff M a.1).mp (by omega)
    · exact Subtype.ext htype
  · rintro rfl
    have hq: sphericalLongest M (positiveRootCell M).2=1 := by
      have h:=(sphericalLongest_spec M (positiveRootCell M).2).1
      simpa [positiveRootCell,coxeterParabolic] using h
    change 1*positiveSimpleLift M (sphericalLongest M (positiveRootCell M).2)=1
    rw [one_mul,hq]
    apply (positiveDegree_zero_iff M _).mp
    simp only [positiveDegree_simpleLift,M.toCoxeterSystem.length_one]

variable [LinearOrder S] (z:M.Group)
  (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
  (inj:Function.Injective (positiveToArtin M))

lemma positiveMatch_gradient (a:NoncriticalPositiveCell M)
    (hs:matchingLetter M z hz a ∉ a.val.2.val) :
    PositiveGradientStep M z hz a.val (positiveMatch M z hz inj a).val := by
  right
  refine ⟨a.property,positiveMatch_top M z hz inj a,Or.inl ⟨?_,?_⟩⟩
  · exact fun h=>hs (Set.mem_toFinset.mp h)
  · have ht:=positiveMatch_type M z hz inj a
    rw [matchingOtherType,ite_eq_right hs] at ht
    ext s
    simp only [Set.mem_toFinset,Finset.mem_insert,ht,Set.mem_insert_iff]
    rfl

end HarmonicArtin

end OAI
