import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.TopBlockMatchingKey
import OAI.Topology.ArtinGroups.Realizations.PositiveLiftedCell

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
variable (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
variable (inj:Function.Injective (positiveToArtin M))

include inj in
omit [LinearOrder S] in
lemma positiveCell_same_top_type_unique (a b:PositiveLiftedCell M)
    (ht:a.2=b.2) (hb:positiveCellTop M a=positiveCellTop M b) : a=b := by
  apply Prod.ext ?_ ht
  apply inj
  have hp:=congrArg (positiveToArtin M) hb
  simp only [positiveCellTop,map_mul,positiveToArtin_simpleLift,ht] at hp
  exact mul_right_cancel hp

include z hz inj in
omit [LinearOrder S] in
theorem positiveCell_realize_top (b:PositiveArtin M) (T:SphericalType M)
    (hT:T.val⊆PositiveDescentSet M b) :
    ∃a:PositiveLiftedCell M,a.2=T ∧ positiveCellTop M a=b := by
  have cancel:∀a d e:PositiveArtin M,a*d=a*e→d=e:=by
    intro a d e h
    apply inj
    exact mul_left_cancel (by simpa only [map_mul] using congrArg (positiveToArtin M) h)
  obtain ⟨hD,q,hq,p,hp⟩:=positive_descent_fundamental M z hz cancel b
  let r:=q*(sphericalLongest M T)⁻¹
  have hm:(sphericalLongest M T)⁻¹∈coxeterParabolic M (PositiveDescentSet M b):=
    coxeterParabolic_mono M hT ((coxeterParabolic M T.val).inv_mem (sphericalLongest_spec M T).1)
  have hl:=parabolic_longest_length_mul M _ q hq (sphericalLongest M T)⁻¹ hm
  rw [M.toCoxeterSystem.length_inv] at hl
  have he:r*sphericalLongest M T=q:=by dsimp [r];group
  have hl':M.toCoxeterSystem.length (r*sphericalLongest M T)=
      M.toCoxeterSystem.length r+M.toCoxeterSystem.length (sphericalLongest M T):=by rw [he];exact hl.symm
  have hprod:=positiveSimpleLift_mul M r (sphericalLongest M T) hl'
  rw [he] at hprod
  refine ⟨(p*positiveSimpleLift M r,T),rfl,?_⟩
  change (p*positiveSimpleLift M r)*positiveSimpleLift M (sphericalLongest M T)=b
  rw [hp,hprod,mul_assoc]

abbrev NoncriticalPositiveCell := {a:PositiveLiftedCell M // positiveCellTop M a≠1}

noncomputable def matchingLetter (a:NoncriticalPositiveCell M) : S :=
  firstPositiveDescent M z hz (positiveCellTop M a.val) a.property

noncomputable def matchingOtherType (a:NoncriticalPositiveCell M) : Set S :=
  if matchingLetter M z hz a∈a.val.2.val then a.val.2.val\{matchingLetter M z hz a}
  else insert (matchingLetter M z hz a) a.val.2.val

lemma matchingOtherType_subset (a:NoncriticalPositiveCell M) :
    matchingOtherType M z hz a⊆PositiveDescentSet M (positiveCellTop M a.val) := by
  have hT:a.val.2.val⊆PositiveDescentSet M (positiveCellTop M a.val):=
    type_subset_positiveDescentSet M _ _ (sphericalLongest_spec M a.val.2) a.val.1
  have hs:matchingLetter M z hz a∈PositiveDescentSet M (positiveCellTop M a.val):=
    firstPositiveDescent_mem M z hz _ _
  unfold matchingOtherType
  split_ifs
  · exact Set.Subset.trans Set.sdiff_subset hT
  · exact Set.insert_subset hs hT

include inj in
lemma matchingOtherType_spherical (a:NoncriticalPositiveCell M) :
    IsSpherical M (matchingOtherType M z hz a) := by
  have cancel:∀a d e:PositiveArtin M,a*d=a*e→d=e:=by
    intro a d e h
    apply inj
    exact mul_left_cancel (by simpa only [map_mul] using congrArg (positiveToArtin M) h)
  exact spherical_type_mono M (matchingOtherType_subset M z hz a)
    (positive_descent_fundamental M z hz cancel (positiveCellTop M a.val)).1

noncomputable def positiveMatch (a:NoncriticalPositiveCell M) : NoncriticalPositiveCell M :=
  let T:SphericalType M:=⟨matchingOtherType M z hz a,matchingOtherType_spherical M z hz inj a⟩
  let h:=positiveCell_realize_top M z hz inj (positiveCellTop M a.val) T (matchingOtherType_subset M z hz a)
  ⟨h.choose,fun he=>a.property (h.choose_spec.2.symm.trans he)⟩

lemma positiveMatch_top (a:NoncriticalPositiveCell M) :
    positiveCellTop M (positiveMatch M z hz inj a).val=positiveCellTop M a.val := by
  exact (positiveCell_realize_top M z hz inj (positiveCellTop M a.val)
    ⟨matchingOtherType M z hz a,matchingOtherType_spherical M z hz inj a⟩
    (matchingOtherType_subset M z hz a)).choose_spec.2

lemma positiveMatch_type (a:NoncriticalPositiveCell M) :
    (positiveMatch M z hz inj a).val.2.val=matchingOtherType M z hz a := by
  exact congrArg Subtype.val (positiveCell_realize_top M z hz inj (positiveCellTop M a.val)
    ⟨matchingOtherType M z hz a,matchingOtherType_spherical M z hz inj a⟩
    (matchingOtherType_subset M z hz a)).choose_spec.1

lemma positiveMatch_letter (a:NoncriticalPositiveCell M) :
    matchingLetter M z hz (positiveMatch M z hz inj a)=matchingLetter M z hz a := by
  simp only [matchingLetter,positiveMatch_top]

theorem positiveMatch_involutive : Function.Involutive (positiveMatch M z hz inj) := by
  intro a
  apply Subtype.ext
  apply positiveCell_same_top_type_unique M inj
  · apply Subtype.ext
    rw [positiveMatch_type]
    simp only [matchingOtherType,positiveMatch_letter,positiveMatch_type]
    by_cases hs:matchingLetter M z hz a∈a.val.2.val
    · simp only [hs,ite_eq_left,Set.mem_sdiff,Set.mem_singleton_iff,not_true_eq_false,and_false,ite_false]
      rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hs]
    · simp only [hs,ite_false,Set.mem_insert_iff,true_or,ite_eq_left]
      ext x
      by_cases he : x = matchingLetter M z hz a
      · subst x
        simp [hs]
      · simp [he]
  · exact (positiveMatch_top M z hz inj (positiveMatch M z hz inj a)).trans (positiveMatch_top M z hz inj a)

theorem positiveMatch_ne (a:NoncriticalPositiveCell M) : positiveMatch M z hz inj a≠a := by
  intro he
  have ht:=positiveMatch_type M z hz inj a
  rw [he] at ht
  have hm:matchingLetter M z hz a∈a.val.2.val ↔ matchingLetter M z hz a∈matchingOtherType M z hz a:=by rw [ht]
  simp only [matchingOtherType] at hm
  split_ifs at hm with hs
  · simp [hs] at hm
  · simp [hs] at hm

theorem positiveMatch_incident (a:NoncriticalPositiveCell M) :
    positiveCellToLifted M a.val < positiveCellToLifted M (positiveMatch M z hz inj a).val ∨
    positiveCellToLifted M (positiveMatch M z hz inj a).val < positiveCellToLifted M a.val := by
  have hne:positiveCellToLifted M a.val ≠ positiveCellToLifted M (positiveMatch M z hz inj a).val := by
    intro he
    apply positiveMatch_ne M z hz inj a
    apply Subtype.ext
    apply Prod.ext
    · apply inj
      exact (congrArg Prod.fst he).symm
    · exact (congrArg Prod.snd he).symm
  have hcell:∀c:PositiveLiftedCell M,positiveCellToLifted M c=
      cellWithTop M (positiveToArtin M (positiveCellTop M c)) c.2:=by
    intro c
    rw [positiveCellTop_toArtin]
    exact (cellWithTop_topVertex M (positiveCellToLifted M c)).symm
  have hAB:a.val.2.val⊆(positiveMatch M z hz inj a).val.2.val ∨
      (positiveMatch M z hz inj a).val.2.val⊆a.val.2.val:=by
    rw [positiveMatch_type]
    unfold matchingOtherType
    split_ifs
    · exact Or.inr Set.sdiff_subset
    · exact Or.inl (Set.subset_insert _ _)
  rcases hAB with hab|hba
  · left
    apply lt_of_le_of_ne ?_ hne
    rw [hcell _,hcell _,positiveMatch_top]
    exact cellWithTop_mono M _ hab
  · right
    apply lt_of_le_of_ne ?_ hne.symm
    rw [hcell _,hcell _,positiveMatch_top]
    exact cellWithTop_mono M _ hba

theorem spherical_positive_matching {A:Type} [Fintype A] [LinearOrder A]
    (N:CoxeterMatrix A) (T:Set A) (hT:IsSpherical N T) :
    ∃ f:NoncriticalPositiveCell (restrictedMatrix N T) → NoncriticalPositiveCell (restrictedMatrix N T),
      Function.Involutive f ∧ ∀a, f a≠a ∧
        (positiveCellToLifted (restrictedMatrix N T) a.val < positiveCellToLifted (restrictedMatrix N T) (f a).val ∨
        positiveCellToLifted (restrictedMatrix N T) (f a).val < positiveCellToLifted (restrictedMatrix N T) a.val) := by
  let : Finite (restrictedMatrix N T).Group:=restricted_finite N T hT
  obtain ⟨z,hz⟩:=exists_longest (restrictedMatrix N T).toCoxeterSystem
  let inj:=spherical_positiveToArtin_injective N T hT
  exact ⟨positiveMatch (restrictedMatrix N T) z hz inj,
    positiveMatch_involutive (restrictedMatrix N T) z hz inj,
    fun a=>⟨positiveMatch_ne (restrictedMatrix N T) z hz inj a,
      positiveMatch_incident (restrictedMatrix N T) z hz inj a⟩⟩

end HarmonicArtin

end OAI
