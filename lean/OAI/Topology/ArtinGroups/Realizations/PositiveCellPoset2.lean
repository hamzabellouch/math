import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.LiftedDeck
import OAI.Topology.ArtinGroups.Realizations.PositiveCellPoset

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

omit [Fintype S] [LinearOrder S] in
lemma positiveCellPoset_lt_iff (a b : PositiveCellPoset M inj) :
    a < b ↔ positiveCellToLifted M a < positiveCellToLifted M b := Iff.rfl

lemma positiveEarlier_of_top_lt (a b : PositiveCellPoset M inj)
    (h : positiveDegree M (positiveCellTop M a) < positiveDegree M (positiveCellTop M b)) :
    PositiveEarlier M z hz inj a b :=
  (positiveEarlier_iff M z hz inj a b).mpr (Or.inl h)

lemma positiveEarlier_of_key_lt (a b : PositiveCellPoset M inj)
    (he : positiveCellTop M a = positiveCellTop M b)
    (h : positiveMatchingTypeKey M z hz a < positiveMatchingTypeKey M z hz b) :
    PositiveEarlier M z hz inj a b :=
  (positiveEarlier_iff M z hz inj a b).mpr
    (Or.inr ⟨congrArg (positiveDegree M) he,Or.inl h⟩)

lemma positive_lt_orientation (a b : PositiveCellPoset M inj) (hab : a < b) :
    PositiveEarlier M z hz inj a b ∨
      ∃ ha : positiveCellTop M a ≠ 1,
        matchingLetter M z hz ⟨a,ha⟩ ∉ a.2.val ∧
        (positiveMatch M z hz inj ⟨a,ha⟩).val = b ∧
        PositiveEarlier M z hz inj b a := by
  by_cases he : positiveCellTop M a = positiveCellTop M b
  · have ha : positiveCellTop M a ≠ 1 := by
      intro h
      have ha' := (positiveCellTop_eq_one_iff M a).mp h
      have hb' := (positiveCellTop_eq_one_iff M b).mp (he.symm.trans h)
      exact hab.ne (ha'.trans hb'.symm)
    have hb : positiveCellTop M b ≠ 1 := fun h => ha (he.trans h)
    let s := matchingLetter M z hz ⟨a,ha⟩
    have ht : a.2.val.toFinset ⊂ b.2.val.toFinset := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
      · intro t ht
        exact Set.mem_toFinset.mpr ((lifted_lt_type M hab).subset (Set.mem_toFinset.mp ht))
      · intro heq
        have htype : a.2.val = b.2.val := by
          ext t
          simpa only [Set.mem_toFinset] using (congrArg (fun F : Finset S => t ∈ F) heq).to_iff
        exact hab.ne (positiveCellToLifted_injective M inj
          (lifted_eq_of_le_type_eq M hab.le htype))
    have hkA : positiveMatchingTypeKey M z hz a = topBlockMatchingKey s a.2.val.toFinset := by
      simp only [positiveMatchingTypeKey,dite_eq_right ha,s,matchingLetter]
    have hkB : positiveMatchingTypeKey M z hz b = topBlockMatchingKey s b.2.val.toFinset := by
      simp only [positiveMatchingTypeKey,dite_eq_right hb,s,matchingLetter,he]
    rcases topBlockMatchingKey_cases (s:=s) ht with hkey | ⟨hs,hT,hkey⟩
    · exact Or.inl (positiveEarlier_of_key_lt M z hz inj a b he (by rwa [hkA,hkB]))
    · have hs' : s ∉ a.2.val := fun h => hs (Set.mem_toFinset.mpr h)
      have hmatch : (positiveMatch M z hz inj ⟨a,ha⟩).val = b := by
        apply positiveCell_same_top_type_unique M inj
        · apply Subtype.ext
          rw [positiveMatch_type,matchingOtherType,ite_eq_right hs']
          ext t
          have hh := congrArg (fun F : Finset S => t ∈ F) hT
          simpa only [Finset.mem_insert,Set.mem_toFinset,Set.mem_insert_iff] using hh.symm.to_iff
        · exact (positiveMatch_top M z hz inj ⟨a,ha⟩).trans he
      exact Or.inr ⟨ha,hs',hmatch,
        positiveEarlier_of_key_lt M z hz inj b a he.symm (by rwa [hkA,hkB])⟩
  · exact Or.inl (positiveEarlier_of_top_lt M z hz inj a b
      (positiveCellTop_degree_strict M inj a b hab.le he))

lemma positiveMatch_below_or_above (a : NoncriticalPositiveCell M) :
    ((matchingLetter M z hz a ∉ a.val.2.val) ∧
        positiveCellToLifted M a.val < positiveCellToLifted M (positiveMatch M z hz inj a).val) ∨
      ((matchingLetter M z hz a ∈ a.val.2.val) ∧
        positiveCellToLifted M (positiveMatch M z hz inj a).val < positiveCellToLifted M a.val) := by
  have hinc := positiveMatch_incident M z hz inj a
  by_cases hs : matchingLetter M z hz a ∈ a.val.2.val
  · right; refine ⟨hs,?_⟩
    rcases hinc with h|h
    · have hsub := ((lifted_le_iff_face M _ _).mp h.le).1
      have hm := hsub hs
      change matchingLetter M z hz a ∈ (positiveMatch M z hz inj a).val.2.val at hm
      rw [positiveMatch_type,matchingOtherType,ite_eq_left hs] at hm
      exact (hm.2 (Set.mem_singleton _)).elim
    · exact h
  · left; refine ⟨hs,?_⟩
    rcases hinc with h|h
    · exact h
    · have hsub := ((lifted_le_iff_face M _ _).mp h.le).1
      exact (hs (hsub (by
        change matchingLetter M z hz a ∈ (positiveMatch M z hz inj a).val.2.val
        rw [positiveMatch_type,matchingOtherType,ite_eq_right hs]
        exact Set.mem_insert _ _))).elim

lemma positiveMatch_before (a : NoncriticalPositiveCell M)
    (hs : matchingLetter M z hz a ∉ a.val.2.val) :
    PositiveEarlier M z hz inj (positiveMatch M z hz inj a).val a.val := by
  apply positiveEarlier_of_key_lt M z hz inj _ _ (positiveMatch_top M z hz inj a)
  simp only [positiveMatchingTypeKey,dite_eq_right a.property,positiveMatch_top]
  apply topBlockStep_key (Or.inl ⟨?_,?_⟩)
  · exact fun h => hs (Set.mem_toFinset.mp h)
  · ext t
    simp only [Set.mem_toFinset,Finset.mem_insert]
    rw [positiveMatch_type,matchingOtherType,ite_eq_right hs]
    rfl

lemma positiveEarlier_asymm {a b : PositiveCellPoset M inj}
    (h : PositiveEarlier M z hz inj a b) : ¬ PositiveEarlier M z hz inj b a :=
  (positiveEarlier_wf M z hz inj).asymmetric _ _ h

end HarmonicArtin

end OAI
