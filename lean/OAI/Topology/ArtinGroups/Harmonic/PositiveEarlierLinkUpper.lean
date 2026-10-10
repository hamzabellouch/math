import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.InsertOldIso
import OAI.Topology.ArtinGroups.Realizations.PositiveCellPoset2

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

lemma positiveMatch_upper_lt (a : NoncriticalPositiveCell M)
    (hs : matchingLetter M z hz a ∉ a.val.2.val) :
    positiveCellToLifted M a.val < positiveCellToLifted M (positiveMatch M z hz inj a).val := by
  rcases positiveMatch_below_or_above M z hz inj a with h|h
  · exact h.2
  · exact (hs h.1).elim

lemma positiveMatch_lower_lt (a : NoncriticalPositiveCell M)
    (hs : matchingLetter M z hz a ∈ a.val.2.val) :
    positiveCellToLifted M (positiveMatch M z hz inj a).val < positiveCellToLifted M a.val := by
  rcases positiveMatch_below_or_above M z hz inj a with h|h
  · exact (h.1 hs).elim
  · exact h.2

lemma positiveMatch_lower_before (a : NoncriticalPositiveCell M)
    (hs : matchingLetter M z hz a ∈ a.val.2.val) :
    PositiveEarlier M z hz inj a.val (positiveMatch M z hz inj a).val := by
  have hs' : matchingLetter M z hz (positiveMatch M z hz inj a) ∉
      (positiveMatch M z hz inj a).val.2.val := by
    rw [positiveMatch_letter,positiveMatch_type,matchingOtherType,ite_eq_left hs]
    simp only [Set.mem_sdiff,Set.mem_singleton_iff,not_true_eq_false,and_false,not_false_eq_true]
  have h := positiveMatch_before M z hz inj (positiveMatch M z hz inj a) hs'
  rw [positiveMatch_involutive M z hz inj a] at h
  exact h

lemma positiveMatch_symm_value (a b : NoncriticalPositiveCell M)
    (h : (positiveMatch M z hz inj a).val = b.val) :
    (positiveMatch M z hz inj b).val = a.val := by
  have he : positiveMatch M z hz inj a = b := Subtype.ext h
  have he' := congrArg (positiveMatch M z hz inj) he
  rw [positiveMatch_involutive] at he'
  exact (congrArg Subtype.val he').symm

lemma positiveEarlier_upper_eq (a b : PositiveCellPoset M inj) (hab : a < b)
    (hba : PositiveEarlier M z hz inj b a) :
    ∃ ha : positiveCellTop M a ≠ 1,
      matchingLetter M z hz ⟨a,ha⟩ ∉ a.2.val ∧
      (positiveMatch M z hz inj ⟨a,ha⟩).val = b := by
  rcases positive_lt_orientation M z hz inj a b hab with h|⟨ha,hs,hm,_⟩
  · exact (positiveEarlier_asymm M z hz inj h hba).elim
  · exact ⟨ha,hs,hm⟩

theorem positiveEarlierLink_lower_contractible (a : NoncriticalPositiveCell M)
    (hs : matchingLetter M z hz a ∉ a.val.2.val) :
    ContractibleSpace (OrderWeights (WeightEarlierLink (PositiveEarlier M z hz inj) a.val)) := by
  let b : PositiveCellPoset M inj := (positiveMatch M z hz inj a).val
  have hab : positiveCellToLifted M a.val < positiveCellToLifted M b := positiveMatch_upper_lt M z hz inj a hs
  have hba : PositiveEarlier M z hz inj b a.val := positiveMatch_before M z hz inj a hs
  let v : WeightEarlierLink (PositiveEarlier M z hz inj) a.val := ⟨b,hba,Or.inr hab.le⟩
  have hv : ∀ x : WeightEarlierLink (PositiveEarlier M z hz inj) a.val, x ≤ v := by
    intro x
    rcases x.property.2 with h|h
    · exact h.trans hab.le
    · have hne : a.val ≠ x.val := by
        intro he
        have hh := x.property.1
        rw [←he] at hh
        exact (positiveEarlier_wf M z hz inj).irrefl.irrefl _ hh
      obtain ⟨_,_,he⟩ := positiveEarlier_upper_eq M z hz inj a.val x.val
        (lt_of_le_of_ne h hne) x.property.1
      change (x.val : PositiveCellPoset M inj) ≤ b
      exact le_of_eq he.symm
  let : OrderTop (WeightEarlierLink (PositiveEarlier M z hz inj) a.val) :=
    { top := v, le_top := hv }
  exact nerveWeightsHomeomorph.contractibleSpace_iff.mp
    (nerve_orderTop_contractible (WeightEarlierLink (PositiveEarlier M z hz inj) a.val))

lemma positiveEarlierLink_upper_iff (a : NoncriticalPositiveCell M)
    (hs : matchingLetter M z hz a ∈ a.val.2.val) (x : PositiveCellPoset M inj) :
    (PositiveEarlier M z hz inj x a.val ∧ (positiveCellToLifted M x ≤ positiveCellToLifted M a.val ∨
      positiveCellToLifted M a.val ≤ positiveCellToLifted M x)) ↔
      positiveCellToLifted M x < positiveCellToLifted M a.val ∧ x ≠ (positiveMatch M z hz inj a).val := by
  constructor
  · rintro ⟨hr,hcomp⟩
    have hne : x ≠ a.val := by
      intro he
      rw [he] at hr
      exact (positiveEarlier_wf M z hz inj).irrefl.irrefl _ hr
    have hlt : positiveCellToLifted M x < positiveCellToLifted M a.val := by
      rcases hcomp with h|h
      · exact lt_of_le_of_ne h (fun he => hne (positiveCellToLifted_injective M inj he))
      · obtain ⟨_,hh,_⟩ := positiveEarlier_upper_eq M z hz inj a.val x
          (lt_of_le_of_ne h hne.symm) hr
        exact (hh hs).elim
    refine ⟨hlt,?_⟩
    intro he
    rw [he] at hr
    exact positiveEarlier_asymm M z hz inj (positiveMatch_lower_before M z hz inj a hs) hr
  · rintro ⟨hlt,hne⟩
    refine ⟨?_,Or.inl hlt.le⟩
    rcases positive_lt_orientation M z hz inj x a.val hlt with h|⟨hx,_,hm,_⟩
    · exact h
    · have he := positiveMatch_symm_value M z hz inj ⟨x,hx⟩ a hm
      exact (hne he.symm).elim

noncomputable def positiveEarlierLink_upper_iso (a : NoncriticalPositiveCell M)
    (hs : matchingLetter M z hz a ∈ a.val.2.val) :
    WeightEarlierLink (PositiveEarlier M z hz inj) a.val ≃o
      {x : PositiveCellPoset M inj // positiveCellToLifted M x < positiveCellToLifted M a.val ∧
        x ≠ (positiveMatch M z hz inj a).val} where
  toFun x := ⟨x.val,(positiveEarlierLink_upper_iff M z hz inj a hs x.val).mp x.property⟩
  invFun x := ⟨x.val,(positiveEarlierLink_upper_iff M z hz inj a hs x.val).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by intros; rfl

end HarmonicArtin

end OAI
