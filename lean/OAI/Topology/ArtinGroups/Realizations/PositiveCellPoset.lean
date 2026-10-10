import Mathlib
import OAI.Topology.ArtinGroups.Realizations.PositiveRootCell
import OAI.Topology.ArtinGroups.Harmonic.PositiveRegion

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] (M : CoxeterMatrix S)

omit [Fintype S] in
lemma positiveCellToLifted_injective (inj : Function.Injective (positiveToArtin M)) :
    Function.Injective (positiveCellToLifted M) := by
  intro a b h
  exact Prod.ext (inj (congrArg (fun c : LiftedCell M => c.1) h))
    (congrArg (fun c : LiftedCell M => c.2) h)

@[reducible] def PositiveCellPoset (_inj : Function.Injective (positiveToArtin M)) := PositiveLiftedCell M

instance (inj : Function.Injective (positiveToArtin M)) : PartialOrder (PositiveCellPoset M inj) :=
  PartialOrder.lift (positiveCellToLifted M) (positiveCellToLifted_injective M inj)

omit [Fintype S] in
lemma positiveCellPoset_le_iff (inj : Function.Injective (positiveToArtin M))
    (a b : PositiveCellPoset M inj) : a ≤ b ↔ positiveCellToLifted M a ≤ positiveCellToLifted M b := Iff.rfl

noncomputable def positiveCellRegionIso (inj : Function.Injective (positiveToArtin M)) :
    PositiveCellPoset M inj ≃o PositiveRegion M 1 where
  toFun a := ⟨positiveCellToLifted M a, a.1, by simp [positiveCellToLifted]⟩
  invFun a := (a.property.choose,a.val.2)
  left_inv a := by
    apply Prod.ext
    · apply inj
      simpa only [positiveCellToLifted,one_mul] using
        (Exists.choose_spec (show ∃ p, (positiveCellToLifted M a).1 = 1*positiveToArtin M p from
            ⟨a.1,by simp [positiveCellToLifted]⟩)).symm
    · rfl
  right_inv a := by
    apply Subtype.ext
    exact Prod.ext (by simpa only [positiveCellToLifted,one_mul] using a.property.choose_spec.symm) rfl
  map_rel_iff' := by intros; rfl

omit [Fintype S] in
lemma topBlockMatchingKey_cases {s : S} {A B : Finset S} (hAB : A ⊂ B) :
    topBlockMatchingKey s A < topBlockMatchingKey s B ∨
      (s ∉ A ∧ B = insert s A ∧ topBlockMatchingKey s B < topBlockMatchingKey s A) := by
  have hsub : A.erase s ⊆ B.erase s := Finset.erase_subset_erase s hAB.1
  by_cases he : A.erase s = B.erase s
  · have hsB : s ∈ B := by
      by_contra hsB
      have hsA : s ∉ A := fun h => hsB (hAB.1 h)
      rw [Finset.erase_eq_of_notMem hsA,Finset.erase_eq_of_notMem hsB] at he
      exact hAB.2 he.symm.subset
    have hsA : s ∉ A := by
      intro hsA
      have he' := congrArg (insert s) he
      rw [Finset.insert_erase hsA,Finset.insert_erase hsB] at he'
      exact hAB.2 he'.symm.subset
    have he' : B = insert s A := by
      rw [←Finset.insert_erase hsB,←he,Finset.erase_eq_of_notMem hsA]
    exact Or.inr ⟨hsA,he',topBlockStep_key (Or.inl ⟨hsA,he'⟩)⟩
  · have hc : (A.erase s).card < (B.erase s).card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,he⟩)
    left
    unfold topBlockMatchingKey
    split_ifs <;> omega

variable [LinearOrder S]
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

def PositiveEarlier (a b : PositiveCellPoset M inj) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) WellOrderingRel)
    (positiveDegree M (positiveCellTop M a),(positiveMatchingTypeKey M z hz a,a))
    (positiveDegree M (positiveCellTop M b),(positiveMatchingTypeKey M z hz b,b))

lemma positiveEarlier_iff (a b : PositiveCellPoset M inj) :
    PositiveEarlier M z hz inj a b ↔
      positiveDegree M (positiveCellTop M a) < positiveDegree M (positiveCellTop M b) ∨
      positiveDegree M (positiveCellTop M a) = positiveDegree M (positiveCellTop M b) ∧
        (positiveMatchingTypeKey M z hz a < positiveMatchingTypeKey M z hz b ∨
          positiveMatchingTypeKey M z hz a = positiveMatchingTypeKey M z hz b ∧ WellOrderingRel a b) := by
  simp only [PositiveEarlier,Prod.lex_iff]

lemma positiveEarlier_wf : WellFounded (PositiveEarlier M z hz inj) :=
  InvImage.wf (fun a : PositiveCellPoset M inj =>
    (positiveDegree M (positiveCellTop M a),(positiveMatchingTypeKey M z hz a,a)))
      (wellFounded_lt.prod_lex (wellFounded_lt.prod_lex WellOrderingRel.isWellOrder.wf))

lemma positiveEarlier_total (a b : PositiveCellPoset M inj) (hne : a ≠ b) :
    PositiveEarlier M z hz inj a b ∨ PositiveEarlier M z hz inj b a := by
  rw [positiveEarlier_iff,positiveEarlier_iff]
  rcases lt_trichotomy (positiveDegree M (positiveCellTop M a))
      (positiveDegree M (positiveCellTop M b)) with h|he|h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy (positiveMatchingTypeKey M z hz a)
        (positiveMatchingTypeKey M z hz b) with h|he'|h
    · exact Or.inl (Or.inr ⟨he,Or.inl h⟩)
    · rcases trichotomous_of WellOrderingRel a b with h|hab|h
      · exact Or.inl (Or.inr ⟨he,Or.inr ⟨he',h⟩⟩)
      · exact (hne hab).elim
      · exact Or.inr (Or.inr ⟨he.symm,Or.inr ⟨he'.symm,h⟩⟩)
    · exact Or.inr (Or.inr ⟨he.symm,Or.inl h⟩)
  · exact Or.inr (Or.inl h)

lemma positiveEarlier_root (a : PositiveCellPoset M inj) :
    ¬PositiveEarlier M z hz inj a (positiveRootCell M) := by
  intro h
  have hr := (positiveCellTop_eq_one_iff M (positiveRootCell M)).mpr rfl
  have hd : positiveDegree M (positiveCellTop M (positiveRootCell M)) = 0 := by
    rw [hr,positiveDegree_one]
  have ha : a = positiveRootCell M := by
    apply (positiveCellTop_eq_one_iff M a).mp
    apply (positiveDegree_zero_iff M _).mp
    rw [positiveEarlier_iff,hd] at h
    omega
  subst a
  exact (positiveEarlier_wf M z hz inj).irrefl.irrefl _ h

end HarmonicArtin

end OAI
