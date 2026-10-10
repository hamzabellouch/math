import OAI.SetTheory.PartitionPrinciple.Transfinite.ChronologicalTheorem

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.Chronological

open RationalHeights

universe u v

def columnOrder (Column : Type v) [LinearOrder Column] : LinearHeightOrder Column where
  lt := (· < ·)
  irrefl := lt_irrefl
  trans := lt_trans
  compare := lt_trichotomy

theorem rational_decreasing_countable {Index : Type u} {Column : Type v}
    [LinearOrder Index] [WellFoundedLT Index] [LinearOrder Column] [WellFoundedLT Column]
    (value : Index → Column × Rational)
    (decreasing : ∀ i j, i < j → (lexOrder (columnOrder Column)).lt (value j) (value i)) :
    Countable Index := by
  classical
  have injective : Function.Injective value := by
    intro i j eq
    rcases lt_trichotomy i j with h | h | h
    · have impossible := decreasing i j h
      rw [eq] at impossible
      exact False.elim ((lexOrder (columnOrder Column)).irrefl _ impossible)
    · exact h
    · have impossible := decreasing j i h
      rw [eq] at impossible
      exact False.elim ((lexOrder (columnOrder Column)).irrefl _ impossible)
  have columns : ∀ i j, i ≤ j → (value j).1 ≤ (value i).1 := by
    intro i j lower
    rcases lt_or_eq_of_le lower with less | rfl
    · rcases decreasing i j less with h | ⟨h, _⟩
      · exact le_of_lt h
      · exact le_of_eq h
    · exact le_refl _
  have fiber : ∀ c : Column, Set.Countable {i : Index | (value i).1 = c} := by
    intro c
    apply Function.Injective.countable
      (f := fun i : {i : Index // (value i).1 = c} => Rational.code (value i.val).2)
    intro i j eq
    apply Subtype.ext
    apply injective
    exact Prod.ext (i.property.trans j.property.symm) (Rational.code_injective _ _ eq)
  have wf : WellFounded ((· < ·) : Column → Column → Prop) := wellFounded_lt
  have tails : ∀ c : Column, ∀ i : Index, (value i).1 = c → Set.Countable {j | i ≤ j} := by
    intro c
    induction c using wf.induction with
    | h c ih =>
      intro i eq
      let lower : Set Index := {j | i ≤ j ∧ (value j).1 < c}
      by_cases nonempty : lower.Nonempty
      · have iwf : WellFounded ((· < ·) : Index → Index → Prop) := wellFounded_lt
        rcases iwf.has_min lower nonempty with ⟨j, hj, minimal⟩
        have rest : Set.Countable {k | j ≤ k} := ih (value j).1 hj.2 j rfl
        apply ((fiber c).union rest).mono
        intro k hk
        by_cases column : (value k).1 = c
        · exact Or.inl column
        · right
          have upper : (value k).1 ≤ c := eq ▸ columns i k hk
          have less : (value k).1 < c := lt_of_le_of_ne upper column
          exact le_of_not_gt (minimal k ⟨hk, less⟩)
      · apply (fiber c).mono
        intro j hj
        have upper : (value j).1 ≤ c := eq ▸ columns i j hj
        show (value j).1 = c
        apply Classical.byContradiction
        intro different
        exact nonempty ⟨j, hj, lt_of_le_of_ne upper different⟩
  by_cases nonempty : (Set.univ : Set Index).Nonempty
  · have iwf : WellFounded ((· < ·) : Index → Index → Prop) := wellFounded_lt
    rcases iwf.has_min Set.univ nonempty with ⟨i, _, minimal⟩
    apply Set.countable_univ_iff.mp
    apply (tails (value i).1 i rfl).mono
    intro j _
    exact le_of_not_gt (minimal j (Set.mem_univ j))
  · apply Set.countable_univ_iff.mp
    rw [Set.not_nonempty_iff_eq_empty.mp nonempty]
    exact Set.countable_empty

theorem rational_descending_property {Stage : Type u} {Column : Type v}
    [LinearOrder Stage] [WellFoundedLT Stage] [LinearOrder Column] [WellFoundedLT Column] :
    DescendingCountable (Stage := Stage) (lexOrder (columnOrder Column)).toHeightOrder := by
  intro S value decreasing
  exact rational_decreasing_countable value decreasing

theorem History.rational_all_filters_countable {Stage : Type u} {Column : Type v}
    [LinearOrder Stage] [WellFoundedLT Stage] [LinearOrder Column] [WellFoundedLT Column]
    (history : History Stage (lexOrder (columnOrder Column)).toHeightOrder) :
    ∀ cutoff, AllFiltersCountable (history.order cutoff) :=
  history.all_filters_countable rational_descending_property

end PartitionPilot.Compression.RecursiveMaps.Chronological

end

end OAI
