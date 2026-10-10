import OAI.SetTheory.PartitionPrinciple.Definability.NatUnionCodes

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

def assignmentCut (levels alpha A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ xi ∈ alpha, ZFSet.pair z xi ∈ levels) A

def assignmentUpper (levels alpha A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∉ assignmentCut levels alpha A) A

def assignmentSplice (levels alpha Aq Ap : ZFSet.{u}) : ZFSet.{u} :=
  assignmentCut levels alpha Aq ∪ assignmentUpper levels alpha Ap

theorem mem_assignmentCut (levels alpha A z : ZFSet.{u}) :
    z ∈ assignmentCut levels alpha A ↔
      z ∈ A ∧ ∃ xi ∈ alpha, ZFSet.pair z xi ∈ levels :=
  ZFSet.mem_sep

theorem mem_assignmentUpper (levels alpha A z : ZFSet.{u}) :
    z ∈ assignmentUpper levels alpha A ↔
      z ∈ A ∧ ¬ ∃ xi ∈ alpha, ZFSet.pair z xi ∈ levels := by
  rw [assignmentUpper, ZFSet.mem_sep, mem_assignmentCut]
  constructor
  · rintro ⟨hz, outside⟩
    exact ⟨hz, fun lower => outside ⟨hz, lower⟩⟩
  · rintro ⟨hz, outside⟩
    exact ⟨hz, fun lower => outside lower.2⟩

theorem mem_assignmentSplice (levels alpha Aq Ap z : ZFSet.{u}) :
    z ∈ assignmentSplice levels alpha Aq Ap ↔
      (z ∈ Aq ∧ ∃ xi ∈ alpha, ZFSet.pair z xi ∈ levels) ∨
      (z ∈ Ap ∧ ¬ ∃ xi ∈ alpha, ZFSet.pair z xi ∈ levels) := by
  rw [assignmentSplice, ZFSet.mem_union, mem_assignmentCut, mem_assignmentUpper]

theorem assignmentCut_subset (levels alpha A : ZFSet.{u}) :
    assignmentCut levels alpha A ⊆ A :=
  fun _ hz => ((mem_assignmentCut levels alpha A _).1 hz).1

theorem assignmentUpper_subset (levels alpha A : ZFSet.{u}) :
    assignmentUpper levels alpha A ⊆ A :=
  fun _ hz => ((mem_assignmentUpper levels alpha A _).1 hz).1

theorem assignmentSplice_subset (levels alpha Aq Ap : ZFSet.{u}) :
    assignmentSplice levels alpha Aq Ap ⊆ Aq ∪ Ap := by
  intro z hz
  rcases (mem_assignmentSplice levels alpha Aq Ap z).1 hz with lower | upper
  · exact ZFSet.mem_union.2 (Or.inl lower.1)
  · exact ZFSet.mem_union.2 (Or.inr upper.1)

theorem assignmentCut_mono {levels alpha A B : ZFSet.{u}} (subset : A ⊆ B) :
    assignmentCut levels alpha A ⊆ assignmentCut levels alpha B := by
  intro z hz
  obtain ⟨hz, lower⟩ := (mem_assignmentCut levels alpha A z).1 hz
  exact (mem_assignmentCut levels alpha B z).2 ⟨subset hz, lower⟩

theorem assignmentCut_nested {levels alpha beta A : ZFSet.{u}}
    (below : alpha ⊆ beta) :
    assignmentCut levels alpha (assignmentCut levels beta A) =
      assignmentCut levels alpha A := by
  apply ZFSet.ext
  intro z
  rw [mem_assignmentCut, mem_assignmentCut, mem_assignmentCut]
  constructor
  · rintro ⟨⟨hz, _⟩, lower⟩
    exact ⟨hz, lower⟩
  · rintro ⟨hz, xi, hxi, entry⟩
    exact ⟨⟨hz, xi, below hxi, entry⟩, xi, hxi, entry⟩

theorem assignmentCut_eq_of_lower {levels alpha A : ZFSet.{u}}
    (lower : ∀ z ∈ A, ∃ xi ∈ alpha, ZFSet.pair z xi ∈ levels) :
    assignmentCut levels alpha A = A := by
  apply ZFSet.ext
  intro z
  rw [mem_assignmentCut]
  exact ⟨fun hz => hz.1, fun hz => ⟨hz, lower z hz⟩⟩

theorem assignmentCut_full {J eta levels A : ZFSet.{u}}
    (function : ZFSet.IsFunc J eta levels) (subset : A ⊆ J) :
    assignmentCut levels eta A = A := by
  apply assignmentCut_eq_of_lower
  intro z hz
  obtain ⟨xi, entry, _⟩ := function.2 z (subset hz)
  exact ⟨xi, (ZFSet.pair_mem_prod.1 (function.1 entry)).2, entry⟩

theorem assignmentCut_splice (levels alpha Aq Ap : ZFSet.{u}) :
    assignmentCut levels alpha (assignmentSplice levels alpha Aq Ap) =
      assignmentCut levels alpha Aq := by
  apply ZFSet.ext
  intro z
  rw [mem_assignmentCut, mem_assignmentSplice, mem_assignmentCut]
  constructor
  · rintro ⟨lower | upper, level⟩
    · exact lower
    · exact False.elim (upper.2 level)
  · intro lower
    exact ⟨Or.inl lower, lower.2⟩

theorem assignmentUpper_splice (levels alpha Aq Ap : ZFSet.{u}) :
    assignmentUpper levels alpha (assignmentSplice levels alpha Aq Ap) =
      assignmentUpper levels alpha Ap := by
  apply ZFSet.ext
  intro z
  rw [mem_assignmentUpper, mem_assignmentSplice, mem_assignmentUpper]
  constructor
  · rintro ⟨lower | upper, outside⟩
    · exact False.elim (outside lower.2)
    · exact upper
  · intro upper
    exact ⟨Or.inr upper, upper.2⟩

theorem assignmentSplice_self (levels alpha A : ZFSet.{u}) :
    assignmentSplice levels alpha A A = A := by
  classical
  apply ZFSet.ext
  intro z
  rw [mem_assignmentSplice]
  constructor
  · exact fun h => h.elim And.left And.left
  · intro hz
    by_cases lower : ∃ xi ∈ alpha, ZFSet.pair z xi ∈ levels
    · exact Or.inl ⟨hz, lower⟩
    · exact Or.inr ⟨hz, lower⟩

theorem assignmentSplice_of_lower {levels alpha Aq Ap : ZFSet.{u}}
    (lower : ∀ z ∈ Aq, ∃ xi ∈ alpha, ZFSet.pair z xi ∈ levels) :
    assignmentSplice levels alpha Aq Ap = Aq ∪ assignmentUpper levels alpha Ap ∧
      assignmentCut levels alpha (assignmentSplice levels alpha Aq Ap) = Aq := by
  have equal := assignmentCut_eq_of_lower lower
  exact ⟨by rw [assignmentSplice, equal], by rw [assignmentCut_splice, equal]⟩

theorem assignmentSplice_extends {levels alpha Aq Ap : ZFSet.{u}}
    (contains : assignmentCut levels alpha Ap ⊆ assignmentCut levels alpha Aq) :
    Ap ⊆ assignmentSplice levels alpha Aq Ap := by
  classical
  intro z hz
  by_cases lower : ∃ xi ∈ alpha, ZFSet.pair z xi ∈ levels
  · exact ZFSet.mem_union.2 (Or.inl (contains
      ((mem_assignmentCut levels alpha Ap z).2 ⟨hz, lower⟩)))
  · exact (mem_assignmentSplice levels alpha Aq Ap z).2 (Or.inr ⟨hz, lower⟩)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u
variable {levels alpha beta : ZFSet.{u}} (below : alpha ⊆ beta)
include below

theorem assignmentCut_splice_below (Aq Ap : ZFSet.{u}) :
    assignmentCut levels alpha (assignmentSplice levels beta Aq Ap) =
      assignmentCut levels alpha Aq := by
  calc
    _ = assignmentCut levels alpha
        (assignmentCut levels beta (assignmentSplice levels beta Aq Ap)) :=
      (assignmentCut_nested below).symm
    _ = assignmentCut levels alpha (assignmentCut levels beta Aq) := by rw [assignmentCut_splice]
    _ = _ := assignmentCut_nested below

theorem assignmentUpper_splice_above (Aq Ap : ZFSet.{u}) :
    assignmentUpper levels beta (assignmentSplice levels alpha Aq Ap) =
      assignmentUpper levels beta Ap := by
  apply ZFSet.ext
  intro z
  rw [mem_assignmentUpper, mem_assignmentSplice, mem_assignmentUpper]
  constructor
  · rintro ⟨lower | upper, outside⟩
    · obtain ⟨xi, hxi, entry⟩ := lower.2
      exact False.elim (outside ⟨xi, below hxi, entry⟩)
    · exact ⟨upper.1, outside⟩
  · rintro ⟨member, outside⟩
    exact ⟨Or.inr ⟨member, fun ⟨xi, hxi, entry⟩ => outside ⟨xi, below hxi, entry⟩⟩, outside⟩

theorem assignmentSplice_nested (Ar Aq Ap : ZFSet.{u}) :
    assignmentSplice levels alpha Ar (assignmentSplice levels beta Aq Ap) =
      assignmentSplice levels beta (assignmentSplice levels alpha Ar Aq) Ap := by
  classical
  apply ZFSet.ext
  intro z
  simp only [mem_assignmentSplice]
  by_cases lower : ∃ xi ∈ alpha, ZFSet.pair z xi ∈ levels
  · obtain ⟨xi, hxi, entry⟩ := lower
    have lower : ∃ xi ∈ alpha, ZFSet.pair z xi ∈ levels := ⟨xi, hxi, entry⟩
    have higher : ∃ xi ∈ beta, ZFSet.pair z xi ∈ levels := ⟨xi, below hxi, entry⟩
    simp only [lower, higher, and_true, not_true_eq_false, and_false, or_false]
  · by_cases higher : ∃ xi ∈ beta, ZFSet.pair z xi ∈ levels
    · simp only [lower, higher, and_true, not_true_eq_false, and_false, or_false,
        not_false_eq_true, false_or]
    · simp only [lower, higher, and_true, and_false, not_false_eq_true, false_or]

end PartitionPilot.Forcing

end

end OAI
