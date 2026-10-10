import OAI.RingTheory.DirectFiniteness.WordDiagrams

namespace OAI

universe u_1 u_2

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.WordReduction
variable {α : Type u_1}
abbrev Word (α : Type u_2) := List (α × Bool)

inductive Delete (Allowed : Word α → Prop) : Word α → Word α → Prop
  | block (pre r post : Word α) (hr : Allowed r) :
      Delete Allowed (pre ++ r ++ post) (pre ++ post)

abbrev Related (Allowed : Word α → Prop) := Relation.EqvGen (Delete Allowed)

variable {Allowed : Word α → Prop}

lemma rel_trans {u v w : Word α} (h₁ : Related Allowed u v) (h₂ : Related Allowed v w) :
    Related Allowed u w := Relation.EqvGen.trans _ _ _ h₁ h₂

lemma rel_symm {u v : Word α} (h : Related Allowed u v) :
    Related Allowed v u := Relation.EqvGen.symm _ _ h

lemma Related.append_left {u v : Word α} (h : Related Allowed u v) (w : Word α) :
    Related Allowed (w ++ u) (w ++ v) := by
  induction h with
  | rel x y h =>
    cases h with
    | block pre r post hr =>
      simpa only [List.append_assoc] using Relation.EqvGen.rel _ _ (Delete.block (w ++ pre) r post hr)
  | refl x => exact .refl _
  | symm _ _ _ ih => exact rel_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact rel_trans ih₁ ih₂

lemma Related.append_right {u v : Word α} (h : Related Allowed u v) (w : Word α) :
    Related Allowed (u ++ w) (v ++ w) := by
  induction h with
  | rel x y h =>
    cases h with
    | block pre r post hr =>
      simpa only [List.append_assoc] using Relation.EqvGen.rel _ _ (Delete.block pre r (post ++ w) hr)
  | refl x => exact .refl _
  | symm _ _ _ ih => exact rel_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact rel_trans ih₁ ih₂

lemma Related.inv (hinv : ∀ w, Allowed w → Allowed (FreeGroup.invRev w))
    {u v : Word α} (h : Related Allowed u v) :
    Related Allowed (FreeGroup.invRev u) (FreeGroup.invRev v) := by
  induction h with
  | rel x y h =>
    cases h with
    | block pre r post hr =>
      simpa only [FreeGroup.invRev_append, List.append_assoc] using
        Relation.EqvGen.rel _ _ (Delete.block (FreeGroup.invRev post) (FreeGroup.invRev r)
          (FreeGroup.invRev pre) (hinv r hr))
  | refl x => exact .refl _
  | symm _ _ _ ih => exact rel_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact rel_trans ih₁ ih₂

lemma related_of_red_step
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)])
    {u v : Word α} (h : FreeGroup.Red.Step u v) : Related Allowed u v := by
  cases h with
  | @not pre post a b =>
    simpa using Relation.EqvGen.rel _ _ (Delete.block pre [(a, b), (a, !b)] post (hcancel a b))

lemma related_of_red
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)])
    {u v : Word α} (h : FreeGroup.Red u v) : Related Allowed u v := by
  induction h with
  | refl => exact .refl _
  | tail h hstep ih => exact rel_trans ih (related_of_red_step hcancel hstep)

lemma related_of_mk_eq
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)])
    {u v : Word α} (h : FreeGroup.mk u = FreeGroup.mk v) : Related Allowed u v := by
  obtain ⟨w, huw, hvw⟩ := FreeGroup.Red.exact.mp h
  exact rel_trans (related_of_red hcancel huw) (rel_symm (related_of_red hcancel hvw))

lemma related_append_null {u v : Word α} (hu : Related Allowed u [])
    (hv : Related Allowed v []) : Related Allowed (u ++ v) [] := by
  exact rel_trans (hu.append_right v) (by simpa using hv)

/-- Words reducible to the empty word form a subgroup of the free group. -/
def nullSubgroup (Allowed : Word α → Prop)
    (hinv : ∀ w, Allowed w → Allowed (FreeGroup.invRev w)) : Subgroup (FreeGroup α) where
  carrier g := ∃ w : Word α, FreeGroup.mk w = g ∧ Related Allowed w []
  one_mem' := ⟨[], rfl, .refl _⟩
  mul_mem' := by
    rintro _ _ ⟨u, rfl, hu⟩ ⟨v, rfl, hv⟩
    exact ⟨u ++ v, FreeGroup.mul_mk.symm, related_append_null hu hv⟩
  inv_mem' := by
    rintro _ ⟨w, rfl, hw⟩
    exact ⟨FreeGroup.invRev w, FreeGroup.inv_mk.symm, by simpa using hw.inv hinv⟩

lemma nullSubgroup_normal
    (hinv : ∀ w, Allowed w → Allowed (FreeGroup.invRev w))
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)]) :
    (nullSubgroup Allowed hinv).Normal := by
  constructor
  rintro g ⟨w, rfl, hw⟩ u
  induction u using Quot.inductionOn with
  | h v =>
    change ∃ z, FreeGroup.mk z = FreeGroup.mk v * FreeGroup.mk w * (FreeGroup.mk v)⁻¹ ∧ _
    refine ⟨v ++ w ++ FreeGroup.invRev v, ?_, ?_⟩
    · rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
    · have h₁ := (hw.append_left v).append_right (FreeGroup.invRev v)
      simp only [List.append_nil] at h₁
      apply rel_trans h₁
      apply related_of_mk_eq hcancel
      rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
      simp only [mul_inv_cancel, ← FreeGroup.one_eq_mk]

/-- Equality with the identity in the actual presentation gives a finite
sequence of contiguous relator insertions/deletions, with no assumed diagrams. -/
theorem of_presented_eq_one (rels : Set (FreeGroup α))
    (hinv : ∀ w, Allowed w → Allowed (FreeGroup.invRev w))
    (hcancel : ∀ a b, Allowed [(a, b), (a, !b)])
    (hrels : ∀ g ∈ rels, ∃ w : Word α, FreeGroup.mk w = g ∧ Allowed w)
    (w : Word α) (hw : PresentedGroup.mk rels (FreeGroup.mk w) = 1) :
    Related Allowed w [] := by
  let H := nullSubgroup Allowed hinv
  let : H.Normal := nullSubgroup_normal hinv hcancel
  have hle : Subgroup.normalClosure rels ≤ H := by
    apply Subgroup.normalClosure_le_normal
    intro g hg
    obtain ⟨v, hv, hA⟩ := hrels g hg
    refine ⟨v, hv, ?_⟩
    simpa using Relation.EqvGen.rel _ _ (Delete.block [] v [] hA)
  obtain ⟨v, hv, hnull⟩ := hle (PresentedGroup.mk_eq_one_iff.mp hw)
  exact rel_trans (related_of_mk_eq hcancel hv.symm) hnull

end KaplanskyCounterexample.WordReduction

end

end OAI
