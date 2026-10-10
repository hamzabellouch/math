import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular
import OAI.SetTheory.PartitionPrinciple.Geometry.RationalOrderBounds

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps

universe u v w

namespace LinearHeightOrder

variable {Column : Type v} {Coord : Type w}

def lex (C : LinearHeightOrder Column) (D : LinearHeightOrder Coord) :
    LinearHeightOrder (Column × Coord) where
  lt x y := C.lt x.1 y.1 ∨ x.1 = y.1 ∧ D.lt x.2 y.2
  irrefl x h := by
    rcases h with h | ⟨_, h⟩
    · exact C.irrefl x.1 h
    · exact D.irrefl x.2 h
  trans h h' := by
    rcases h with h | ⟨eq, h⟩
    · rcases h' with h' | ⟨eq, _⟩
      · exact Or.inl (C.trans h h')
      · exact Or.inl (eq ▸ h)
    · rcases h' with h' | ⟨eq', h'⟩
      · exact Or.inl (eq ▸ h')
      · exact Or.inr ⟨eq.trans eq', D.trans h h'⟩
  compare x y := by
    rcases C.compare x.1 y.1 with h | eq | h
    · exact Or.inl (Or.inl h)
    · rcases D.compare x.2 y.2 with h | eq' | h
      · exact Or.inl (Or.inr ⟨eq, h⟩)
      · exact Or.inr (Or.inl (Prod.ext eq eq'))
      · exact Or.inr (Or.inr (Or.inr ⟨eq.symm, h⟩))
    · exact Or.inr (Or.inr (Or.inl h))

end LinearHeightOrder

namespace RationalHeights

variable {A : Type u} {Column : Type v} {P : MeetOrder A}
    (C : LinearHeightOrder Column)

def lexOrder : LinearHeightOrder (Column × Rational) := C.lex Rational.order.toLinearHeightOrder

theorem local_assignment (seed : StrictHeight P (lexOrder C).toHeightOrder)
    (base : A) (countable : CountableRange seed.value)
    (lo hi : Column × Rational) (gap : (lexOrder C).lt lo hi) :
    ∃ height : StrictHeight P (lexOrder C).toHeightOrder,
      (∀ x, (lexOrder C).lt lo (height.value x)) ∧
      (∀ x, (lexOrder C).lt (height.value x) hi) ∧
      (∀ x, (height.value x).1 = lo.1) := by
  have construct (upper : Rational) (qgap : Rational.lt lo.2 upper)
      (upper_ok : ∀ q, Rational.lt q upper → (lexOrder C).lt (lo.1, q) hi) :
      ∃ height : StrictHeight P (lexOrder C).toHeightOrder,
        (∀ x, (lexOrder C).lt lo (height.value x)) ∧
        (∀ x, (lexOrder C).lt (height.value x) hi) ∧
        (∀ x, (height.value x).1 = lo.1) := by
    rcases countable_range_interpolation (lexOrder C) Rational.order seed.value
      base countable lo.2 upper qgap with ⟨assign, bounds, strict, _⟩
    let height : StrictHeight P (lexOrder C).toHeightOrder := {
      value := fun x => (lo.1, assign x)
      strict := fun x y lower different => Or.inr ⟨rfl, strict x y (seed.strict x y lower different)⟩ }
    exact ⟨height, fun x => Or.inr ⟨rfl, (bounds x).1⟩,
      fun x => upper_ok (assign x) (bounds x).2, fun _ => rfl⟩
  rcases gap with columns | ⟨same, coordinates⟩
  · rcases Rational.unbounded_above lo.2 with ⟨upper, qupper⟩
    exact construct upper qupper (fun _ _ => Or.inl columns)
  · exact construct hi.2 coordinates (fun _ h => Or.inr ⟨same, h⟩)

noncomputable def intervalHeights (seed : StrictHeight P (lexOrder C).toHeightOrder)
    (base : A) (countable : CountableRange seed.value) :
    IntervalHeights P (lexOrder C).toHeightOrder where
  assign lo hi gap := Classical.choose (local_assignment C seed base countable lo hi gap)
  lower lo hi gap := (Classical.choose_spec (local_assignment C seed base countable lo hi gap)).1
  upper lo hi gap := (Classical.choose_spec (local_assignment C seed base countable lo hi gap)).2.1
  column lo hi gap := (Classical.choose_spec (local_assignment C seed base countable lo hi gap)).2.2

end RationalHeights

namespace TaskSystem

open RationalHeights

variable {A G Task Label : Type u} {P : MeetOrder A} (f : TaskSystem P G Task Label)
    {Column : Type v} (C : LinearHeightOrder Column)
    (seed : StrictHeight P (lexOrder C).toHeightOrder) (countable : CountableRange seed.value)

noncomputable def rationalUnionHeight : StrictHeight f.unionOrder (lexOrder C).toHeightOrder :=
  f.unionHeight (intervalHeights C seed f.top countable) seed

theorem rationalUnionHeight_original (x : A) :
    (f.rationalUnionHeight C seed countable).value (f.originalEmbedding.toFun x) = seed.value x := rfl

theorem rationalUnionHeight_bounded (x : f.Union) :
    (lexOrder C).Weak ((f.rationalUnionHeight C seed countable).value x) (seed.value f.top) :=
  f.unionHeight_bounded (intervalHeights C seed f.top countable) seed x

theorem rationalUnionHeight_countable : CountableRange (f.rationalUnionHeight C seed countable).value :=
  f.unionHeight_countable (intervalHeights C seed f.top countable) seed countable
    Rational.code Rational.code_injective

include countable in

theorem rational_height_extension :
    ∃ height : StrictHeight f.unionOrder (lexOrder C).toHeightOrder,
      (∀ x, height.value (f.originalEmbedding.toFun x) = seed.value x) ∧
      CountableRange height.value ∧
      (∀ x, (lexOrder C).Weak (height.value x) (seed.value f.top)) :=
  ⟨f.rationalUnionHeight C seed countable, f.rationalUnionHeight_original C seed countable,
    f.rationalUnionHeight_countable C seed countable, f.rationalUnionHeight_bounded C seed countable⟩

end TaskSystem

end PartitionPilot.Compression.RecursiveMaps



namespace PartitionPilot.Compression.RecursiveMaps.TaskSystem

open Cardinal
open scoped Cardinal

universe u

variable {A G Task Label : Type u} {P : MeetOrder A} (f : TaskSystem P G Task Label)

theorem union_cardinal_bound : #f.Union ≤ max ℵ₀ (max #Task #A) := by
  let bound : Cardinal.{u} := max ℵ₀ (max #Task #A)
  have infinite : ℵ₀ ≤ bound := le_max_left _ _
  have task : #Task ≤ bound := (le_max_left _ _).trans (le_max_right _ _)
  have original : #A ≤ bound := (le_max_right _ _).trans (le_max_right _ _)
  have words : #(List Task) ≤ bound := (mk_list_le_max Task).trans (max_le infinite task)
  have code : #f.Union ≤ #(List Task × A) :=
    mk_le_of_injective (fun {x y} h => f.nodeCode_injective x y h)
  calc
    #f.Union ≤ #(List Task × A) := code
    _ = #(List Task) * #A := by simp only [mk_prod, lift_id]
    _ ≤ bound * bound := mul_le_mul' words original
    _ = bound := mul_eq_self infinite

theorem union_cardinal_lt (κ : Cardinal.{u}) (uncountable : ℵ₀ < κ)
    (original : #A < κ) (tasks : #Task < κ) : #f.Union < κ :=
  (f.union_cardinal_bound).trans_lt (max_lt uncountable (max_lt tasks original))

end PartitionPilot.Compression.RecursiveMaps.TaskSystem



namespace PartitionPilot.Compression.RecursiveMaps.SizeBounds

open Cardinal
open scoped Cardinal
universe u
variable (κ : Cardinal.{u}) (inaccessible : κ.IsInaccessible)
variable {A B I : Type u}
include inaccessible

theorem countable_lt [Countable A] : #A < κ := (mk_le_aleph0 (α := A)).trans_lt inaccessible.1

theorem prod_lt (left : #A < κ) (right : #B < κ) : #(A × B) < κ := by
  rw [mk_prod, lift_id, lift_id]
  exact mul_lt_of_lt inaccessible.1.le left right

theorem sum_lt (left : #A < κ) (right : #B < κ) : #(A ⊕ B) < κ := by
  rw [mk_sum, lift_id, lift_id]
  exact add_lt_of_lt inaccessible.1.le left right

theorem option_lt (small : #A < κ) : #(Option A) < κ := by
  rw [mk_option]
  exact add_lt_of_lt inaccessible.1.le small (one_lt_aleph0.trans inaccessible.1)

theorem list_lt (small : #A < κ) : #(List A) < κ :=
  (mk_list_le_max A).trans_lt (max_lt inaccessible.1 small)

theorem sets_lt (small : #A < κ) : #(Set A) < κ := by
  rw [mk_set]
  exact inaccessible.isStrongPrelimit small

omit inaccessible in
theorem subtype_lt (small : #A < κ) (p : A → Prop) : #(Subtype p) < κ :=
  (mk_subtype_le p).trans_lt small

theorem sigma_lt (small : #I < κ) (B : I → Type u) (fibers : ∀ i, #(B i) < κ) :
    #(Sigma B) < κ := by
  rw [mk_sigma]
  exact sum_lt_of_isRegular inaccessible.isRegular small fibers

theorem image_cover_lt (small : #I < κ) (B : I → Type u) (fibers : ∀ i, #(B i) < κ)
    (map : ∀ i, B i → A) (cover : ∀ x, ∃ i y, map i y = x) : #A < κ := by
  have onto : Function.Surjective (fun x : Sigma B => map x.1 x.2) := by
    intro x
    rcases cover x with ⟨i, y, eq⟩
    exact ⟨⟨i, y⟩, eq⟩
  exact (mk_le_of_surjective onto).trans_lt (sigma_lt κ inaccessible small B fibers)

end PartitionPilot.Compression.RecursiveMaps.SizeBounds

end OAI
