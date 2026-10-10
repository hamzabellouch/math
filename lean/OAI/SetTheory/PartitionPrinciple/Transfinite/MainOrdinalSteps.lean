import OAI.SetTheory.PartitionPrinciple.Geometry.MainEndpoints

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

namespace CountableColumns

instance below_countable (a : Column) : Countable (Set.Iio a) := by
  let : Countable (Set.Iio a.val) := (initialSegment_countable a).to_subtype
  let f : Set.Iio a → Set.Iio a.val := fun i => ⟨i.val.val, i.property⟩
  have injective : Function.Injective f := by
    intro i j eq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun k : Set.Iio a.val => k.val) eq
  exact injective.countable

theorem start_val (a : Column) : (start a).val = Order.succ a.val := by
  change a.val + (1 : Nat) = _
  rw [Nat.cast_one, Order.succ_eq_add_one]

def predecessor (a : Column) : Set.Iio (start a) := ⟨a, lt_start a⟩

theorem predecessor_greatest (a : Column) (i : Set.Iio (start a)) : i ≤ predecessor a := by
  change i.val.val ≤ a.val
  have h := i.property
  change i.val.val < (start a).val at h
  rw [start_val] at h
  exact Order.lt_succ_iff.mp h

theorem limit_no_last (a : Column) (limit : Order.IsSuccLimit a.val) :
    ¬ ∃ last : Set.Iio a, ∀ i, i ≤ last := by
  rintro ⟨last, greatest⟩
  have small : start last.val < a := by
    change (start last.val).val < a.val
    rw [start_val]
    exact limit.succ_lt last.property
  exact (not_le_of_gt (lt_start last.val)) (greatest ⟨start last.val, small⟩)

end CountableColumns

namespace MainStage
open CountableColumns

noncomputable def ordinalStep (Label : Type 1) (a : Column) (d : Diagram (Set.Iio a)) : d.Cone := by
  classical
  exact if inhabited : Nonempty (Set.Iio a) then
    if hasLast : ∃ last : Set.Iio a, ∀ i, i ≤ last then
      (d.lastCone hasLast.choose hasLast.choose_spec).extend (d := d)
        ((d.stage hasLast.choose).nextTransition Label)
    else
      letI := inhabited
      d.limitCone
  else {
    apex := initial
    leg := fun i => False.elim (inhabited ⟨i⟩)
    coherent := fun {i} => False.elim (inhabited ⟨i⟩) }

theorem ordinalStep_empty (Label : Type 1) (a : Column) (d : Diagram (Set.Iio a))
    (empty : ¬ Nonempty (Set.Iio a)) : (ordinalStep Label a d).apex = initial := by
  simp only [ordinalStep, dite_eq_right empty]

theorem ordinalStep_last (Label : Type 1) (a : Column) (d : Diagram (Set.Iio a))
    (last : Set.Iio a) (greatest : ∀ i, i ≤ last) :
    (ordinalStep Label a d).apex = (d.stage last).next Label := by
  have inhabited : Nonempty (Set.Iio a) := ⟨last⟩
  have hasLast : ∃ last : Set.Iio a, ∀ i, i ≤ last := ⟨last, greatest⟩
  have eq : hasLast.choose = last := le_antisymm (greatest _) (hasLast.choose_spec last)
  simp only [ordinalStep, dite_eq_left inhabited, dite_eq_left hasLast,
    Diagram.Cone.extend, Diagram.lastCone]
  rw [eq]

theorem ordinalStep_limit (Label : Type 1) (a : Column) (d : Diagram (Set.Iio a))
    (limit : Order.IsSuccLimit a.val) :
    letI : Nonempty (Set.Iio a) := ⟨⟨natural 0, limit.pos⟩⟩
    (ordinalStep Label a d).apex = d.limit := by
  let : Nonempty (Set.Iio a) := ⟨⟨natural 0, limit.pos⟩⟩
  simp only [ordinalStep, dite_eq_left (inferInstance : Nonempty (Set.Iio a)),
    dite_eq_right (limit_no_last a limit), Diagram.limitCone]

theorem ordinalStep_zero (Label : Type 1) (d : Diagram (Set.Iio (natural 0))) :
    (ordinalStep Label (natural 0) d).apex = initial := by
  apply ordinalStep_empty
  rintro ⟨i⟩
  exact (not_lt_of_ge (zero_le : 0 ≤ i.val.val)) i.property

theorem ordinalStep_successor (Label : Type 1) (a : Column)
    (d : Diagram (Set.Iio (start a))) :
    (ordinalStep Label (start a) d).apex = (d.stage (predecessor a)).next Label :=
  ordinalStep_last Label (start a) d (predecessor a) (predecessor_greatest a)

theorem ordinalStep_strict_top (Label : Type 1) (a : Column) (d : Diagram (Set.Iio a))
    (i : Set.Iio a) (x : (d.stage i).Point) :
    ¬ (ordinalStep Label a d).apex.order.le (ordinalStep Label a d).apex.top
      (((ordinalStep Label a d).leg i).points.toFun x) := by
  classical
  have inhabited : Nonempty (Set.Iio a) := ⟨i⟩
  by_cases hasLast : ∃ last : Set.Iio a, ∀ i, i ≤ last
  · have eq : ordinalStep Label a d =
        (d.lastCone hasLast.choose hasLast.choose_spec).extend (d := d)
          ((d.stage hasLast.choose).nextTransition Label) :=
      (dite_eq_left inhabited).trans (dite_eq_left hasLast)
    rw [eq]
    exact (d.stage _).next_strict_top Label ((d.transition _).points.toFun x)
  · let := inhabited
    have eq : ordinalStep Label a d = d.limitCone :=
      (dite_eq_left inhabited).trans (dite_eq_right hasLast)
    rw [eq]
    exact d.limit_strict_top i x

noncomputable def ordinalAppend (Label : Type 1) (a : Column)
    (d : Diagram (Set.Iio a)) : Diagram (Set.Iic a) := (ordinalStep Label a d).append

theorem ordinalAppend_restrict (Label : Type 1) (a : Column) (d : Diagram (Set.Iio a)) :
    (ordinalAppend Label a d).reindex
      (fun i : Set.Iio a => (⟨i.val, (show i.val < a from i.property).le⟩ : Set.Iic a))
      (fun _ _ h => h) = d :=
  (ordinalStep Label a d).append_restrict

end MainStage

end PartitionPilot.Compression.RecursiveMaps

end

end OAI
