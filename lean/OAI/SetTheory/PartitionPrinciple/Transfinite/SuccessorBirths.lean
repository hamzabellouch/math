import OAI.SetTheory.PartitionPrinciple.Forcing.LimitAction

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps.CountableColumns

open scoped Cardinal
universe u

theorem initialSegment_countable (a : Column) : (Set.Iio a.val).Countable := by
  have : Countable a.val.ToType := Cardinal.mk_le_aleph0_iff.mp (by
    rw [Cardinal.mk_toType]
    exact a.property)
  exact (Ordinal.ToType.mk (o := a.val)).injective.countable

theorem sequenceSup_countable (f : Nat → Column) :
    (iSup (fun n => (f n).val)).card ≤ Cardinal.aleph0 := by
  have same : Set.Iio (iSup (fun n => (f n).val)) = ⋃ n, Set.Iio (f n).val := by
    ext a
    simp only [Set.mem_Iio, Set.mem_iUnion, Ordinal.lt_iSup_iff]
  have small : (Set.Iio (iSup (fun n => (f n).val))).Countable := by
    rw [same]
    exact Set.countable_iUnion (fun n => initialSegment_countable (f n))
  let := small.to_subtype
  let : Countable (iSup (fun n => (f n).val)).ToType :=
    (Ordinal.ToType.mk (o := iSup (fun n => (f n).val))).symm.injective.countable
  simpa only [Cardinal.mk_toType] using
    (Cardinal.mk_le_aleph0 (α := (iSup (fun n => (f n).val)).ToType))

noncomputable def sequenceSup (f : Nat → Column) : Column :=
  ⟨iSup (fun n => (f n).val), sequenceSup_countable f⟩

theorem lt_start (a : Column) : order.lt a (start a) := by
  change a.val < a.val + (1 : Nat)
  rw [Nat.cast_one, ← Order.succ_eq_add_one]
  exact Order.lt_succ _

noncomputable def upperBound {I : Type u} [Countable I] (f : I → Column) : Column :=
  start (sequenceSup (Set.enumerateCountable (Set.countable_range f) (natural 0)))

theorem upperBound_above {I : Type u} [Countable I] (f : I → Column) (i : I) :
    order.lt (f i) (upperBound f) := by
  let seq := Set.enumerateCountable (Set.countable_range f) (natural 0)
  have below : (f i).val ≤ (sequenceSup seq).val := by
    rcases Set.subset_range_enumerate (Set.countable_range f) (natural 0)
      (Set.mem_range_self i) with ⟨n, eq⟩
    change (f i).val ≤ iSup (fun n => (seq n).val)
    rw [← eq]
    exact Ordinal.le_iSup (fun n => (seq n).val) n
  exact lt_of_le_of_lt below (lt_start (sequenceSup seq))

end PartitionPilot.Compression.RecursiveMaps.CountableColumns



namespace PartitionPilot.Compression.RecursiveMaps

open RationalHeights
universe u v

namespace DirectSystem
variable {I : Type u} [LinearOrder I] [Countable I] (c : DirectSystem I)
    {H : Type v} (value : ∀ i, c.Point i → H)
    (coherent : ∀ {i j} (h : i ≤ j) x, value j (c.map h x) = value i x)

theorem descend_countable (countable : ∀ i, CountableRange (value i)) :
    CountableRange (c.descend value coherent) := by
  classical
  rcases exists_injective_nat I with ⟨indexCode, index_injective⟩
  let code (i : I) : c.Point i → Nat := Classical.choose (countable i)
  have equal (i : I) := Classical.choose_spec (countable i)
  let labelValue (x : c.Label) := value x.1 x.2
  have label_equal (x y : c.Label)
      (eq : natPair (indexCode x.1) (code x.1 x.2) = natPair (indexCode y.1) (code y.1 y.2)) :
      labelValue x = labelValue y := by
    rcases x with ⟨i, x⟩
    rcases y with ⟨j, y⟩
    rcases natPair_injective eq with ⟨same, codes⟩
    have same := index_injective same
    cases same
    exact equal i x y codes
  have out_value (x : c.Union) : labelValue (Quotient.out x) = c.descend value coherent x :=
    congrArg (c.descend value coherent) (Quotient.out_eq x)
  refine ⟨fun x => natPair (indexCode (Quotient.out x).1)
    (code (Quotient.out x).1 (Quotient.out x).2), ?_⟩
  intro x y eq
  exact (out_value x).symm.trans ((label_equal _ _ eq).trans (out_value y))

end DirectSystem

namespace MeetSystem
variable {I : Type u} [LinearOrder I] (p : MeetSystem I) {H : Type v} (R : HeightOrder H)

structure Heights where
  height : ∀ i, StrictHeight (p.order i) R
  coherent : ∀ {i j} (h : i ≤ j) x, (height j).value (p.system.map h x) = (height i).value x

namespace Heights
variable {p R} (h : Heights p R)

def unionHeight : StrictHeight p.unionOrder R where
  value := p.system.descend (fun i => (h.height i).value) h.coherent
  strict x y lower different := by
    rcases p.system.pair_cover p.system x y with ⟨i, x, y, rfl, rfl⟩
    exact (h.height i).strict x y ((p.le_stage i x y).mp lower)
      (fun eq => different (congrArg (p.system.point i) eq))

theorem unionHeight_stage (i : I) (x : p.system.Point i) :
    h.unionHeight.value ((p.inclusion i).toFun x) = (h.height i).value x := rfl

theorem unionHeight_countable [Countable I] (countable : ∀ i, CountableRange (h.height i).value) :
    CountableRange h.unionHeight.value :=
  p.system.descend_countable (fun i => (h.height i).value) h.coherent countable

end Heights
end MeetSystem

namespace MeetSystem.Heights
open CountableColumns

variable {I : Type u} [LinearOrder I] [Countable I] {p : MeetSystem I}
    (h : p.Heights (lexOrder CountableColumns.order).toHeightOrder)
    (bound : I → Column)
    (bounded : ∀ i x, ((h.height i).value x).1.val ≤ (bound i).val)

include bounded in
theorem union_column_bound (x : p.system.Union) :
    CountableColumns.order.lt (h.unionHeight.value x).1 (upperBound bound) := by
  rcases p.system.cover x with ⟨i, x, rfl⟩
  exact lt_of_le_of_lt (bounded i x) (upperBound_above bound i)

noncomputable def limitHeight :
    StrictHeight p.boundedOrder (lexOrder CountableColumns.order).toHeightOrder :=
  FixedTop.extendHeight h.unionHeight (upperBound bound, zero)
    (fun x => Or.inl (h.union_column_bound bound bounded x))

theorem limitHeight_stage (i : I) (x : p.system.Point i) :
    (h.limitHeight bound bounded).value ((p.boundedInclusion i).toFun x) =
      (h.height i).value x := rfl

theorem limitHeight_countable (countable : ∀ i, CountableRange (h.height i).value) :
    CountableRange (h.limitHeight bound bounded).value :=
  FixedTop.extendHeight_countable _ _ _ (h.unionHeight_countable countable)

theorem limitHeight_top : (h.limitHeight bound bounded).value none = (upperBound bound, zero) := rfl

theorem limitHeight_bounded (x : Option p.system.Union) :
    (lexOrder CountableColumns.order).Weak ((h.limitHeight bound bounded).value x)
      (upperBound bound, zero) :=
  (h.limitHeight bound bounded).mono (FixedTop.greatest p.unionOrder x)

include bounded in
theorem countable_limit_height (countable : ∀ i, CountableRange (h.height i).value) :
    ∃ height : StrictHeight p.boundedOrder (lexOrder CountableColumns.order).toHeightOrder,
      (∀ i x, height.value ((p.boundedInclusion i).toFun x) = (h.height i).value x) ∧
      CountableRange height.value ∧ height.value none = (upperBound bound, zero) ∧
      (∀ x, (lexOrder CountableColumns.order).Weak (height.value x) (upperBound bound, zero)) :=
  ⟨h.limitHeight bound bounded, h.limitHeight_stage bound bounded,
    h.limitHeight_countable bound bounded countable, h.limitHeight_top bound bounded,
    h.limitHeight_bounded bound bounded⟩

omit [Countable I] in
theorem stage_bound_from_top (top : ∀ i, p.system.Point i)
    (greatest : ∀ i x, (p.order i).le x (top i)) (i : I) (x : p.system.Point i) :
    ((h.height i).value x).1.val ≤ ((h.height i).value (top i)).1.val := by
  have weak := CountableColumns.order.first_weak Rational.order.toLinearHeightOrder
    ((h.height i).mono (greatest i x))
  rcases weak with eq | lower
  · exact (congrArg Subtype.val eq).le
  · exact lower.le

theorem bounded_countable_limit (top : ∀ i, p.system.Point i)
    (greatest : ∀ i x, (p.order i).le x (top i))
    (countable : ∀ i, CountableRange (h.height i).value) :
    ∃ height : StrictHeight p.boundedOrder (lexOrder CountableColumns.order).toHeightOrder,
      (∀ i x, height.value ((p.boundedInclusion i).toFun x) = (h.height i).value x) ∧
      CountableRange height.value := by
  rcases h.countable_limit_height (fun i => ((h.height i).value (top i)).1)
    (h.stage_bound_from_top top greatest) countable with ⟨height, fixed, small, _⟩
  exact ⟨height, fixed, small⟩

end MeetSystem.Heights

end PartitionPilot.Compression.RecursiveMaps



namespace PartitionPilot.Compression.RecursiveMaps

open RationalHeights CountableColumns

theorem countable_ordinal_limit
    (α : Column) (positive : 0 < α.val)
    (p : MeetSystem (Set.Iio α.val)) (g : GroupSystem (Set.Iio α.val))
    (a : ActionSystem g p)
    (h : p.Heights (lexOrder CountableColumns.order).toHeightOrder)
    (top : ∀ i, p.system.Point i)
    (greatest : ∀ i x, (p.order i).le x (top i))
    (countable : ∀ i, CountableRange (h.height i).value) :
    letI : Nonempty (Set.Iio α.val) := ⟨⟨0, positive⟩⟩
    ∃ height : StrictHeight p.boundedOrder (lexOrder CountableColumns.order).toHeightOrder,
      (∀ i x, height.value ((p.boundedInclusion i).toFun x) = (h.height i).value x) ∧
      CountableRange height.value ∧
      (∀ x, (lexOrder CountableColumns.order).Weak (height.value x) (height.value none)) ∧
      (∀ i s x, (a.topAction.iso ((g.inclusion i) s)).toFun ((p.boundedInclusion i).toFun x) =
        (p.boundedInclusion i).toFun (((a.action i).iso s).toFun x)) ∧
      (∀ s, (a.topAction.iso s).toFun none = none) ∧
      (∀ i x, p.boundedOrder.le ((p.boundedInclusion i).toFun x) none ∧
        ¬ p.boundedOrder.le none ((p.boundedInclusion i).toFun x)) := by
  let : Nonempty (Set.Iio α.val) := ⟨⟨0, positive⟩⟩
  let : Countable (Set.Iio α.val) := (initialSegment_countable α).to_subtype
  rcases h.bounded_countable_limit top greatest countable with ⟨height, fixed, small⟩
  exact ⟨height, fixed, small,
    fun x => height.mono (FixedTop.greatest p.unionOrder x),
    a.topAction_stage, a.top_fixed, p.bounded_strict_top⟩

end PartitionPilot.Compression.RecursiveMaps



namespace PartitionPilot.Compression.RecursiveMaps.DirectSystem

universe u
variable {I : Type u} [LinearOrder I] [WellFoundedLT I] (c : DirectSystem I)

def Present (x : c.Union) : Set I := {i | ∃ a, c.point i a = x}

omit [WellFoundedLT I] in
theorem present_nonempty (x : c.Union) : (c.Present x).Nonempty := c.cover x

noncomputable def birth (x : c.Union) : I :=
  wellFounded_lt.min (c.Present x) (c.present_nonempty x)

theorem present_birth (x : c.Union) : ∃ a, c.point (c.birth x) a = x :=
  wellFounded_lt.min_mem (c.Present x) (c.present_nonempty x)

theorem birth_le_iff (x : c.Union) (i : I) : c.birth x ≤ i ↔ ∃ a, c.point i a = x := by
  constructor
  · intro lower
    rcases c.present_birth x with ⟨a, eq⟩
    exact ⟨c.map lower a, (c.point_map lower a).trans eq⟩
  · intro present
    exact le_of_not_gt (wellFounded_lt.not_lt_min (c.Present x) present)

noncomputable def stageBirth (i : I) (x : c.Point i) : I := c.birth (c.point i x)

theorem stageBirth_le (i : I) (x : c.Point i) : c.stageBirth i x ≤ i :=
  (c.birth_le_iff _ i).mpr ⟨x, rfl⟩

theorem stageBirth_map {i j : I} (lower : i ≤ j) (x : c.Point i) :
    c.stageBirth j (c.map lower x) = c.stageBirth i x :=
  congrArg c.birth (c.point_map lower x)

theorem stageBirth_le_iff {i j : I} (lower : i ≤ j) (x : c.Point j) :
    c.stageBirth j x ≤ i ↔ ∃ a, c.map lower a = x := by
  constructor
  · intro old
    rcases (c.birth_le_iff (c.point j x) i).mp old with ⟨a, eq⟩
    exact ⟨a, c.point_injective j ((c.point_map lower a).trans eq)⟩
  · rintro ⟨a, rfl⟩
    rw [c.stageBirth_map]
    exact c.stageBirth_le i a

theorem born_stage_cover {i j : I} (lower : i ≤ j) (x : c.Point j)
    (born : c.stageBirth j x = i) : ∃ a, c.map lower a = x :=
  (c.stageBirth_le_iff lower x).mp born.le

theorem union_born_cover (i : I) (x : c.Union) (born : c.birth x = i) :
    ∃ a, c.point i a = x := (c.birth_le_iff x i).mp born.le

theorem stageBirth_eq_iff (j : I) (x : c.Point j) (i : I) :
    c.stageBirth j x = i ↔
      (∃ lower : i ≤ j, ∃ a, c.map lower a = x) ∧
      (∀ k, k < i → ∀ lower : k ≤ j, ¬ ∃ a, c.map lower a = x) := by
  constructor
  · intro eq
    have lower : i ≤ j := eq ▸ c.stageBirth_le j x
    refine ⟨⟨lower, c.born_stage_cover lower x eq⟩, ?_⟩
    intro k earlier lower present
    have old := (c.stageBirth_le_iff lower x).mpr present
    rw [eq] at old
    exact (not_lt_of_ge old) earlier
  · rintro ⟨⟨lower, present⟩, first⟩
    apply le_antisymm ((c.stageBirth_le_iff lower x).mpr present)
    apply le_of_not_gt
    intro earlier
    exact first (c.stageBirth j x) earlier (c.stageBirth_le j x)
      (c.born_stage_cover (c.stageBirth_le j x) x rfl)

include c in

theorem continuous_stage_no_birth (j : I)
    (cover : ∀ x : c.Point j, ∃ i, ∃ lower : i < j, ∃ a, c.map lower.le a = x)
    (x : c.Point j) : c.stageBirth j x < j := by
  rcases cover x with ⟨i, lower, a, rfl⟩
  rw [c.stageBirth_map]
  exact lt_of_le_of_lt (c.stageBirth_le i a) lower

theorem stageBirth_eq_of_records (record : ∀ i, c.Point i → I)
    (bounded : ∀ i x, record i x ≤ i)
    (coherent : ∀ {i j} (lower : i ≤ j) x, record j (c.map lower x) = record i x)
    (origin : ∀ j x, ∃ a, c.map (bounded j x) a = x)
    (j : I) (x : c.Point j) : c.stageBirth j x = record j x := by
  apply le_antisymm ((c.stageBirth_le_iff (bounded j x) x).mpr (origin j x))
  rcases c.born_stage_cover (c.stageBirth_le j x) x rfl with ⟨a, eq⟩
  calc
    record j x = record (c.stageBirth j x) a :=
      (congrArg (record j) eq).symm.trans (coherent (c.stageBirth_le j x) a)
    _ ≤ c.stageBirth j x := bounded _ a

theorem birth_eq_of_records (record : ∀ i, c.Point i → I)
    (bounded : ∀ i x, record i x ≤ i)
    (coherent : ∀ {i j} (lower : i ≤ j) x, record j (c.map lower x) = record i x)
    (origin : ∀ j x, ∃ a, c.map (bounded j x) a = x)
    (x : c.Union) : c.birth x = c.descend record coherent x := by
  rcases c.cover x with ⟨j, x, rfl⟩
  exact c.stageBirth_eq_of_records record bounded coherent origin j x

end PartitionPilot.Compression.RecursiveMaps.DirectSystem



namespace PartitionPilot.Compression.RecursiveMaps.MeetSystem

open Chronological
universe u v
variable {I : Type u} [LinearOrder I] [WellFoundedLT I] (p : MeetSystem I)

def LocalOldMeet : Prop := ∀ i (x y : p.system.Point i),
  p.system.stageBirth i x = i → p.system.stageBirth i y < i → ¬ (p.order i).le x y →
    p.system.stageBirth i ((p.order i).meet x y) < i

theorem old_meet_at (localMeet : p.LocalOldMeet) (j : I) :
    OldMeet (P := p.order j) (p.system.stageBirth j) := by
  intro x y earlier notLower
  let i := p.system.stageBirth j x
  have present : i ≤ j := p.system.stageBirth_le j x
  rcases p.system.born_stage_cover present x rfl with ⟨a, ha⟩
  rcases (p.system.stageBirth_le_iff present y).mp earlier.le with ⟨b, hb⟩
  have a_birth : p.system.stageBirth i a = i := by
    rw [← p.system.stageBirth_map present, ha]
  have b_birth : p.system.stageBirth i b < i := by
    rw [← p.system.stageBirth_map present, hb]
    exact earlier
  have notLower' : ¬ (p.order i).le a b := by
    intro lower
    have raised := (p.map_le present a b).mpr lower
    rw [ha, hb] at raised
    exact notLower raised
  have old := localMeet i a b a_birth b_birth notLower'
  have meet_birth : p.system.stageBirth j ((p.order j).meet x y) =
      p.system.stageBirth i ((p.order i).meet a b) := by
    rw [← ha, ← hb, ← p.map_meet, p.system.stageBirth_map]
  rw [meet_birth]
  exact old

theorem union_old_meet (localMeet : p.LocalOldMeet) :
    OldMeet (P := p.unionOrder) p.system.birth :=
  oldMeet_of_covered_stages p.order p.system.birth p.system.stageBirth p.inclusion
    (fun _ _ => rfl) (p.system.pair_cover p.system) (p.old_meet_at localMeet)

def OwnLayers : Type (u + 1) :=
  ∀ i, GrowthLayer p.system.Point p.order (p.order i) (p.system.stageBirth i) i

noncomputable def laterLayer (own : p.OwnLayers) (i j : I) (lower : i ≤ j) :
    GrowthLayer p.system.Point p.order (p.order j) (p.system.stageBirth j) i :=
  (own i).transport (p.transition lower) (p.system.stageBirth_map lower)
    (p.system.born_stage_cover lower)

noncomputable def unionLayer (own : p.OwnLayers) (i : I) :
    GrowthLayer p.system.Point p.order p.unionOrder p.system.birth i :=
  (own i).transport (p.inclusion i) (fun _ => rfl) (p.system.union_born_cover i)

noncomputable def history {H : Type v} {R : HeightOrder H}
    (heights : p.Heights R) (localMeet : p.LocalOldMeet) (own : p.OwnLayers) : History I R where
  Space := p.system.Point
  order := p.order
  birth := p.system.stageBirth
  birth_le := p.system.stageBirth_le
  old_meet := p.old_meet_at localMeet
  height := heights.height
  layer cutoff i lower := p.laterLayer own i cutoff lower

theorem stages_all_filters_countable {H : Type v} {R : HeightOrder H}
    (heights : p.Heights R) (localMeet : p.LocalOldMeet) (own : p.OwnLayers)
    (descending : DescendingCountable (Stage := I) R) : ∀ i, AllFiltersCountable (p.order i) :=
  (p.history heights localMeet own).all_filters_countable descending

theorem union_all_filters_countable {H : Type v} {R : HeightOrder H}
    (heights : p.Heights R) (localMeet : p.LocalOldMeet) (own : p.OwnLayers)
    (descending : DescendingCountable (Stage := I) R) : AllFiltersCountable p.unionOrder := by
  intro F
  apply countable_basis_of_layers p.system.birth F
  · exact essential_stages_countable p.system.birth heights.unionHeight descending
      (p.union_old_meet localMeet) F
  · intro i
    apply (p.unionLayer own i).countable_essentials F
    intro j _
    exact p.stages_all_filters_countable heights localMeet own descending j

end PartitionPilot.Compression.RecursiveMaps.MeetSystem



namespace PartitionPilot.Compression.RecursiveMaps.FixedTop

open Chronological
universe u v
variable {A : Type u} {Stage : Type v} [LinearOrder Stage]

def birth (oldBirth : A → Stage) (s : Stage) : Option A → Stage
  | none => s
  | some x => oldBirth x

theorem birth_le (oldBirth : A → Stage) (s : Stage) (old : ∀ x, oldBirth x < s)
    (x : Option A) : birth oldBirth s x ≤ s := by
  cases x with
  | none => exact le_rfl
  | some x => exact (old x).le

theorem birth_at_top_iff (oldBirth : A → Stage) (s : Stage) (old : ∀ x, oldBirth x < s)
    (x : Option A) : birth oldBirth s x = s ↔ x = none := by
  cases x with
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some x =>
    constructor
    · intro eq
      exact False.elim ((ne_of_lt (old x)) eq)
    · intro eq
      cases eq

theorem old_meet_preserved (P : MeetOrder A) (oldBirth : A → Stage) (s : Stage)
    (old : ∀ x, oldBirth x < s) (previous : OldMeet (P := P) oldBirth) :
    OldMeet (P := order P) (birth oldBirth s) := by
  intro x y earlier notLower
  cases x with
  | none =>
    cases y with
    | none => exact False.elim (lt_irrefl s earlier)
    | some y => exact old y
  | some x =>
    cases y with
    | none => exact False.elim (lt_asymm earlier (old x))
    | some y => exact previous x y earlier notLower

section Layers
variable {Stage : Type u} [LinearOrder Stage] (P : MeetOrder A)
    (Space : Stage → Type u) (orders : ∀ i, MeetOrder (Space i))

noncomputable def earlier_layer (oldBirth : A → Stage) (s t : Stage)
    (earlier : t < s) (layer : GrowthLayer Space orders P oldBirth t) :
    GrowthLayer Space orders (order P) (birth oldBirth s) t := by
  apply layer.transport (embedding P).toMeetEmbedding (fun _ => rfl)
  intro x hx
  cases x with
  | none =>
    change s = t at hx
    exact False.elim ((ne_of_lt earlier) hx.symm)
  | some x => exact ⟨x, rfl⟩

def incoming_layer (oldBirth : A → Stage) (s : Stage) (old : ∀ x, oldBirth x < s) :
    GrowthLayer Space orders (order P) (birth oldBirth s) s := by
  apply finiteLayer Space orders
  apply (Set.finite_singleton (none : Option A)).subset
  intro x hx
  exact (birth_at_top_iff oldBirth s old x).mp hx

end Layers

omit [LinearOrder Stage] in

theorem all_filters_countable (P : MeetOrder A) (previous : AllFiltersCountable P) :
    AllFiltersCountable (order P) := by
  intro F
  have topPositive : F.mem none := by
    rcases F.nonempty with ⟨x, positive⟩
    exact F.upward positive (greatest P x)
  rcases countableBelow_copy (embedding P).toMeetEmbedding F previous with ⟨B, small, positive, below⟩
  refine ⟨insert none B, small.insert none, ?_, ?_⟩
  · intro x hx
    rcases Set.mem_insert_iff.mp hx with eq | hx
    · exact eq ▸ topPositive
    · exact positive x hx
  · intro x hx
    cases x with
    | none => exact ⟨none, Set.mem_insert _ _, True.intro⟩
    | some x =>
      rcases below (some x) ⟨hx, x, rfl⟩ with ⟨y, hy, lower⟩
      exact ⟨y, Set.mem_insert_of_mem _ hy, lower⟩

end PartitionPilot.Compression.RecursiveMaps.FixedTop



namespace PartitionPilot.Compression.RecursiveMaps

namespace CountableColumns

noncomputable instance columnLinearOrder : LinearOrder Column :=
  inferInstanceAs (LinearOrder {o : Ordinal.{0} // o.card ≤ Cardinal.aleph0})

instance columnWellFoundedLT : WellFoundedLT Column :=
  inferInstanceAs (WellFoundedLT {o : Ordinal.{0} // o.card ≤ Cardinal.aleph0})

universe u

theorem descending_property {I : Type u} [LinearOrder I] [WellFoundedLT I] :
    Chronological.DescendingCountable (Stage := I)
      (RationalHeights.lexOrder order).toHeightOrder :=
  Chronological.rational_descending_property

end CountableColumns

namespace MeetSystem

open Chronological
universe u
variable {I : Type u} [LinearOrder I] [WellFoundedLT I] (p : MeetSystem I)

theorem rational_stages_all_filters_countable
    (heights : p.Heights (RationalHeights.lexOrder CountableColumns.order).toHeightOrder)
    (localMeet : p.LocalOldMeet) (own : p.OwnLayers) : ∀ i, AllFiltersCountable (p.order i) :=
  p.stages_all_filters_countable heights localMeet own CountableColumns.descending_property

theorem rational_union_all_filters_countable
    (heights : p.Heights (RationalHeights.lexOrder CountableColumns.order).toHeightOrder)
    (localMeet : p.LocalOldMeet) (own : p.OwnLayers) : AllFiltersCountable p.unionOrder :=
  p.union_all_filters_countable heights localMeet own CountableColumns.descending_property

theorem rational_bounded_all_filters_countable
    (heights : p.Heights (RationalHeights.lexOrder CountableColumns.order).toHeightOrder)
    (localMeet : p.LocalOldMeet) (own : p.OwnLayers) : AllFiltersCountable p.boundedOrder :=
  FixedTop.all_filters_countable p.unionOrder
    (p.rational_union_all_filters_countable heights localMeet own)

end MeetSystem





open RationalHeights CountableColumns Chronological

namespace MeetSystem
variable {α : Column} (p : MeetSystem (Set.Iio α.val))

noncomputable def ordinalBirth (x : p.system.Union) : Ordinal.{0} :=
  (p.system.birth x).val

noncomputable def boundedBirth : Option p.system.Union → Ordinal.{0} :=
  FixedTop.birth p.ordinalBirth α.val

theorem ordinalBirth_lt (x : p.system.Union) : p.ordinalBirth x < α.val :=
  (p.system.birth x).property

theorem boundedBirth_le (x : Option p.system.Union) : p.boundedBirth x ≤ α.val :=
  FixedTop.birth_le p.ordinalBirth α.val p.ordinalBirth_lt x

theorem boundedBirth_stage (i : Set.Iio α.val) (x : p.system.Point i) :
    p.boundedBirth ((p.boundedInclusion i).toFun x) = (p.system.stageBirth i x).val := rfl

theorem boundedBirth_stage_le (i : Set.Iio α.val) (x : p.system.Point i) :
    p.boundedBirth ((p.boundedInclusion i).toFun x) ≤ i.val :=
  p.system.stageBirth_le i x

theorem boundedBirth_at_limit_iff (x : Option p.system.Union) :
    p.boundedBirth x = α.val ↔ x = none :=
  FixedTop.birth_at_top_iff p.ordinalBirth α.val p.ordinalBirth_lt x

theorem ordinalBirth_old_meet (localMeet : p.LocalOldMeet) :
    OldMeet (P := p.unionOrder) p.ordinalBirth :=
  p.union_old_meet localMeet

theorem boundedBirth_old_meet (localMeet : p.LocalOldMeet) :
    OldMeet (P := p.boundedOrder) p.boundedBirth :=
  FixedTop.old_meet_preserved p.unionOrder p.ordinalBirth α.val p.ordinalBirth_lt
    (p.ordinalBirth_old_meet localMeet)

noncomputable def boundedBirth_incoming_layer
    (Space : Ordinal.{0} → Type 1) (orders : ∀ i, MeetOrder (Space i)) :
    GrowthLayer Space orders p.boundedOrder p.boundedBirth α.val :=
  FixedTop.incoming_layer p.unionOrder Space orders p.ordinalBirth α.val p.ordinalBirth_lt

theorem countable_ordinal_chronological_limit
    (h : p.Heights (lexOrder CountableColumns.order).toHeightOrder)
    (top : ∀ i, p.system.Point i)
    (greatest : ∀ i x, (p.order i).le x (top i))
    (countable : ∀ i, CountableRange (h.height i).value)
    (localMeet : p.LocalOldMeet) (own : p.OwnLayers) :
    ∃ height : StrictHeight p.boundedOrder (lexOrder CountableColumns.order).toHeightOrder,
      (∀ i x, height.value ((p.boundedInclusion i).toFun x) = (h.height i).value x) ∧
      CountableRange height.value ∧
      AllFiltersCountable p.boundedOrder ∧
      OldMeet (P := p.boundedOrder) p.boundedBirth ∧
      (∀ i x, p.boundedBirth ((p.boundedInclusion i).toFun x) =
        (p.system.stageBirth i x).val) ∧
      (∀ x, p.boundedBirth x = α.val ↔ x = none) := by
  let : Countable (Set.Iio α.val) := (initialSegment_countable α).to_subtype
  rcases h.bounded_countable_limit top greatest countable with ⟨height, fixed, small⟩
  exact ⟨height, fixed, small, p.rational_bounded_all_filters_countable h localMeet own,
    p.boundedBirth_old_meet localMeet, p.boundedBirth_stage, p.boundedBirth_at_limit_iff⟩

end MeetSystem
end PartitionPilot.Compression.RecursiveMaps



namespace PartitionPilot.Compression.RecursiveMaps.Chronological

universe u
variable {A B Stage : Type u} [LinearOrder Stage]
    {P : MeetOrder A} {Q : MeetOrder B}

def NewOldMeet (birth : A → Stage) (s : Stage) : Prop :=
  ∀ x y, birth x = s → birth y < s → ¬ P.le x y → birth (P.meet x y) < s

theorem NewOldMeet.transport {birthA : A → Stage} {birthB : B → Stage} {s : Stage}
    (localMeet : NewOldMeet (P := P) birthA s) (e : MeetEmbedding P Q)
    (preserves : ∀ x, birthB (e.toFun x) = birthA x)
    (cover : ∀ y, ∃ x, e.toFun x = y) : NewOldMeet (P := Q) birthB s := by
  intro x y born earlier notLower
  rcases cover x with ⟨a, rfl⟩
  rcases cover y with ⟨b, rfl⟩
  rw [preserves] at born earlier
  have old := localMeet a b born earlier (fun lower => notLower ((e.le_iff a b).mpr lower))
  rw [← e.map_meet, preserves]
  exact old

theorem OldMeet.transport {birthA : A → Stage} {birthB : B → Stage}
    (previous : OldMeet (P := P) birthA) (e : MeetEmbedding P Q)
    (preserves : ∀ x, birthB (e.toFun x) = birthA x)
    (cover : ∀ y, ∃ x, e.toFun x = y) : OldMeet (P := Q) birthB := by
  intro x y earlier notLower
  rcases cover x with ⟨a, rfl⟩
  rcases cover y with ⟨b, rfl⟩
  rw [preserves, preserves] at earlier
  have old := previous a b earlier (fun lower => notLower ((e.le_iff a b).mpr lower))
  rw [← e.map_meet, preserves, preserves]
  exact old

end PartitionPilot.Compression.RecursiveMaps.Chronological

namespace PartitionPilot.Attachment.Templates

open Compression Compression.RecursiveMaps Compression.RecursiveMaps.Chronological
universe u
variable {A I Stage : Type u} [LinearOrder Stage] {P : MeetOrder A}
    (b : Templates.{u,u,u} P I)

def birth (oldBirth : A → Stage) (s : Stage) : A ⊕ b.Fresh → Stage
  | .inl a => oldBirth a
  | .inr _ => s

theorem birth_le (oldBirth : A → Stage) (s : Stage) (old : ∀ x, oldBirth x < s)
    (x : A ⊕ b.Fresh) : b.birth oldBirth s x ≤ s := by
  cases x with
  | inl a => exact (old a).le
  | inr _ => exact le_rfl

theorem birth_at_step_iff (oldBirth : A → Stage) (s : Stage) (old : ∀ x, oldBirth x < s)
    (x : A ⊕ b.Fresh) : b.birth oldBirth s x = s ↔ ∃ y, x = .inr y := by
  cases x with
  | inl a =>
    constructor
    · intro eq
      exact False.elim ((ne_of_lt (old a)) eq)
    · rintro ⟨y, eq⟩
      cases eq
  | inr y => exact ⟨fun _ => ⟨y, rfl⟩, fun _ => rfl⟩

theorem old_meet_preserved (oldBirth : A → Stage) (s : Stage) (old : ∀ x, oldBirth x < s)
    (previous : OldMeet (P := P) oldBirth) : OldMeet (P := b.extension) (b.birth oldBirth s) :=
  attachment_old_meet b (b.birth oldBirth s) s old (fun _ => rfl) previous

theorem new_old_meet (oldBirth : A → Stage) (s : Stage) (old : ∀ x, oldBirth x < s) :
    NewOldMeet (P := b.extension) (b.birth oldBirth s) s := by
  intro x y born earlier notLower
  rcases (b.birth_at_step_iff oldBirth s old x).mp born with ⟨x, rfl⟩
  cases y with
  | inl a =>
    rw [b.shadow_meet_eq x a notLower]
    exact old _
  | inr y => exact False.elim (lt_irrefl s earlier)

noncomputable def earlier_layer {Space : Stage → Type u} {orders : ∀ t, MeetOrder (Space t)}
    (oldBirth : A → Stage) (s t : Stage) (earlier : t < s)
    (layer : GrowthLayer Space orders P oldBirth t) :
    GrowthLayer Space orders b.extension (b.birth oldBirth s) t := by
  apply layer.transport b.oldEmbedding (fun _ => rfl)
  intro x hx
  cases x with
  | inl a => exact ⟨a, rfl⟩
  | inr y =>
    change s = t at hx
    exact False.elim ((ne_of_lt earlier) hx.symm)

noncomputable def incoming_layer (Space : Stage → Type u) (orders : ∀ t, MeetOrder (Space t))
    (oldBirth : A → Stage) (s : Stage) (old : ∀ x, oldBirth x < s)
    (index : I → Stage) (earlier : ∀ i, index i < s)
    (template : ∀ i, MeetIso (orders (index i)) (b.order i)) :
    GrowthLayer Space orders b.extension (b.birth oldBirth s) s :=
  attachmentLayer b Space orders (b.birth oldBirth s) s old index earlier template

end PartitionPilot.Attachment.Templates

namespace PartitionPilot.Compression.RecursiveMaps.PrincipalAmalgamation.Input

open Chronological
universe u
variable {A B Stage : Type u} [LinearOrder Stage]
    {P : MeetOrder A} {Q : MeetOrder B} (g : Input P Q)

theorem new_old_meet (oldBirth : A → Stage) (s : Stage) (old : ∀ x, oldBirth x < s) :
    NewOldMeet (P := g.order) (g.birth oldBirth s) s := by
  intro x y born earlier _
  cases x with
  | inl a => exact False.elim ((ne_of_lt (old a)) born)
  | inr x =>
    cases y with
    | inl a =>
      rw [g.new_shadow_meet]
      exact old _
    | inr y => exact False.elim (lt_irrefl s earlier)

end PartitionPilot.Compression.RecursiveMaps.PrincipalAmalgamation.Input

end OAI
