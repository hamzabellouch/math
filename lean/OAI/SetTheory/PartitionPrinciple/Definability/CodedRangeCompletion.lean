import OAI.SetTheory.PartitionPrinciple.Geometry.DecodedMeetMaps

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

structure CompressionRangeAccounting (P0 I U R MU Maps Bases Caps : ZFSet.{u}) : Prop where
  original_subset : P0 ⊆ U
  base_filled : ∀ i ∈ I, ∀ f b,
    ZFSet.pair i f ∈ Maps → ZFSet.pair i b ∈ Bases →
    ∀ x ∈ U, ZFSet.pair x b ∈ R → ∃ y ∈ U, ZFSet.pair y x ∈ f
  old_shadow : ∀ i ∈ I, ∀ b k,
    ZFSet.pair i b ∈ Bases → ZFSet.pair i k ∈ Caps →
    ∀ x ∈ P0, ZFSet.pair x k ∈ R → ZFSet.pair x b ∈ R
  cap_separation : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ b c k l,
    ZFSet.pair i b ∈ Bases → ZFSet.pair j c ∈ Bases →
    ZFSet.pair i k ∈ Caps → ZFSet.pair j l ∈ Caps →
    ZFSet.pair k c ∈ R ∨ ZFSet.pair l b ∈ R ∨
      ∃ z, ZFSet.pair (ZFSet.pair k l) z ∈ MU ∧ ZFSet.pair (ZFSet.pair b c) z ∈ MU
  fresh_accounting : ∀ x ∈ U, x ∈ P0 ∨
    ∃ i ∈ I, ∃ f k b, ∃ y ∈ U,
      ZFSet.pair i f ∈ Maps ∧ ZFSet.pair i k ∈ Caps ∧ ZFSet.pair i b ∈ Bases ∧
      ZFSet.pair y x ∈ f ∧ ZFSet.pair x k ∈ R ∧ ZFSet.pair x b ∉ R

namespace CompressionRangeAccounting
variable {P0 I U R MU Maps Bases Caps : ZFSet.{u}}
variable (accounting : CompressionRangeAccounting P0 I U R MU Maps Bases Caps)
include accounting

theorem range_completion (meet : MeetOrderCode U R MU) (maps : FunctionGraphOn I Maps)
    (embeddings : ∀ i f, ZFSet.pair i f ∈ Maps → MeetEmbeddingCode U U R R MU MU f)
    (bases : ZFSet.IsFunc I U Bases) (caps : ZFSet.IsFunc I U Caps) :
    ∀ i ∈ I, ∀ f k, ZFSet.pair i f ∈ Maps → ZFSet.pair i k ∈ Caps →
      ∀ x ∈ U, ZFSet.pair x k ∈ R → ∃ y ∈ U, ZFSet.pair y x ∈ f := by
  let baseGraph : FunctionGraphOn I Bases := ⟨U, bases⟩
  let capGraph : FunctionGraphOn I Caps := ⟨U, caps⟩
  let base (i : {i : ZFSet.{u} // i ∈ I}) : {x : ZFSet.{u} // x ∈ U} :=
    ⟨baseGraph.value i, (ZFSet.pair_mem_prod.1 (bases.1 (baseGraph.value_entry i))).2⟩
  let cap (i : {i : ZFSet.{u} // i ∈ I}) : {x : ZFSet.{u} // x ∈ U} :=
    ⟨capGraph.value i, (ZFSet.pair_mem_prod.1 (caps.1 (capGraph.value_entry i))).2⟩
  let embedding (i : {i : ZFSet.{u} // i ∈ I}) :=
    embeddings i.val (maps.value i) (maps.value_entry i)
  let s (i : {i : ZFSet.{u} // i ∈ I}) := (embedding i).toMeetEmbedding meet meet
  have baseFilled : ∀ i x, meet.toMeetOrder.le x (base i) → ∃ y, (s i).toFun y = x := by
    intro i x below
    obtain ⟨y, hy, entry⟩ := accounting.base_filled i.val i.property
      (maps.value i) (base i).val (maps.value_entry i) (baseGraph.value_entry i) x.val x.property below
    exact ⟨⟨y, hy⟩, ((embedding i).toMeetEmbedding_eq_iff meet meet ⟨y, hy⟩ x).2 entry⟩
  have shadow : ∀ i x, x.val ∈ P0 → meet.toMeetOrder.le x (cap i) →
      meet.toMeetOrder.le x (base i) := by
    intro i x original below
    exact accounting.old_shadow i.val i.property (base i).val (cap i).val
      (baseGraph.value_entry i) (capGraph.value_entry i) x.val original below
  have separation : ∀ i j, i ≠ j →
      meet.toMeetOrder.le (cap i) (base j) ∨ meet.toMeetOrder.le (cap j) (base i) ∨
      meet.toMeetOrder.meet (cap i) (cap j) = meet.toMeetOrder.meet (base i) (base j) := by
    intro i j different
    have rawDifferent : i.val ≠ j.val := fun equal => different (Subtype.ext equal)
    rcases accounting.cap_separation i.val i.property j.val j.property rawDifferent
      (base i).val (base j).val (cap i).val (cap j).val
      (baseGraph.value_entry i) (baseGraph.value_entry j)
      (capGraph.value_entry i) (capGraph.value_entry j) with first | second | common
    · exact Or.inl first
    · exact Or.inr (Or.inl second)
    · obtain ⟨z, capsMeet, basesMeet⟩ := common
      apply Or.inr ∘ Or.inr
      apply Subtype.ext
      let operation : FunctionGraphOn (ZFSet.prod U U) MU := ⟨U, meet.operation⟩
      exact (operation.unique (meet.toMeetOrder_meet_entry (cap i) (cap j)) capsMeet).trans
        (operation.unique (meet.toMeetOrder_meet_entry (base i) (base j)) basesMeet).symm
  have accounted : ∀ x : {x : ZFSet.{u} // x ∈ U}, x.val ∈ P0 ∨
      ∃ j y, (s j).toFun y = x ∧ meet.toMeetOrder.le x (cap j) ∧ ¬ meet.toMeetOrder.le x (base j) := by
    intro x
    rcases accounting.fresh_accounting x.val x.property with original | fresh
    · exact Or.inl original
    · obtain ⟨j, hj, f, k, b, y, hy, indexed, capped, based, entry, below, outside⟩ := fresh
      let i : {i : ZFSet.{u} // i ∈ I} := ⟨j, hj⟩
      have fEq := maps.value_eq_of_entry i indexed
      have kEq := capGraph.value_eq_of_entry i capped
      have bEq := baseGraph.value_eq_of_entry i based
      refine Or.inr ⟨i, ⟨y, hy⟩, ?_, ?_, ?_⟩
      · apply ((embedding i).toMeetEmbedding_eq_iff meet meet ⟨y, hy⟩ x).2
        exact fEq.symm ▸ entry
      · change ZFSet.pair x.val (capGraph.value i) ∈ R
        exact kEq.symm ▸ below
      · change ZFSet.pair x.val (baseGraph.value i) ∉ R
        exact bEq.symm ▸ outside
  have complete := Compression.range_completion_from_accounting meet.toMeetOrder
    (fun x => x.val ∈ P0) base cap (fun i => (s i).toFun) baseFilled shadow separation accounted
  intro i hi f k indexed capped x hx below
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have fEq := maps.value_eq_of_entry j indexed
  have kEq := capGraph.value_eq_of_entry j capped
  obtain ⟨y, equal⟩ := complete j ⟨x, hx⟩ (show ZFSet.pair x (capGraph.value j) ∈ R from kEq.symm ▸ below)
  refine ⟨y.val, y.property, ?_⟩
  have entry := ((embedding j).toMeetEmbedding_eq_iff meet meet y ⟨x, hx⟩).1 equal
  exact fEq ▸ entry

theorem range_iff (meet : MeetOrderCode U R MU) (maps : FunctionGraphOn I Maps)
    (embeddings : ∀ i f, ZFSet.pair i f ∈ Maps → MeetEmbeddingCode U U R R MU MU f)
    (bases : ZFSet.IsFunc I U Bases) (caps : ZFSet.IsFunc I U Caps)
    (bounded : ∀ i ∈ I, ∀ f k, ZFSet.pair i f ∈ Maps → ZFSet.pair i k ∈ Caps →
      ∀ x y, ZFSet.pair x y ∈ f → ZFSet.pair y k ∈ R)
    {i f k x : ZFSet.{u}} (hi : i ∈ I) (indexed : ZFSet.pair i f ∈ Maps)
    (capped : ZFSet.pair i k ∈ Caps) :
    (∃ y ∈ U, ZFSet.pair y x ∈ f) ↔ x ∈ U ∧ ZFSet.pair x k ∈ R := by
  constructor
  · rintro ⟨y, _, entry⟩
    exact ⟨(ZFSet.pair_mem_prod.1 ((embeddings i f indexed).injection.function.1 entry)).2,
      bounded i hi f k indexed capped y x entry⟩
  · rintro ⟨hx, below⟩
    exact accounting.range_completion meet maps embeddings bases caps i hi f k indexed capped x hx below

end CompressionRangeAccounting

end PartitionPilot.Forcing

end

end OAI
