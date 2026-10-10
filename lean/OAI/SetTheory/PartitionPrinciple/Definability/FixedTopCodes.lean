import OAI.SetTheory.PartitionPrinciple.Forcing.GroundFilterCopies
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundAttachmentEmbeddings

namespace OAI

namespace PartitionPilot.Forcing

universe u

def GreatestLowerBoundCode (L r x y z : ZFSet.{u}) : Prop :=
  ZFSet.pair z x ∈ r ∧ ZFSet.pair z y ∈ r ∧
    ∀ w ∈ L, ZFSet.pair w x ∈ r → ZFSet.pair w y ∈ r → ZFSet.pair w z ∈ r

noncomputable def canonicalMeetGraph (L r : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun v => ∃ x ∈ L, ∃ y ∈ L, ∃ z ∈ L,
    v = ZFSet.pair (ZFSet.pair x y) z ∧ GreatestLowerBoundCode L r x y z)
    (ZFSet.prod (ZFSet.prod L L) L)

theorem canonicalMeetGraph_subset (L r : ZFSet.{u}) :
    canonicalMeetGraph L r ⊆ ZFSet.prod (ZFSet.prod L L) L := by
  intro v hv
  exact (ZFSet.mem_sep.1 hv).1

theorem mem_canonicalMeetGraph (L r v : ZFSet.{u}) :
    v ∈ canonicalMeetGraph L r ↔ ∃ x ∈ L, ∃ y ∈ L, ∃ z ∈ L,
      v = ZFSet.pair (ZFSet.pair x y) z ∧ GreatestLowerBoundCode L r x y z := by
  constructor
  · intro hv
    exact (ZFSet.mem_sep.1 hv).2
  · intro h
    obtain ⟨x, hx, y, hy, z, hz, eq, glb⟩ := h
    subst v
    exact ZFSet.mem_sep.2
      ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, hz⟩,
        x, hx, y, hy, z, hz, rfl, glb⟩

theorem pair_mem_canonicalMeetGraph (L r x y z : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair x y) z ∈ canonicalMeetGraph L r ↔
      x ∈ L ∧ y ∈ L ∧ z ∈ L ∧ GreatestLowerBoundCode L r x y z := by
  rw [mem_canonicalMeetGraph]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, eq, h⟩
    have outer := ZFSet.pair_inj.1 eq
    have inner := ZFSet.pair_inj.1 outer.1
    rcases inner with ⟨rfl, rfl⟩
    rcases outer.2 with rfl
    exact ⟨ha, hb, hc, h⟩
  · rintro ⟨hx, hy, hz, h⟩
    exact ⟨x, hx, y, hy, z, hz, rfl, h⟩

theorem GreatestLowerBoundCode.unique {L r x y z w : ZFSet.{u}}
    (order : PartialOrderCode L r) (hz : z ∈ L) (hw : w ∈ L)
    (left : GreatestLowerBoundCode L r x y z)
    (right : GreatestLowerBoundCode L r x y w) : z = w := by
  exact order.antisymm z hz w hw (right.2.2 z hz left.1 left.2.1)
    (left.2.2 w hw right.1 right.2.1)

theorem canonicalMeetGraph_code {L r : ZFSet.{u}} (order : PartialOrderCode L r)
    (existsGLB : ∀ x ∈ L, ∀ y ∈ L, ∃ z ∈ L, GreatestLowerBoundCode L r x y z) :
    MeetOrderCode L r (canonicalMeetGraph L r) := by
  refine ⟨order, ⟨canonicalMeetGraph_subset L r, ?_⟩, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 ha
    obtain ⟨z, hz, h⟩ := existsGLB x hx y hy
    refine ⟨z, (pair_mem_canonicalMeetGraph L r x y z).2 ⟨hx, hy, hz, h⟩, ?_⟩
    intro w hw
    have other := (pair_mem_canonicalMeetGraph L r x y w).1 hw
    exact GreatestLowerBoundCode.unique order other.2.2.1 hz other.2.2.2 h
  · intro x y z h
    exact ((pair_mem_canonicalMeetGraph L r x y z).1 h).2.2.2.1
  · intro x y z h
    exact ((pair_mem_canonicalMeetGraph L r x y z).1 h).2.2.2.2.1
  · intro x y z w hw h hleft hright
    exact ((pair_mem_canonicalMeetGraph L r x y z).1 h).2.2.2.2.2 w hw hleft hright

namespace MeetOrderCode

theorem pair_iff {L r μ x y z : ZFSet.{u}} (code : MeetOrderCode L r μ) :
    ZFSet.pair (ZFSet.pair x y) z ∈ μ ↔
      x ∈ L ∧ y ∈ L ∧ z ∈ L ∧ GreatestLowerBoundCode L r x y z := by
  constructor
  · intro h
    have shape := ZFSet.pair_mem_prod.1 (code.operation.1 h)
    have domain := ZFSet.pair_mem_prod.1 shape.1
    exact ⟨domain.1, domain.2, shape.2, code.lower_left x y z h,
      code.lower_right x y z h, fun w hw => code.greatest x y z w hw h⟩
  · rintro ⟨hx, hy, hz, h⟩
    obtain ⟨w, hw, _⟩ := code.operation.2 (ZFSet.pair x y) (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
    have wL := (ZFSet.pair_mem_prod.1 (code.operation.1 hw)).2
    have glb : GreatestLowerBoundCode L r x y w :=
      ⟨code.lower_left x y w hw, code.lower_right x y w hw,
        fun a ha => code.greatest x y w a ha hw⟩
    have eq := GreatestLowerBoundCode.unique code.order hz wL h glb
    exact eq.symm ▸ hw

theorem eq_canonicalMeetGraph {L r μ : ZFSet.{u}} (code : MeetOrderCode L r μ) :
    μ = canonicalMeetGraph L r := by
  apply ZFSet.ext
  intro v
  constructor
  · intro hv
    obtain ⟨a, ha, z, _, rfl⟩ := ZFSet.mem_prod.1 (code.operation.1 hv)
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.1 ha
    exact (pair_mem_canonicalMeetGraph L r x y z).2 (code.pair_iff.1 hv)
  · intro hv
    obtain ⟨x, hx, y, hy, z, hz, rfl, h⟩ := (mem_canonicalMeetGraph L r v).1 hv
    exact code.pair_iff.2 ⟨hx, hy, hz, h⟩

theorem graph_unique {L r μ ν : ZFSet.{u}} (left : MeetOrderCode L r μ)
    (right : MeetOrderCode L r ν) : μ = ν :=
  left.eq_canonicalMeetGraph.trans right.eq_canonicalMeetGraph.symm

noncomputable def meetValue {L r μ : ZFSet.{u}} (code : MeetOrderCode L r μ)
    (x y : {a : ZFSet.{u} // a ∈ L}) : {a : ZFSet.{u} // a ∈ L} :=
  let witness := code.operation.2 (ZFSet.pair x.val y.val)
    (ZFSet.pair_mem_prod.2 ⟨x.property, y.property⟩)
  ⟨Classical.choose witness,
    (ZFSet.pair_mem_prod.1 (code.operation.1 (Classical.choose_spec witness).1)).2⟩

theorem meetValue_entry {L r μ : ZFSet.{u}} (code : MeetOrderCode L r μ)
    (x y : {a : ZFSet.{u} // a ∈ L}) :
    ZFSet.pair (ZFSet.pair x.val y.val) (code.meetValue x y).val ∈ μ :=
  (Classical.choose_spec (code.operation.2 (ZFSet.pair x.val y.val)
    (ZFSet.pair_mem_prod.2 ⟨x.property, y.property⟩))).1

noncomputable def toMeetOrder {L r μ : ZFSet.{u}} (code : MeetOrderCode L r μ) :
    PartitionPilot.MeetOrder {a : ZFSet.{u} // a ∈ L} where
  le x y := ZFSet.pair x.val y.val ∈ r
  meet := code.meetValue
  refl x := code.order.refl x.val x.property
  trans {x y z} := code.order.trans x.val x.property y.val y.property z.val z.property
  antisymm {x y} hxy hyx := Subtype.ext (code.order.antisymm x.val x.property y.val y.property hxy hyx)
  meet_le_left x y := code.lower_left x.val y.val _ (code.meetValue_entry x y)
  meet_le_right x y := code.lower_right x.val y.val _ (code.meetValue_entry x y)
  le_meet {x y z} := code.greatest y.val z.val _ x.val x.property (code.meetValue_entry y z)

theorem toMeetOrder_le_iff {L r μ : ZFSet.{u}} (code : MeetOrderCode L r μ)
    (x y : {a : ZFSet.{u} // a ∈ L}) :
    code.toMeetOrder.le x y ↔ ZFSet.pair x.val y.val ∈ r := Iff.rfl

theorem toMeetOrder_meet_entry {L r μ : ZFSet.{u}} (code : MeetOrderCode L r μ)
    (x y : {a : ZFSet.{u} // a ∈ L}) :
    ZFSet.pair (ZFSet.pair x.val y.val) (code.toMeetOrder.meet x y).val ∈ μ :=
  code.meetValue_entry x y

end MeetOrderCode

noncomputable def fixedTopCarrier (P : ZFSet.{u}) : ZFSet.{u} := insert P P

noncomputable def fixedTopOrder (P r : ZFSet.{u}) : ZFSet.{u} :=
  r ∪ ZFSet.prod (fixedTopCarrier P) {P}

noncomputable def fixedTopMeet (P r : ZFSet.{u}) : ZFSet.{u} :=
  canonicalMeetGraph (fixedTopCarrier P) (fixedTopOrder P r)

theorem mem_fixedTopCarrier (P x : ZFSet.{u}) : x ∈ fixedTopCarrier P ↔ x = P ∨ x ∈ P :=
  ZFSet.mem_insert_iff

theorem fixedTopCarrier_top (P : ZFSet.{u}) : P ∈ fixedTopCarrier P :=
  (mem_fixedTopCarrier P P).2 (Or.inl rfl)

theorem fixedTopCarrier_old {P x : ZFSet.{u}} (hx : x ∈ P) : x ∈ fixedTopCarrier P :=
  (mem_fixedTopCarrier P x).2 (Or.inr hx)

theorem fixedTopCarrier_subset (P : ZFSet.{u}) : P ⊆ fixedTopCarrier P :=
  fun _ hx => fixedTopCarrier_old hx

theorem fixedTopOrder_subset (P r : ZFSet.{u}) : r ⊆ fixedTopOrder P r :=
  fun _ hx => ZFSet.mem_union.2 (Or.inl hx)

theorem pair_mem_fixedTopOrder (P r x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ fixedTopOrder P r ↔
      ZFSet.pair x y ∈ r ∨ (x ∈ fixedTopCarrier P ∧ y = P) := by
  rw [fixedTopOrder, ZFSet.mem_union, ZFSet.pair_mem_prod, ZFSet.mem_singleton]

theorem fixedTopOrder_old_iff {P r x y : ZFSet.{u}} (hy : y ∈ P) :
    ZFSet.pair x y ∈ fixedTopOrder P r ↔ ZFSet.pair x y ∈ r := by
  rw [pair_mem_fixedTopOrder]
  constructor
  · rintro (old | ⟨_, equal⟩)
    · exact old
    · exact False.elim (ZFSet.mem_irrefl P (equal ▸ hy))
  · exact Or.inl

theorem fixedTopOrder_greatest {P r x : ZFSet.{u}} (hx : x ∈ fixedTopCarrier P) :
    ZFSet.pair x P ∈ fixedTopOrder P r :=
  (pair_mem_fixedTopOrder P r x P).2 (Or.inr ⟨hx, rfl⟩)

theorem fixedTopOrder_no_new_below {P r x y : ZFSet.{u}}
    (old : PartialOrderCode P r) (hy : y ∈ P) (entry : ZFSet.pair x y ∈ fixedTopOrder P r) :
    x ∈ P :=
  (ZFSet.pair_mem_prod.1 (old.relation ((fixedTopOrder_old_iff hy).1 entry))).1

theorem fixedTopOrder_strict_top {P r x : ZFSet.{u}}
    (old : PartialOrderCode P r) (hx : x ∈ P) :
    ZFSet.pair x P ∈ fixedTopOrder P r ∧ ZFSet.pair P x ∉ fixedTopOrder P r := by
  refine ⟨fixedTopOrder_greatest (fixedTopCarrier_old hx), ?_⟩
  intro entry
  exact ZFSet.mem_irrefl P (fixedTopOrder_no_new_below old hx entry)

theorem fixedTopOrder_top_iff {P r x : ZFSet.{u}} (old : PartialOrderCode P r) :
    ZFSet.pair P x ∈ fixedTopOrder P r ↔ x = P := by
  rw [pair_mem_fixedTopOrder]
  constructor
  · rintro (entry | ⟨_, equal⟩)
    · exact False.elim (ZFSet.mem_irrefl P (ZFSet.pair_mem_prod.1 (old.relation entry)).1)
    · exact equal
  · intro equal
    exact Or.inr ⟨fixedTopCarrier_top P, equal⟩

theorem fixedTopOrder_code {P r : ZFSet.{u}} (old : PartialOrderCode P r) :
    PartialOrderCode (fixedTopCarrier P) (fixedTopOrder P r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases ZFSet.mem_union.1 hz with entry | entry
    · obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (old.relation entry)
      exact ZFSet.pair_mem_prod.2 ⟨fixedTopCarrier_old hx, fixedTopCarrier_old hy⟩
    · obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 entry
      have equal := ZFSet.mem_singleton.1 hy
      exact ZFSet.pair_mem_prod.2 ⟨hx, equal.symm ▸ fixedTopCarrier_top P⟩
  · intro x hx
    rcases (mem_fixedTopCarrier P x).1 hx with rfl | oldx
    · exact fixedTopOrder_greatest hx
    · exact (pair_mem_fixedTopOrder P r x x).2 (Or.inl (old.refl x oldx))
  · intro x hx y hy xy yx
    rcases (mem_fixedTopCarrier P x).1 hx with rfl | oldx
    · exact ((fixedTopOrder_top_iff old).1 xy).symm
    · have oldy := fixedTopOrder_no_new_below old oldx yx
      exact old.antisymm x oldx y oldy ((fixedTopOrder_old_iff oldy).1 xy)
        ((fixedTopOrder_old_iff oldx).1 yx)
  · intro x hx y _ z hz xy yz
    rcases (mem_fixedTopCarrier P z).1 hz with rfl | oldz
    · exact fixedTopOrder_greatest hx
    · have oldy := fixedTopOrder_no_new_below old oldz yz
      have oldx := fixedTopOrder_no_new_below old oldy xy
      exact (fixedTopOrder_old_iff oldz).2 (old.trans x oldx y oldy z oldz
        ((fixedTopOrder_old_iff oldy).1 xy) ((fixedTopOrder_old_iff oldz).1 yz))

theorem fixedTop_old_glb {P r μ x y z : ZFSet.{u}} (old : MeetOrderCode P r μ)
    (entry : ZFSet.pair (ZFSet.pair x y) z ∈ μ) :
    GreatestLowerBoundCode (fixedTopCarrier P) (fixedTopOrder P r) x y z := by
  obtain ⟨hx, hy, hz, glb⟩ := old.pair_iff.1 entry
  refine ⟨(fixedTopOrder_old_iff hx).2 glb.1, (fixedTopOrder_old_iff hy).2 glb.2.1, ?_⟩
  intro w _ wx wy
  have hw := fixedTopOrder_no_new_below old.order hx wx
  exact (fixedTopOrder_old_iff hz).2 (glb.2.2 w hw
    ((fixedTopOrder_old_iff hx).1 wx) ((fixedTopOrder_old_iff hy).1 wy))

theorem fixedTopMeet_code {P r μ : ZFSet.{u}} (old : MeetOrderCode P r μ) :
    MeetOrderCode (fixedTopCarrier P) (fixedTopOrder P r) (fixedTopMeet P r) := by
  apply canonicalMeetGraph_code (fixedTopOrder_code old.order)
  intro x hx y hy
  rcases (mem_fixedTopCarrier P x).1 hx with rfl | oldx
  · exact ⟨y, hy, fixedTopOrder_greatest hy, (fixedTopOrder_code old.order).refl y hy,
      fun _ _ _ wy => wy⟩
  · rcases (mem_fixedTopCarrier P y).1 hy with rfl | oldy
    · exact ⟨x, hx, (fixedTopOrder_code old.order).refl x hx, fixedTopOrder_greatest hx,
        fun _ _ wx _ => wx⟩
    · obtain ⟨z, entry, _⟩ := old.operation.2 (ZFSet.pair x y) (ZFSet.pair_mem_prod.2 ⟨oldx, oldy⟩)
      exact ⟨z, fixedTopCarrier_old (ZFSet.pair_mem_prod.1 (old.operation.1 entry)).2,
        fixedTop_old_glb old entry⟩

theorem fixedTopMeet_old_iff {P r μ x y z : ZFSet.{u}}
    (old : MeetOrderCode P r μ) (hx : x ∈ P) (hy : y ∈ P) :
    ZFSet.pair (ZFSet.pair x y) z ∈ fixedTopMeet P r ↔ ZFSet.pair (ZFSet.pair x y) z ∈ μ := by
  constructor
  · intro entry
    obtain ⟨_, _, _, glb⟩ := (fixedTopMeet_code old).pair_iff.1 entry
    have hz := fixedTopOrder_no_new_below old.order hx glb.1
    refine old.pair_iff.2 ⟨hx, hy, hz, (fixedTopOrder_old_iff hx).1 glb.1,
      (fixedTopOrder_old_iff hy).1 glb.2.1, ?_⟩
    intro w hw wx wy
    exact (fixedTopOrder_old_iff hz).1 (glb.2.2 w (fixedTopCarrier_old hw)
      ((fixedTopOrder_old_iff hx).2 wx) ((fixedTopOrder_old_iff hy).2 wy))
  · intro entry
    have hz := (ZFSet.pair_mem_prod.1 (old.operation.1 entry)).2
    exact (fixedTopMeet_code old).pair_iff.2
      ⟨fixedTopCarrier_old hx, fixedTopCarrier_old hy, fixedTopCarrier_old hz, fixedTop_old_glb old entry⟩

theorem fixedTopMeet_top_left {P r μ x z : ZFSet.{u}}
    (old : MeetOrderCode P r μ) (hx : x ∈ fixedTopCarrier P) :
    ZFSet.pair (ZFSet.pair P x) z ∈ fixedTopMeet P r ↔ z = x := by
  have code := fixedTopMeet_code old
  have entry : ZFSet.pair (ZFSet.pair P x) x ∈ fixedTopMeet P r :=
    code.pair_iff.2 ⟨fixedTopCarrier_top P, hx, hx, fixedTopOrder_greatest hx,
      code.order.refl x hx, fun _ _ _ wx => wx⟩
  constructor
  · intro other
    obtain ⟨v, _, unique⟩ := code.operation.2 (ZFSet.pair P x)
      (ZFSet.pair_mem_prod.2 ⟨fixedTopCarrier_top P, hx⟩)
    exact (unique z other).trans (unique x entry).symm
  · intro equal
    exact equal.symm ▸ entry

theorem fixedTopMeet_subset {P r μ : ZFSet.{u}} (old : MeetOrderCode P r μ) :
    μ ⊆ fixedTopMeet P r := by
  intro z hz
  obtain ⟨xy, hxy, v, _, rfl⟩ := ZFSet.mem_prod.1 (old.operation.1 hz)
  obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
  exact (fixedTopMeet_old_iff old hx hy).2 hz

theorem fixedTopOrder_bottom {P r b : ZFSet.{u}} (hb : b ∈ P)
    (least : ∀ x ∈ P, ZFSet.pair b x ∈ r) :
    ∀ x ∈ fixedTopCarrier P, ZFSet.pair b x ∈ fixedTopOrder P r := by
  intro x hx
  rcases (mem_fixedTopCarrier P x).1 hx with rfl | oldx
  · exact fixedTopOrder_greatest (fixedTopCarrier_old hb)
  · exact fixedTopOrder_subset P r (least x oldx)

theorem fixedTopMeet_top_right {P r μ x z : ZFSet.{u}}
    (old : MeetOrderCode P r μ) (hx : x ∈ fixedTopCarrier P) :
    ZFSet.pair (ZFSet.pair x P) z ∈ fixedTopMeet P r ↔ z = x := by
  have code := fixedTopMeet_code old
  have entry : ZFSet.pair (ZFSet.pair x P) x ∈ fixedTopMeet P r :=
    code.pair_iff.2 ⟨hx, fixedTopCarrier_top P, hx, code.order.refl x hx,
      fixedTopOrder_greatest hx, fun _ _ wx _ => wx⟩
  constructor
  · intro other
    obtain ⟨v, _, unique⟩ := code.operation.2 (ZFSet.pair x P)
      (ZFSet.pair_mem_prod.2 ⟨hx, fixedTopCarrier_top P⟩)
    exact (unique z other).trans (unique x entry).symm
  · intro equal
    exact equal.symm ▸ entry

theorem fixedTopOldEmbedding_injection (P : ZFSet.{u}) :
    InjectionCode P (fixedTopCarrier P) (attachmentOldEmbeddingGraph P) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := (mem_attachmentOldEmbeddingGraph P z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hx, fixedTopCarrier_old hx⟩
  · intro x hx
    exact ⟨x, (pair_mem_attachmentOldEmbeddingGraph P x x).2 ⟨hx, rfl⟩,
      fun y entry => ((pair_mem_attachmentOldEmbeddingGraph P x y).1 entry).2⟩
  · intro x y z first second
    exact ((pair_mem_attachmentOldEmbeddingGraph P x z).1 first).2.symm.trans
      ((pair_mem_attachmentOldEmbeddingGraph P y z).1 second).2

theorem fixedTopOldEmbedding_code {P r μ : ZFSet.{u}} (old : MeetOrderCode P r μ) :
    MeetEmbeddingCode P (fixedTopCarrier P) r (fixedTopOrder P r) μ (fixedTopMeet P r)
      (attachmentOldEmbeddingGraph P) := by
  refine ⟨fixedTopOldEmbedding_injection P, ?_, ?_⟩
  · intro x y x' y' below first second
    obtain ⟨_, rfl⟩ := (pair_mem_attachmentOldEmbeddingGraph P x x').1 first
    obtain ⟨hy, rfl⟩ := (pair_mem_attachmentOldEmbeddingGraph P y y').1 second
    exact (fixedTopOrder_old_iff hy).2 below
  · intro x y z x' y' z' meet first second third
    obtain ⟨hx, rfl⟩ := (pair_mem_attachmentOldEmbeddingGraph P x x').1 first
    obtain ⟨hy, rfl⟩ := (pair_mem_attachmentOldEmbeddingGraph P y y').1 second
    obtain ⟨_, rfl⟩ := (pair_mem_attachmentOldEmbeddingGraph P z z').1 third
    exact (fixedTopMeet_old_iff old hx hy).2 meet

noncomputable def fixedTopOldIdealEmbedding {P r μ : ZFSet.{u}} (old : MeetOrderCode P r μ) :
    PartitionPilot.Compression.RecursiveMaps.IdealEmbedding old.toMeetOrder (fixedTopMeet_code old).toMeetOrder where
  toFun x := ⟨x.val, fixedTopCarrier_old x.property⟩
  le_iff x y := fixedTopOrder_old_iff y.property
  map_meet x y := by
    apply Subtype.ext
    have oldEntry := old.toMeetOrder_meet_entry x y
    have newEntry := (fixedTopMeet_code old).toMeetOrder_meet_entry
      ⟨x.val, fixedTopCarrier_old x.property⟩ ⟨y.val, fixedTopCarrier_old y.property⟩
    obtain ⟨v, _, unique⟩ := old.operation.2 (ZFSet.pair x.val y.val)
      (ZFSet.pair_mem_prod.2 ⟨x.property, y.property⟩)
    exact (unique _ oldEntry).trans (unique _ ((fixedTopMeet_old_iff old x.property y.property).1 newEntry)).symm
  ideal x z below := ⟨⟨z.val, fixedTopOrder_no_new_below old.order x.property below⟩, rfl⟩

end PartitionPilot.Forcing

end OAI
