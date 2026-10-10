import OAI.SetTheory.PartitionPrinciple.Definability.GroundBoundedExternalBirths

namespace OAI

namespace PartitionPilot.Forcing

namespace MeetEmbeddingCode
universe u
variable {P U Q rP rU rQ μP μU μQ e : ZFSet.{u}}
variable (code : MeetEmbeddingCode U Q rU rQ μU μQ e)
include code

theorem restrictSource (subset : P ⊆ U)
    (order : ∀ x ∈ P, ∀ y ∈ P, ZFSet.pair x y ∈ rP → ZFSet.pair x y ∈ rU)
    (meet : ∀ x ∈ P, ∀ y ∈ P, ∀ z, ZFSet.pair (ZFSet.pair x y) z ∈ μP →
      ZFSet.pair (ZFSet.pair x y) z ∈ μU) :
    MeetEmbeddingCode P Q rP rQ μP μQ (graphRestriction P e) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [graphRestriction_eq_sep code.injection.function]
    exact code.injection.restrict subset
  · intro x y x' y' lower first second
    obtain ⟨first, hx⟩ := pair_mem_graphRestriction.1 first
    obtain ⟨second, hy⟩ := pair_mem_graphRestriction.1 second
    exact code.monotone x y x' y' (order x hx y hy lower) first second
  · intro x y z x' y' z' entry first second third
    obtain ⟨first, hx⟩ := pair_mem_graphRestriction.1 first
    obtain ⟨second, hy⟩ := pair_mem_graphRestriction.1 second
    have third := (pair_mem_graphRestriction.1 third).1
    exact code.map_meet x y z x' y' z' (meet x hx y hy z entry) first second third

end MeetEmbeddingCode

section
open SetFormula
universe u

namespace AttachmentBatchInputs
variable {P r μ J Qs rs μs As Es Fs Ss : ZFSet.{u}}

theorem batch_bottom (d : AttachmentBatchInputs P r μ J Qs rs μs As Es Fs Ss)
    {b : ZFSet.{u}} (hb : b ∈ P) (least : ∀ x ∈ P, ZFSet.pair b x ∈ r) :
    b ∈ d.batchCarrier ∧ ∀ x ∈ d.batchCarrier, ZFSet.pair b x ∈ d.batchOrder :=
  ⟨old_mem_taggedExtension hb, d.coding.least_preserved hb least⟩

end AttachmentBatchInputs

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem canonical_iterate_bottom {b : ZFSet.{u}} (hb : b ∈ state.data.D)
    (least : ∀ x ∈ state.data.D, ZFSet.pair b x ∈ state.data.rD) (n : Nat) :
    let current := state.data.iterate M I Sources Reps G T n
    b ∈ current.D ∧ ∀ x ∈ current.D, ZFSet.pair b x ∈ current.rD := by
  induction n with
  | zero => exact ⟨hb, least⟩
  | succ n ih =>
    change b ∈ (state.data.iterate M I Sources Reps G T n).currentCarrier ∧
      ∀ x ∈ (state.data.iterate M I Sources Reps G T n).currentCarrier,
        ZFSet.pair b x ∈ (state.data.iterate M I Sources Reps G T n).currentOrder
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid
      pairing unions powers separation hI hSources hReps hG hT n
    rw [← equal] at ih ⊢
    exact current.batch.batch_bottom ih.1 ih.2

theorem union_bottom
    (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
    {b : ZFSet.{u}} (hb : b ∈ state.data.D)
    (least : ∀ x ∈ state.data.D, ZFSet.pair b x ∈ state.data.rD) :
    b ∈ data.fields 0 ∧ ∀ x ∈ data.fields 0, ZFSet.pair b x ∈ data.fields 1 := by
  have carrier : NatUnionCode (fun n => (state.data.iterate M I Sources Reps G T n).D) (data.fields 0) :=
    data.fieldUnion 0
  have order : NatUnionCode (fun n => (state.data.iterate M I Sources Reps G T n).rD) (data.fields 1) :=
    data.fieldUnion 1
  refine ⟨carrier.subset 0 hb, ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := (carrier x).1 hx
  exact order.subset n ((state.canonical_iterate_bottom pairing unions powers separation
    hI hSources hReps hG hT hb least n).2 x hn)

end GroundCompressionState

namespace GroundCompressionOrigin
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable (origin : GroundCompressionOrigin M initial P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)

include origin in
theorem union_bottom
    (data : GroundCompressionUnionData M initial I Sources Reps G m one T)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (initialDomain : initial.D = P0) (initialOrder : initial.rD = r0)
    {b : ZFSet.{u}} (hb : b ∈ P0) (least : ∀ x ∈ P0, ZFSet.pair b x ∈ r0) :
    b ∈ data.fields 0 ∧ ∀ x ∈ data.fields 0, ZFSet.pair b x ∈ data.fields 1 := by
  obtain ⟨seed, state, equal⟩ := origin
  cases equal
  apply state.union_bottom pairing unions powers separation hI hSources hReps hG hT data
  · simpa only [initialDomain] using hb
  · simpa only [initialDomain, initialOrder] using least

theorem initial_union_bottom {Labels : ZFSet.{u}}
    (origin : GroundCompressionOrigin M (M.initialCompressionData P0 G r0 μ0 A0 Labels)
      P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)
    (data : GroundCompressionUnionData M (M.initialCompressionData P0 G r0 μ0 A0 Labels)
      I Sources Reps G m one T)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    {b : ZFSet.{u}} (hb : b ∈ P0) (least : ∀ x ∈ P0, ZFSet.pair b x ∈ r0) :
    b ∈ data.fields 0 ∧ ∀ x ∈ data.fields 0, ZFSet.pair b x ∈ data.fields 1 :=
  origin.union_bottom data pairing unions powers separation hI hSources hReps hG hT rfl rfl hb least

end GroundCompressionOrigin
end

section
universe u
namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def externalOriginalEmbedding (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  graphRestriction P (completion.externalCopyGraph P r μ A
    (M.externalGroupIdentity G (externalChildLetters I P (externalRectangles P G r μ A)) m one))

theorem externalOriginalEmbedding_entry_iff (P r μ A x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ completion.externalOriginalEmbedding P r μ A ↔
      ZFSet.pair x y ∈ completion.externalCopyGraph P r μ A
        (M.externalGroupIdentity G (externalChildLetters I P (externalRectangles P G r μ A)) m one) ∧ x ∈ P :=
  pair_mem_graphRestriction

end GroundCompressionCompletion

namespace GroundExternalGeometryInputs
open SetFormula
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP : P0 ∈ M.sets)
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "originalGraph" => completion.externalOriginalEmbedding P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG hP

theorem externalOriginalEmbedding_mem : originalGraph ∈ M.sets := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  exact M.graphRestriction_mem unions separation hP (geometry.copies_ground _ data.group.group_code.identity_mem)

theorem externalOriginalEmbedding_code :
    MeetEmbeddingCode P0 (completion.externalBoundedCarrier P0 r0 μ0 A0)
      r0 (completion.externalBoundedOrder P0 r0 μ0 A0) μ0 (completion.externalBoundedMeet P0 r0 μ0 A0)
      originalGraph := by
  have geometry := data.externalBoundedGeometryData group oldAction pairing unions powers separation infinite hG hP
  exact (geometry.copies _ data.group.group_code.identity_mem).toMeetEmbeddingCode.restrictSource
    data.original.subset (fun x hx y hy => (data.original.order x hx y hy).2)
    (fun x hx y hy z => (data.original.meet x hx y hy z).2)

theorem externalOriginalEmbedding_order_iff {x y x' y' : ZFSet.{u}}
    (first : ZFSet.pair x x' ∈ originalGraph) (second : ZFSet.pair y y' ∈ originalGraph) :
    ZFSet.pair x' y' ∈ completion.externalBoundedOrder P0 r0 μ0 A0 ↔ ZFSet.pair x y ∈ r0 := by
  obtain ⟨first, hx⟩ := (completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 x x').1 first
  obtain ⟨second, hy⟩ := (completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 y y').1 second
  have geometry := data.externalBoundedGeometryData group oldAction pairing unions powers separation infinite hG hP
  exact ((geometry.copies _ data.group.group_code.identity_mem).order_iff first second).trans
    (data.original.order x hx y hy)

theorem externalOriginalEmbedding_equivariant {g g' x y x' y' : ZFSet.{u}}
    (actor : ZFSet.pair g g' ∈ M.externalOldInclusion G letters m one)
    (first : ZFSet.pair x x' ∈ originalGraph) (second : ZFSet.pair y y' ∈ originalGraph)
    (acted : ZFSet.pair (ZFSet.pair g x) y ∈ A0) :
    ZFSet.pair (ZFSet.pair g' x') y' ∈ completion.externalBoundedAction P0 r0 μ0 A0 := by
  obtain ⟨first, hx⟩ := (completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 x x').1 first
  have second := ((completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 y y').1 second).1
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  have hx' := (ZFSet.pair_mem_prod.1
    ((geometry.copies _ data.group.group_code.identity_mem).injection.function.1 first)).2
  exact (fixedTopAction_old_iff hx').2 (data.externalIdentityCopy_equivariant group oldAction
    pairing unions powers separation infinite hG actor first second ((data.original.action g x hx y).2 acted))

theorem externalOriginalEmbedding_agreement {g h g' h' v v' : ZFSet.{u}}
    (firstActor : ZFSet.pair g g' ∈ M.externalOldInclusion G letters m one)
    (secondActor : ZFSet.pair h h' ∈ M.externalOldInclusion G letters m one)
    (image : ZFSet.pair v v' ∈ originalGraph) (agree : ActionAgreementBelow P0 r0 A0 g h v) :
    ActionAgreementBelow (completion.externalBoundedCarrier P0 r0 μ0 A0)
      (completion.externalBoundedOrder P0 r0 μ0 A0) (completion.externalBoundedAction P0 r0 μ0 A0) g' h' v' := by
  obtain ⟨image, hv⟩ := (completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 v v').1 image
  exact data.externalBoundedOriginal_agreement group oldAction pairing unions powers separation infinite hG hP
    firstActor secondActor hv image agree

end GroundExternalGeometryInputs
end

namespace GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 Filters : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (origin : GroundCompressionOrigin M initial P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (initialDomain : initial.D = P0) (initialOrder : initial.rD = r0)
local notation "B" => completion.externalBoundedCarrier P0 r0 μ0 A0
local notation "rB" => completion.externalBoundedOrder P0 r0 μ0 A0
local notation "embedding" => completion.externalOriginalEmbedding P0 r0 μ0 A0
include data origin group action pairing unions powers separation infinite hI hSources hReps hG hT hP0 initialDomain initialOrder

theorem externalOriginalEmbedding_bottom {b b' : ZFSet.{u}}
    (least : ∀ x ∈ P0, ZFSet.pair b x ∈ r0)
    (image : ZFSet.pair b b' ∈ embedding) :
    b' ∈ B ∧ ∀ y ∈ B, ZFSet.pair b' y ∈ rB := by
  obtain ⟨copied, hb⟩ := (completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 b b').1 image
  have bottom := origin.union_bottom completion.algebra.union pairing unions powers separation
    hI hSources hReps hG hT initialDomain initialOrder hb least
  have code := data.externalOriginalEmbedding_code group action pairing unions powers separation infinite hG hP0
  exact ⟨(ZFSet.pair_mem_prod.1 (code.injection.function.1 image)).2,
    data.externalBoundedCopy_bottom group action pairing unions powers separation infinite hG hP0
      data.group.group_code.identity_mem bottom.2 copied⟩

theorem exists_externalOriginal_bottom {b : ZFSet.{u}} (hb : b ∈ P0)
    (least : ∀ x ∈ P0, ZFSet.pair b x ∈ r0) :
    ∃ b' ∈ M.sets, ZFSet.pair b b' ∈ embedding ∧ b' ∈ B ∧
      ∀ y ∈ B, ZFSet.pair b' y ∈ rB := by
  have code := data.externalOriginalEmbedding_code group action pairing unions powers separation infinite hG hP0
  obtain ⟨b', image, _⟩ := code.injection.function.2 b hb
  have bottom := data.externalOriginalEmbedding_bottom origin group action pairing unions powers separation infinite
    hI hSources hReps hG hT hP0 initialDomain initialOrder least image
  have geometry := data.externalBoundedGeometryData group action pairing unions powers separation infinite hG hP0
  exact ⟨b', M.transitive geometry.carrier_ground bottom.1, image, bottom⟩

end GroundExternalGeometryInputs

namespace GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P r μ A : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P r μ A completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP : P ∈ M.sets)
include data group action pairing unions powers separation infinite hG hP

theorem externalOriginal_image_mem {x y : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ completion.externalOriginalEmbedding P r μ A) :
    y ∈ completion.externalPointCarrier P r μ A := by
  have copied := ((completion.externalOriginalEmbedding_entry_iff P r μ A x y).1 entry).1
  have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP
  exact (ZFSet.pair_mem_prod.1
    ((geometry.copies _ data.group.group_code.identity_mem).injection.function.1 copied)).2

theorem externalOriginal_top_strict {x y : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ completion.externalOriginalEmbedding P r μ A) :
    ZFSet.pair y (completion.externalPointCarrier P r μ A) ∈ completion.externalBoundedOrder P r μ A ∧
    ZFSet.pair (completion.externalPointCarrier P r μ A) y ∉ completion.externalBoundedOrder P r μ A := by
  have hy := data.externalOriginal_image_mem group action pairing unions powers separation infinite hG hP entry
  have geometry := data.externalBoundedGeometryData group action pairing unions powers separation infinite hG hP
  exact ⟨geometry.greatest y (ZFSet.mem_insert_of_mem _ hy), geometry.strict_top y hy⟩

theorem externalOriginal_top_not_image (x : ZFSet.{u}) :
    ZFSet.pair x (completion.externalPointCarrier P r μ A) ∉ completion.externalOriginalEmbedding P r μ A := by
  intro entry
  exact ZFSet.mem_irrefl _ (data.externalOriginal_image_mem group action pairing unions powers separation infinite hG hP entry)

end GroundExternalGeometryInputs

open SetFormula
universe u

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

theorem externalOriginal_filterImage_eq (P r μ A B : ZFSet.{u}) {F : ZFSet.{u}}
    (subset : F ⊆ P) :
    relationImage F B (completion.externalOriginalEmbedding P r μ A) =
      relationImage F B (completion.externalCopyGraph P r μ A
        (M.externalGroupIdentity G (externalChildLetters I P (externalRectangles P G r μ A)) m one)) := by
  apply ZFSet.ext
  intro y
  rw [mem_relationImage, mem_relationImage]
  constructor
  · rintro ⟨hy, x, hx, entry⟩
    exact ⟨hy, x, hx, ((completion.externalOriginalEmbedding_entry_iff P r μ A x y).1 entry).1⟩
  · rintro ⟨hy, x, hx, entry⟩
    exact ⟨hy, x, hx, (completion.externalOriginalEmbedding_entry_iff P r μ A x y).2 ⟨entry, subset hx⟩⟩

end GroundCompressionCompletion

namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP : P0 ∈ M.sets)
include data group oldAction pairing unions powers separation infinite hG hP
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalBoundedCarrier P0 r0 μ0 A0
local notation "originalGraph" => completion.externalOriginalEmbedding P0 r0 μ0 A0

theorem externalBounded_original_capProfile
    {c e K F c' e' K' : ZFSet.{u}}
    (profile : CodedCapProfile U (completion.algebra.union.fields 1)
      (completion.algebra.union.fields 2) c e K F)
    (subset : F ⊆ P0)
    (imageC : ZFSet.pair c c' ∈ originalGraph)
    (imageE : ZFSet.pair e e' ∈ originalGraph)
    (imageK : ZFSet.pair K K' ∈ originalGraph) :
    CodedCapProfile B (completion.externalBoundedOrder P0 r0 μ0 A0)
      (completion.externalBoundedMeet P0 r0 μ0 A0) c' e' K'
      (relationImage F B originalGraph) := by
  have geometry := data.externalBoundedGeometryData group oldAction
    pairing unions powers separation infinite hG hP
  rw [completion.externalOriginal_filterImage_eq P0 r0 μ0 A0 B subset]
  exact (geometry.copies _ data.group.group_code.identity_mem).capProfile
    completion.algebra.union.meet geometry.meet completion.top_mem completion.top profile
    ((completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 c c').1 imageC).1
    ((completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 e e').1 imageE).1
    ((completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 K K').1 imageK).1

end GroundExternalGeometryInputs

end PartitionPilot.Forcing

end OAI
