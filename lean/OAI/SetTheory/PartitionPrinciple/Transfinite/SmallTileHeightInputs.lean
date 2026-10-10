import OAI.SetTheory.PartitionPrinciple.Geometry.RectangleFulfillmentAtBound

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression Compression.RecursiveMaps
universe u

namespace MeetEmbeddingCode
variable {P Q rP rQ μP μQ f : ZFSet.{u}}
variable (embedding : MeetEmbeddingCode P Q rP rQ μP μQ f)

noncomputable def smallValue (x : SetMembers P) : SetMembers Q :=
  (SetMembers.presentation P).decodeFunction (SetMembers.presentation Q) f
    embedding.injection.function x

theorem smallValue_entry (x : SetMembers P) :
    ZFSet.pair (SetMembers.raw x) (SetMembers.raw (embedding.smallValue x)) ∈ f :=
  (SetMembers.presentation P).decodeFunction_mem (SetMembers.presentation Q) f
    embedding.injection.function x

theorem smallValue_eq_iff (x : SetMembers P) (y : SetMembers Q) :
    embedding.smallValue x = y ↔ ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ f :=
  (SetMembers.presentation P).decodeFunction_iff (SetMembers.presentation Q) f
    embedding.injection.function x y

noncomputable def toSmallMeetEmbedding (source : MeetOrderCode P rP μP)
    (target : MeetOrderCode Q rQ μQ) :
    MeetEmbedding source.toSmallMeetOrder target.toSmallMeetOrder where
  toFun := embedding.smallValue
  le_iff x y := embedding.order_iff source target
    (embedding.smallValue_entry x) (embedding.smallValue_entry y)
  map_meet x y := by
    symm
    apply (target.smallMeet_eq_iff _ _ _).2
    exact embedding.map_meet _ _ _ _ _ _ (source.smallMeet_entry x y)
      (embedding.smallValue_entry x) (embedding.smallValue_entry y)
      (embedding.smallValue_entry (source.smallMeet x y))

end MeetEmbeddingCode

noncomputable def smallCompressionTileIso {P r μ f : ZFSet.{u}}
    (meet : MeetOrderCode P r μ) (embedding : MeetEmbeddingCode P P r r μ μ f)
    (K : SetMembers P)
    (range : ∀ z, (∃ x ∈ P, ZFSet.pair x z ∈ f) ↔
      z ∈ P ∧ ZFSet.pair z (SetMembers.raw K) ∈ r) :
    MeetIso meet.toSmallMeetOrder (Attachment.idealOrder meet.toSmallMeetOrder K) := by
  apply isoOntoIdeal meet.toSmallMeetOrder (embedding.toSmallMeetEmbedding meet meet) K
  · intro x
    exact ((range _).1 ⟨SetMembers.raw x, SetMembers.raw_mem x, embedding.smallValue_entry x⟩).2
  · intro z hz
    obtain ⟨x, hx, entry⟩ := (range (SetMembers.raw z)).2 ⟨SetMembers.raw_mem z, hz⟩
    refine ⟨SetMembers.ofMem x hx, (embedding.smallValue_eq_iff _ z).2 ?_⟩
    simpa only [SetMembers.raw_ofMem] using entry

theorem smallCompressionTileIso_entry {P r μ f : ZFSet.{u}}
    (meet : MeetOrderCode P r μ) (embedding : MeetEmbeddingCode P P r r μ μ f)
    (K : SetMembers P)
    (range : ∀ z, (∃ x ∈ P, ZFSet.pair x z ∈ f) ↔
      z ∈ P ∧ ZFSet.pair z (SetMembers.raw K) ∈ r) (x : SetMembers P) :
    ZFSet.pair (SetMembers.raw x)
      (SetMembers.raw ((smallCompressionTileIso meet embedding K range).toFun x).val) ∈ f :=
  embedding.smallValue_entry x

variable {P G r μ A m inv one c b d g h : ZFSet.{u}}

noncomputable def ExternalRectangleCode.toSmallActionRectangle
    (code : ExternalRectangleCode P G r μ A c b d g h)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) :
    ActionRectangle meet.toSmallMeetOrder (action.toSmallMeetIso group meet) := by
  obtain ⟨hc, hb, hd, hg, hh, cd, bd, witness⟩ := code
  let w := Classical.choose witness
  have mw := (Classical.choose_spec witness).2.1
  have agree := (Classical.choose_spec witness).2.2.1
  have separated := (Classical.choose_spec witness).2.2.2
  let C := SetMembers.ofMem c hc
  let B := SetMembers.ofMem b hb
  let D := SetMembers.ofMem d hd
  let first := SetMembers.ofMem g hg
  let second := SetMembers.ofMem h hh
  have meetValue : SetMembers.raw (meet.smallMeet C B) = w := by
    apply (show FunctionGraphOn (ZFSet.prod P P) μ from ⟨P, meet.operation⟩).unique
      (meet.smallMeet_entry C B)
    simpa only [C, B, SetMembers.raw_ofMem] using mw
  refine {
    C := C
    B := B
    D := D
    first := first
    second := second
    C_le_D := ?_
    B_le_D := ?_
    agree := ?_
    separated := ?_ }
  · simpa only [MeetOrderCode.toSmallMeetOrder, C, D, SetMembers.raw_ofMem] using cd
  · simpa only [MeetOrderCode.toSmallMeetOrder, B, D, SetMembers.raw_ofMem] using bd
  · intro x lower
    apply SetMembers.raw_injective P
    have lowerW : ZFSet.pair (SetMembers.raw x) w ∈ r := meetValue ▸ lower
    apply agree.entry_eq action hh (SetMembers.raw_mem x) lowerW
    · simpa only [first, SetMembers.raw_ofMem, PosetActionCode.toSmallMeetIso] using action.act_mem first x
    · simpa only [second, SetMembers.raw_ofMem, PosetActionCode.toSmallMeetIso] using action.act_mem second x
  · apply SetMembers.raw_injective P
    let y := action.act first D
    let z := action.act second D
    let v := action.act first (meet.smallMeet C B)
    have actMeet : ZFSet.pair (ZFSet.pair g w) (SetMembers.raw v) ∈ A := by
      rw [← meetValue]
      simpa only [first, SetMembers.raw_ofMem] using action.act_mem first (meet.smallMeet C B)
    have value := separated (SetMembers.raw y) (SetMembers.raw_mem y)
      (SetMembers.raw z) (SetMembers.raw_mem z) (SetMembers.raw v) (SetMembers.raw_mem v)
      ⟨by simpa only [first, D, SetMembers.raw_ofMem] using action.act_mem first D,
        by simpa only [second, D, SetMembers.raw_ofMem] using action.act_mem second D, actMeet⟩
    exact (show FunctionGraphOn (ZFSet.prod P P) μ from ⟨P, meet.operation⟩).unique
      (meet.smallMeet_entry y z) value

theorem ExternalRectangleCode.toSmallActionRectangle_fields
    (code : ExternalRectangleCode P G r μ A c b d g h)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) :
    let request := code.toSmallActionRectangle group action meet
    SetMembers.raw request.C = c ∧ SetMembers.raw request.B = b ∧
      SetMembers.raw request.D = d ∧ SetMembers.raw request.first = g ∧ SetMembers.raw request.second = h := by
  obtain ⟨hc, hb, hd, hg, hh, cd, bd, witness⟩ := code
  exact ⟨SetMembers.raw_ofMem _ _, SetMembers.raw_ofMem _ _, SetMembers.raw_ofMem _ _,
    SetMembers.raw_ofMem _ _, SetMembers.raw_ofMem _ _⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps
universe u
variable {P L r μ v ν f : ZFSet.{u}}

noncomputable def MeetEmbeddingCode.smallIdealEmbedding
    (embedding : MeetEmbeddingCode P L r v μ ν f)
    (source : MeetOrderCode P r μ) (target : MeetOrderCode L v ν)
    (ideal : ∀ x y z, ZFSet.pair x y ∈ f → z ∈ L → ZFSet.pair z y ∈ v →
      ∃ a ∈ P, ZFSet.pair a z ∈ f) :
    IdealEmbedding source.toSmallMeetOrder target.toSmallMeetOrder where
  toMeetEmbedding := embedding.toSmallMeetEmbedding source target
  ideal a z lower := by
    obtain ⟨x, hx, entry⟩ := ideal _ _ _ (embedding.smallValue_entry a) (SetMembers.raw_mem z) lower
    refine ⟨SetMembers.ofMem x hx, (embedding.smallValue_eq_iff _ z).2 ?_⟩
    simpa only [SetMembers.raw_ofMem] using entry

theorem MeetEmbeddingCode.smallValue_graph (embedding : MeetEmbeddingCode P L r v μ ν f) :
    (SetMembers.presentation P).graph (SetMembers.presentation L) embedding.smallValue = f :=
  (SetMembers.presentation P).graph_decodeFunction (SetMembers.presentation L) f embedding.injection.function

noncomputable def binaryTileOfCodes {first second : ZFSet.{u}}
    (source : MeetOrderCode P r μ) (target : MeetOrderCode L v ν)
    (left : MeetEmbeddingCode P L r v μ ν first) (right : MeetEmbeddingCode P L r v μ ν second)
    (leftIdeal : ∀ x y z, ZFSet.pair x y ∈ first → z ∈ L → ZFSet.pair z y ∈ v →
      ∃ a ∈ P, ZFSet.pair a z ∈ first)
    (rightIdeal : ∀ x y z, ZFSet.pair x y ∈ second → z ∈ L → ZFSet.pair z y ∈ v →
      ∃ a ∈ P, ZFSet.pair a z ∈ second)
    (cover : ∀ z ∈ L, (∃ x ∈ P, ZFSet.pair x z ∈ first) ∨ ∃ x ∈ P, ZFSet.pair x z ∈ second) :
    TileRequests.Tile source.toSmallMeetOrder (ULift.{u} Unit) where
  Space := SetMembers L
  order := target.toSmallMeetOrder
  root := left.smallIdealEmbedding source target leftIdeal
  child _ := right.smallIdealEmbedding source target rightIdeal
  cover z := by
    rcases cover (SetMembers.raw z) (SetMembers.raw_mem z) with ⟨x, hx, entry⟩ | ⟨x, hx, entry⟩
    · refine Or.inl ⟨SetMembers.ofMem x hx, (left.smallValue_eq_iff _ z).2 ?_⟩
      simpa only [SetMembers.raw_ofMem] using entry
    · refine Or.inr ⟨⟨()⟩, SetMembers.ofMem x hx, (right.smallValue_eq_iff _ z).2 ?_⟩
      simpa only [SetMembers.raw_ofMem] using entry

end PartitionPilot.Forcing

end

end OAI
