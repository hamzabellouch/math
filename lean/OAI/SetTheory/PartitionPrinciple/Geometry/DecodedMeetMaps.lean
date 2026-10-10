import OAI.SetTheory.PartitionPrinciple.Forcing.ActionPostcompositionCodes

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace MeetEmbeddingCode

variable {P L rP rL μP μL S : ZFSet.{u}}
variable (embedding : MeetEmbeddingCode P L rP rL μP μL S)

noncomputable def value (x : {x : ZFSet.{u} // x ∈ P}) :
    {y : ZFSet.{u} // y ∈ L} :=
  let graph : FunctionGraphOn P S := ⟨L, embedding.injection.function⟩
  ⟨graph.value x, (ZFSet.pair_mem_prod.1
    (embedding.injection.function.1 (graph.value_entry x))).2⟩

theorem value_entry (x : {x : ZFSet.{u} // x ∈ P}) :
    ZFSet.pair x.val (embedding.value x).val ∈ S :=
  (show FunctionGraphOn P S from ⟨L, embedding.injection.function⟩).value_entry x

theorem value_eq_iff (x : {x : ZFSet.{u} // x ∈ P})
    (y : {y : ZFSet.{u} // y ∈ L}) :
    embedding.value x = y ↔ ZFSet.pair x.val y.val ∈ S := by
  constructor
  · intro equal
    exact equal ▸ embedding.value_entry x
  · intro entry
    exact Subtype.ext ((show FunctionGraphOn P S from
      ⟨L, embedding.injection.function⟩).unique (embedding.value_entry x) entry)

noncomputable def toMeetEmbedding (source : MeetOrderCode P rP μP)
    (target : MeetOrderCode L rL μL) :
    MeetEmbedding source.toMeetOrder target.toMeetOrder where
  toFun := embedding.value
  le_iff x y := embedding.order_iff source target
    (embedding.value_entry x) (embedding.value_entry y)
  map_meet x y := by
    apply Subtype.ext
    exact (show FunctionGraphOn (ZFSet.prod L L) μL from
      ⟨L, target.operation⟩).unique
      (embedding.map_meet _ _ _ _ _ _ (source.toMeetOrder_meet_entry x y)
        (embedding.value_entry x) (embedding.value_entry y)
        (embedding.value_entry (source.toMeetOrder.meet x y)))
      (target.toMeetOrder_meet_entry (embedding.value x) (embedding.value y))

theorem toMeetEmbedding_entry (source : MeetOrderCode P rP μP)
    (target : MeetOrderCode L rL μL) (x : {x : ZFSet.{u} // x ∈ P}) :
    ZFSet.pair x.val ((embedding.toMeetEmbedding source target).toFun x).val ∈ S :=
  embedding.value_entry x

theorem toMeetEmbedding_eq_iff (source : MeetOrderCode P rP μP)
    (target : MeetOrderCode L rL μL) (x : {x : ZFSet.{u} // x ∈ P})
    (y : {y : ZFSet.{u} // y ∈ L}) :
    (embedding.toMeetEmbedding source target).toFun x = y ↔
      ZFSet.pair x.val y.val ∈ S := embedding.value_eq_iff x y

end MeetEmbeddingCode

namespace PosetActionCode

variable {G P m inv e r μ A : ZFSet.{u}}
variable (action : PosetActionCode G P m e r A)

noncomputable def rawAct (g : {g : ZFSet.{u} // g ∈ G})
    (x : {x : ZFSet.{u} // x ∈ P}) : {y : ZFSet.{u} // y ∈ P} :=
  let graph : FunctionGraphOn (ZFSet.prod G P) A := ⟨P, action.function⟩
  let input := (⟨ZFSet.pair g.val x.val,
    ZFSet.pair_mem_prod.2 ⟨g.property, x.property⟩⟩ :
      {z : ZFSet.{u} // z ∈ ZFSet.prod G P})
  ⟨graph.value input, (ZFSet.pair_mem_prod.1
    (action.function.1 (graph.value_entry input))).2⟩

theorem rawAct_entry (g : {g : ZFSet.{u} // g ∈ G})
    (x : {x : ZFSet.{u} // x ∈ P}) :
    ZFSet.pair (ZFSet.pair g.val x.val) (action.rawAct g x).val ∈ A :=
  (show FunctionGraphOn (ZFSet.prod G P) A from ⟨P, action.function⟩).value_entry
    ⟨ZFSet.pair g.val x.val, ZFSet.pair_mem_prod.2 ⟨g.property, x.property⟩⟩

theorem rawAct_eq_iff (g : {g : ZFSet.{u} // g ∈ G})
    (x y : {x : ZFSet.{u} // x ∈ P}) :
    action.rawAct g x = y ↔ ZFSet.pair (ZFSet.pair g.val x.val) y.val ∈ A := by
  constructor
  · intro equal
    exact equal ▸ action.rawAct_entry g x
  · intro entry
    exact Subtype.ext ((show FunctionGraphOn (ZFSet.prod G P) A from
      ⟨P, action.function⟩).unique (action.rawAct_entry g x) entry)

theorem rawAct_injective (group : GroupCode G m inv e) (order : PartialOrderCode P r)
    (g : {g : ZFSet.{u} // g ∈ G}) : Function.Injective (action.rawAct g) := by
  intro x y equal
  have lower : ZFSet.pair (action.rawAct g x).val (action.rawAct g y).val ∈ r := by
    rw [equal]
    exact order.refl _ (action.rawAct g y).property
  have back : ZFSet.pair (action.rawAct g y).val (action.rawAct g x).val ∈ r := by
    rw [equal]
    exact order.refl _ (action.rawAct g y).property
  exact Subtype.ext (order.antisymm x.val x.property y.val y.property
    ((action.raw_order_iff group order g.property
      (action.rawAct_entry g x) (action.rawAct_entry g y)).1 lower)
    ((action.raw_order_iff group order g.property
      (action.rawAct_entry g y) (action.rawAct_entry g x)).1 back))

theorem rawAct_surjective (group : GroupCode G m inv e)
    (g : {g : ZFSet.{u} // g ∈ G}) : Function.Surjective (action.rawAct g) := by
  intro y
  obtain ⟨x, hx, entry⟩ := action.raw_preimage group g.property y.property
  exact ⟨⟨x, hx⟩, (action.rawAct_eq_iff g ⟨x, hx⟩ y).2 entry⟩

noncomputable def toMeetIso (group : GroupCode G m inv e) (meet : MeetOrderCode P r μ)
    (g : {g : ZFSet.{u} // g ∈ G}) :
    Compression.MeetIso meet.toMeetOrder meet.toMeetOrder where
  toFun := action.rawAct g
  le_iff x y := action.raw_order_iff group meet.order g.property
    (action.rawAct_entry g x) (action.rawAct_entry g y)
  map_meet x y := by
    apply Subtype.ext
    exact (show FunctionGraphOn (ZFSet.prod P P) μ from ⟨P, meet.operation⟩).unique
      (action.raw_map_meet group meet g.property (meet.toMeetOrder_meet_entry x y)
        (action.rawAct_entry g x) (action.rawAct_entry g y)
        (action.rawAct_entry g (meet.toMeetOrder.meet x y)))
      (meet.toMeetOrder_meet_entry (action.rawAct g x) (action.rawAct g y))
  inverse y := Classical.choose (action.rawAct_surjective group g y)
  left_inverse x := action.rawAct_injective group meet.order g
    (Classical.choose_spec (action.rawAct_surjective group g (action.rawAct g x)))
  right_inverse y := Classical.choose_spec (action.rawAct_surjective group g y)

theorem toMeetIso_entry (group : GroupCode G m inv e) (meet : MeetOrderCode P r μ)
    (g : {g : ZFSet.{u} // g ∈ G}) (x : {x : ZFSet.{u} // x ∈ P}) :
    ZFSet.pair (ZFSet.pair g.val x.val)
      ((action.toMeetIso group meet g).toFun x).val ∈ A := action.rawAct_entry g x

theorem toMeetIso_eq_iff (group : GroupCode G m inv e) (meet : MeetOrderCode P r μ)
    (g : {g : ZFSet.{u} // g ∈ G}) (x y : {x : ZFSet.{u} // x ∈ P}) :
    (action.toMeetIso group meet g).toFun x = y ↔
      ZFSet.pair (ZFSet.pair g.val x.val) y.val ∈ A := action.rawAct_eq_iff g x y

end PosetActionCode

end PartitionPilot.Forcing

end

end OAI
