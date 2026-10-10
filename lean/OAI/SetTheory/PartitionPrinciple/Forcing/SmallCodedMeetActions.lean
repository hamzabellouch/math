import OAI.SetTheory.PartitionPrinciple.Geometry.DecodedMeetMaps

namespace OAI

section

namespace PartitionPilot.Forcing

open SetRealization
universe u

namespace MeetOrderCode

variable {P r μ : ZFSet.{u}} (code : MeetOrderCode P r μ)

noncomputable def smallMeet (x y : SetMembers P) : SetMembers P :=
  ((SetMembers.presentation P).product (SetMembers.presentation P)).decodeFunction
    (SetMembers.presentation P) μ code.operation (x, y)

theorem smallMeet_entry (x y : SetMembers P) :
    ZFSet.pair (ZFSet.pair (SetMembers.raw x) (SetMembers.raw y))
      (SetMembers.raw (code.smallMeet x y)) ∈ μ :=
  ((SetMembers.presentation P).product (SetMembers.presentation P)).decodeFunction_mem
    (SetMembers.presentation P) μ code.operation (x, y)

theorem smallMeet_eq_iff (x y z : SetMembers P) :
    code.smallMeet x y = z ↔ ZFSet.pair (ZFSet.pair (SetMembers.raw x) (SetMembers.raw y))
      (SetMembers.raw z) ∈ μ :=
  ((SetMembers.presentation P).product (SetMembers.presentation P)).decodeFunction_iff
    (SetMembers.presentation P) μ code.operation (x, y) z

noncomputable def toSmallMeetOrder : MeetOrder (SetMembers P) where
  le x y := ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ r
  meet := code.smallMeet
  refl x := code.order.refl _ (SetMembers.raw_mem x)
  trans {x y z} := code.order.trans _ (SetMembers.raw_mem x) _ (SetMembers.raw_mem y)
    _ (SetMembers.raw_mem z)
  antisymm {x y} xy yx := SetMembers.raw_injective P
    (code.order.antisymm _ (SetMembers.raw_mem x) _ (SetMembers.raw_mem y) xy yx)
  meet_le_left x y := code.lower_left _ _ _ (code.smallMeet_entry x y)
  meet_le_right x y := code.lower_right _ _ _ (code.smallMeet_entry x y)
  le_meet {x y z} := code.greatest _ _ _ _ (SetMembers.raw_mem x) (code.smallMeet_entry y z)

theorem toSmallMeetOrder_le_iff (x y : SetMembers P) :
    code.toSmallMeetOrder.le x y ↔ ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ r := Iff.rfl

theorem toSmallMeetOrder_meet_entry (x y : SetMembers P) :
    ZFSet.pair (ZFSet.pair (SetMembers.raw x) (SetMembers.raw y))
      (SetMembers.raw (code.toSmallMeetOrder.meet x y)) ∈ μ := code.smallMeet_entry x y

theorem toSmallMeetOrder_meet_eq_iff (x y z : SetMembers P) :
    code.toSmallMeetOrder.meet x y = z ↔
      ZFSet.pair (ZFSet.pair (SetMembers.raw x) (SetMembers.raw y)) (SetMembers.raw z) ∈ μ :=
  code.smallMeet_eq_iff x y z

theorem smallMeet_graph_eq :
    ((SetMembers.presentation P).product (SetMembers.presentation P)).graph
      (SetMembers.presentation P) (fun xy => code.toSmallMeetOrder.meet xy.1 xy.2) = μ :=
  ((SetMembers.presentation P).product (SetMembers.presentation P)).graph_decodeFunction
    (SetMembers.presentation P) μ code.operation

end MeetOrderCode

namespace PosetActionCode

variable {G P m inv one r μ A : ZFSet.{u}} (action : PosetActionCode G P m one r A)

noncomputable def toSmallMeetIso (group : GroupCode G m inv one) (meet : MeetOrderCode P r μ)
    (g : SetMembers G) : Compression.MeetIso meet.toSmallMeetOrder meet.toSmallMeetOrder := by
  letI := group.toGroup
  exact {
    toFun := action.act g
    le_iff := fun x y => action.raw_order_iff group meet.order (SetMembers.raw_mem g)
      (action.act_mem g x) (action.act_mem g y)
    map_meet := fun x y => by
      symm
      apply (meet.smallMeet_eq_iff _ _ _).2
      exact action.raw_map_meet group meet (SetMembers.raw_mem g) (meet.smallMeet_entry x y)
        (action.act_mem g x) (action.act_mem g y) (action.act_mem g (meet.smallMeet x y))
    inverse := action.act g⁻¹
    left_inverse := action.act_inv_left group g
    right_inverse := action.act_inv_right group g }

noncomputable def toOrderAction (group : GroupCode G m inv one) (meet : MeetOrderCode P r μ) :
    letI := group.toGroup
    Compression.RecursiveMaps.CosetGeometry.OrderAction (SetMembers G) meet.toSmallMeetOrder := by
  letI := group.toGroup
  exact {
    iso := action.toSmallMeetIso group meet
    one := action.act_one group
    mul := action.act_mul group }

theorem toOrderAction_entry (group : GroupCode G m inv one) (meet : MeetOrderCode P r μ)
    (g : SetMembers G) (x : SetMembers P) :
    letI := group.toGroup
    ZFSet.pair (ZFSet.pair (SetMembers.raw g) (SetMembers.raw x))
      (SetMembers.raw (((action.toOrderAction group meet).iso g).toFun x)) ∈ A := action.act_mem g x

theorem toOrderAction_eq_iff (group : GroupCode G m inv one) (meet : MeetOrderCode P r μ)
    (g : SetMembers G) (x y : SetMembers P) :
    letI := group.toGroup
    ((action.toOrderAction group meet).iso g).toFun x = y ↔
      ZFSet.pair (ZFSet.pair (SetMembers.raw g) (SetMembers.raw x)) (SetMembers.raw y) ∈ A :=
  action.act_eq_iff g x y

theorem toOrderAction_graph_eq (group : GroupCode G m inv one) (meet : MeetOrderCode P r μ) :
    letI := group.toGroup
    ((SetMembers.presentation G).product (SetMembers.presentation P)).graph (SetMembers.presentation P)
      (fun gx => ((action.toOrderAction group meet).iso gx.1).toFun gx.2) = A :=
  ((SetMembers.presentation G).product (SetMembers.presentation P)).graph_decodeFunction
    (SetMembers.presentation P) A action.function

end PosetActionCode

end PartitionPilot.Forcing

end

end OAI
