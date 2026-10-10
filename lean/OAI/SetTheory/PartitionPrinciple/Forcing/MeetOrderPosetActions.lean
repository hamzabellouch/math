import OAI.SetTheory.PartitionPrinciple.Forcing.FinitePrincipalNameSupports

namespace OAI

section

namespace PartitionPilot.MeetOrder

universe u

@[instance_reducible]
def toPartialOrder {I : Type u} (P : MeetOrder I) : PartialOrder I where
  le := P.le
  le_refl := P.refl
  le_trans _ _ _ := P.trans
  le_antisymm _ _ := P.antisymm

end PartitionPilot.MeetOrder

namespace PartitionPilot.Compression.MeetIso

universe u v

def toOrderIso {I : Type u} {J : Type v} {P : MeetOrder I} {Q : MeetOrder J} (f : MeetIso P Q) :
    letI := P.toPartialOrder
    letI := Q.toPartialOrder
    I ≃o J := by
  letI := P.toPartialOrder
  letI := Q.toPartialOrder
  exact {
    toFun := f.toFun
    invFun := f.inverse
    left_inv := f.left_inverse
    right_inv := f.right_inverse
    map_rel_iff' := f.le_iff _ _ }

end PartitionPilot.Compression.MeetIso

namespace PartitionPilot.Compression.RecursiveMaps.CosetGeometry.OrderAction

open SetRealization
universe u
variable {I G : Type u} [Group G] {P : MeetOrder I} (a : OrderAction G P)

def toPosetAction :
    letI := P.toPartialOrder
    Forcing.PosetAction G I := by
  letI := P.toPartialOrder
  exact { iso := fun g => (a.iso g).toOrderIso, one := a.one, mul := a.mul }

theorem principalFix_eq (C : I) :
    letI := P.toPartialOrder
    a.toPosetAction.principalFix C = a.fixSubgroup C := rfl

theorem actionGraph_eq (s : GeometryPresentation I G) :
    letI := P.toPartialOrder
    a.toPosetAction.actionGraph s.points s.actors = s.actionGraph P a := rfl

end PartitionPilot.Compression.RecursiveMaps.CosetGeometry.OrderAction

namespace PartitionPilot.SetRealization.GeometryPresentation

universe u

theorem conditionOrder_eq {I G : Type u} (s : GeometryPresentation I G) (P : MeetOrder I) :
    letI := P.toPartialOrder
    s.points.conditionOrder = s.orderRelation P := rfl

end PartitionPilot.SetRealization.GeometryPresentation

end

end OAI
