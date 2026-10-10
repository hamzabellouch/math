import OAI.SetTheory.PartitionPrinciple.Definability.GroundRefinementLiftedClassGraphs
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRefinementAssignmentLabelEntries

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P Q : Type u} [PartialOrder P] [OrderTop P]
variable (lower : Presentation P) (upper : Presentation Q)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem refinementAssignmentLabel_mem
    (lowerGround : lower.carrier ∈ M.sets) (upperGround : upper.carrier ∈ M.sets)
    (lowerOrder : lower.conditionOrder ∈ M.sets)
    (incl : P → Q) (inclGround : lower.graph upper incl ∈ M.sets) (one : Q)
    (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName lower z)
    (idx : ZFSet.{u}) (hIdx : idx ∈ M.sets)
    (Rf Rc : Name lower) (hRf : Rf.val ∈ M.sets) (hRc : Rc.val ∈ M.sets) :
    (Name.refinementAssignmentLabel upper incl one T valid idx Rf Rc).val ∈ M.sets := by
  obtain ⟨Gc, hGc, coarse⟩ := M.exists_refinementLiftedClassGraph lower upper
    pairing unions powers separation collection lowerGround upperGround lowerOrder
    incl inclGround T hT valid Rc hRc
  obtain ⟨Gf, hGf, fine⟩ := M.exists_refinementLiftedClassGraph lower upper
    pairing unions powers separation collection lowerGround upperGround lowerOrder
    incl inclGround T hT valid Rf hRf
  exact M.refinementAssignmentLabel_mem_of_graphs upper incl one pairing unions powers separation
    upperGround (M.transitive upperGround (upper.encode_mem one)) hT valid idx hIdx Rf Rc
    Gc Gf hGc hGf coarse fine

end PartitionPilot.Forcing.TransitiveGround

end OAI
