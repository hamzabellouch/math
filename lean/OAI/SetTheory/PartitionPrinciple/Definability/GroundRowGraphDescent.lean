import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalSeparatedActors

namespace OAI

section

namespace PartitionPilot.Forcing.Rows

open SetRealization SetFormula Compression.RecursiveMaps
open Compression.RecursiveMaps.CountableColumns Compression.RecursiveMaps.MainStage.OrdinalRun

theorem ground_row_common_support_from_graphs (M : TransitiveGround.{1})
    (t : Presentation (FinalActor Column)) (b : Presentation (FinalPoint Column))
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : namePresentation.carrier ∈ M.sets) (order : namePresentation.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (support_order : (GeometryPresentation.mk b t).orderRelation (finalOrder Column) ∈ M.sets)
    (support_action : (GeometryPresentation.mk b t).actionGraph (finalOrder Column) (finalAction Column) ∈ M.sets)
    (forcing_action : posetAction.actionGraph namePresentation t ∈ M.sets)
    (H : ConditionFilter RowForcing) (generic : H.GenericFor (rowAtomicFamily (M.nameDomain namePresentation)))
    (C B : FinalPoint Column) (x y : Name namePresentation)
    (hx : x.val ∈ M.sets) (hy : y.val ∈ M.sets)
    (sx : (finalAction Column).fixSubgroup C ≤ posetAction.stabilizer namePresentation x)
    (sy : (finalAction Column).fixSubgroup B ≤ posetAction.stabilizer namePresentation y)
    (hs : HereditarilySymmetric posetAction namePresentation (supportFamily Column) x)
    (values : Name.eval {q | H.mem q} x = Name.eval {q | H.mem q} y) :
    ∃ z : Name namePresentation, z.val ∈ M.sets ∧
      HereditarilySymmetric posetAction namePresentation (supportFamily Column) z ∧
      (finalAction Column).fixSubgroup ((finalOrder Column).meet C B) ≤ posetAction.stabilizer namePresentation z ∧
      Name.nameRank z ≤ Name.nameRank x ∧ Name.eval {q | H.mem q} z = Name.eval {q | H.mem q} x :=
  ground_row_common_support M t b pairing unions powers separation collection carrier order group nodes
    (M.geometry_supportBasis_mem (GeometryPresentation.mk b t) (finalOrder Column) (finalAction Column)
      pairing unions powers separation nodes group support_order support_action)
    (M.conditionMapFamily_mem_of_actionGraph posetAction namePresentation t pairing unions powers separation collection
      carrier group forcing_action)
    H generic C B x y hx hy sx sy hs values

end PartitionPilot.Forcing.Rows

end

end OAI
