import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStageOneAssignmentUnions

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {Lower Upper : Type u}
variable [PartialOrder Lower] [PartialOrder Upper]
variable (lower : Presentation Lower) (upper : Presentation Upper)
variable {restriction : Upper →o Lower} {inclusion : Lower ↪o Upper}
variable (projection : CompleteProjection restriction inclusion)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (lowerGround : lower.carrier ∈ M.sets) (upperGround : upper.carrier ∈ M.sets)
variable (inclusionGround : lower.graph upper inclusion ∈ M.sets)
include pairing unions powers separation collection lowerGround upperGround inclusionGround

theorem completeProjection_refinementCollision_eval
    (H : ConditionFilter Upper) (ordinary : H.GenericFor (formulaFamily (M.nameDomain upper)))
    (env : Assignment (M.nameDomain lower) 4) {q : Lower}
    (member : (projection.projectedFilter H).mem q)
    (test : Forces (M.nameDomain lower) refinementCollisionFormula env q) :
    (Name.eval {r | (projection.projectedFilter H).mem r} (env 0).val =
      Name.eval {r | (projection.projectedFilter H).mem r} (env 1).val ↔
    Name.eval {r | (projection.projectedFilter H).mem r} (env 2).val =
      Name.eval {r | (projection.projectedFilter H).mem r} (env 3).val) := by
  let lifted : Assignment (M.nameDomain upper) 4 := fun i =>
    ⟨Name.rename upper inclusion (env i).val,
      M.rename_between_mem lower upper pairing unions powers separation collection
        lowerGround upperGround inclusion inclusionGround (env i).val (env i).property⟩
  have atomic (p : Upper) (i j : Fin 4) :
      Name.ForcesEq p (lifted i).val (lifted j).val ↔
        Name.ForcesEq (restriction p) (env i).val (env j).val :=
    Name.forcesEq_rename_completeProjection lower upper restriction inclusion projection p _ _
  have transfer (i j k l : Fin 4)
      (clause : ∀ r, r ≤ q → ¬ (Name.ForcesEq r (env i).val (env j).val ∧
        ∀ p, p ≤ r → ¬ Name.ForcesEq p (env k).val (env l).val)) :
      ∀ r, r ≤ inclusion q → ¬ (Name.ForcesEq r (lifted i).val (lifted j).val ∧
        ∀ p, p ≤ r → ¬ Name.ForcesEq p (lifted k).val (lifted l).val) := by
    intro r rq facts
    apply clause (restriction r) ((projection.le_include_iff r q).1 rq)
    refine ⟨(atomic r i j).1 facts.1, ?_⟩
    intro p pr eq
    obtain ⟨v, vr, vp⟩ := projection.lift r p pr
    apply facts.2 v vr
    exact (atomic v k l).2 (vp.symm ▸ eq)
  have upperTest : Forces (M.nameDomain upper) refinementCollisionFormula lifted (inclusion q) :=
    ⟨transfer 0 1 2 3 test.1, transfer 2 3 0 1 test.2⟩
  have evaluated := M.refinementCollision_eval upper lifted H ordinary member upperTest
  simpa only [lifted, Name.eval_rename, CompleteProjection.projectedFilter,
    Set.mem_ofPred_eq] using evaluated

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
