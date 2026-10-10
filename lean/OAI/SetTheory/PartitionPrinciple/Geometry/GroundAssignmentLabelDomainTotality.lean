import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRepresentedDomainConditions

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P Q : Type u}
variable [PartialOrder P] [OrderTop P] [PartialOrder Q] [OrderTop Q]
variable (lower : Presentation P) (upper : Presentation Q)
variable {restriction : Q →o P} {inclusion : P ↪o Q}
variable (projection : CompleteProjection restriction inclusion)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (lowerGround : lower.carrier ∈ M.sets) (upperGround : upper.carrier ∈ M.sets)
variable (lowerOrder : lower.conditionOrder ∈ M.sets)
variable (inclusionGround : lower.graph upper inclusion ∈ M.sets)
variable {levels alpha T : ZFSet.{u}}
variable (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets) (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName lower z) (idx : ZFSet.{u}) (hIdx : idx ∈ M.sets)
variable (U Rc : (M.nameDomain lower).names) (Rf : Name lower)
variable (cutCoordinates : ∀ p : Q, ∃ row A : ZFSet.{u}, upper.encode p = ZFSet.pair row A ∧
  lower.encode (restriction p) = ZFSet.pair row (assignmentCut levels alpha A))
variable (H : ConditionFilter Q) (ordinary : H.GenericFor (formulaFamily (M.nameDomain upper)))
include pairing unions powers separation collection lowerGround upperGround lowerOrder inclusionGround
  hLevels hAlpha hT hIdx cutCoordinates ordinary

local notation "lowerH" => projection.projectedFilter H
local notation "label" => Name.refinementAssignmentLabel upper inclusion ⊤ T valid idx Rf Rc.val
local notation "domainSet" => (M.representedDomainConditions lower upper.carrier levels alpha T valid idx U Rc)

theorem refinementAssignmentLabel_represents_active_term
    (u : (M.nameDomain lower).names) (_hu : u.val.val ∈ T)
    (ground : domainSet u ∈ M.sets)
    (dense : Dense {p : Q | upper.encode p ∈ domainSet u})
    (active : ∃ q : P, (lowerH).mem q ∧ Name.ForcesMem q u.val U.val) :
    ∃ a : ZFSet.{u}, ZFSet.pair
      (Name.eval {q | (lowerH).mem q} (Name.refinementClass T valid Rc.val u.val)) a ∈
      Name.eval {p | H.mem p} label := by
  obtain ⟨p, hp, inD⟩ := M.ordinary_generic_meets_ground_dense upper pairing unions powers separation
    H ordinary ground (M.representedDomainConditions_subset lower _ _ _ _ valid idx U Rc u) dense
  obtain ⟨row, A, pCode, cutCode⟩ := cutCoordinates p
  have cutMember : (lowerH).mem (restriction p) :=
    (projection.projectedFilter_mem_iff H _).2 ⟨p, hp, rfl⟩
  have branches := (M.pair_mem_representedDomainConditions lower pairing unions powers separation collection
    lowerGround lowerOrder upperGround hLevels hAlpha hT valid hIdx U Rc u row A
    (restriction p) cutCode).1 (pCode ▸ inD)
  rcases branches.2 with inactive | ⟨_active, v, w, hv, hw, literal, forcedEqual⟩
  · obtain ⟨q, hq, activeQ⟩ := active
    obtain ⟨r, _hr, rp, rq⟩ := (lowerH).directed cutMember hq
    exact False.elim (inactive r rp (Name.forcesMem_mono activeQ rq))
  · have classU := M.refinementClass_mem lower pairing unions powers separation collection
      lowerGround lowerOrder hT valid Rc.val u.val Rc.property u.property
    have classV := M.refinementClass_mem lower pairing unions powers separation collection
      lowerGround lowerOrder hT valid Rc.val v Rc.property (M.transitive hT hv)
    have equal := (M.completeProjection_eval_eq_iff_forcesEq lower upper projection
      pairing unions powers separation collection lowerGround upperGround inclusionGround H ordinary
      (Name.refinementClass T valid Rc.val u.val) (Name.refinementClass T valid Rc.val v)
      classU classV).2 ⟨restriction p, cutMember, forcedEqual⟩
    let a := Name.eval {q | (lowerH).mem q} (Name.refinementClass T valid Rf w)
    refine ⟨a, (Name.mem_eval_refinementAssignmentLabel upper inclusion ⊤ T valid idx Rf Rc.val
      {p | H.mem p} H.top_mem _).2 ?_⟩
    exact ⟨p, v, w, hp, hv, hw, ⟨row, A, pCode, literal⟩,
      congrArg (fun x => ZFSet.pair x a) equal.symm⟩

theorem refinementAssignmentLabel_domain_total
    (density : ∀ u : (M.nameDomain lower).names, u.val.val ∈ T →
      domainSet u ∈ M.sets ∧ Dense {p : Q | upper.encode p ∈ domainSet u}) :
    ∀ b ∈ Name.eval {q | (lowerH).mem q} (Name.refinementQuotient T valid U.val Rc.val),
      ∃ a : ZFSet.{u}, ZFSet.pair b a ∈ Name.eval {p | H.mem p} label := by
  intro b member
  obtain ⟨sigma, q, entry, hq, equal⟩ := (Name.mem_eval {q | (lowerH).mem q}
    (Name.refinementQuotient T valid U.val Rc.val) b).1 member
  obtain ⟨u, hu, active, rfl⟩ := (Name.entry_refinementQuotient T valid U.val Rc.val sigma q).1 entry
  let term : (M.nameDomain lower).names := ⟨u, M.transitive hT hu⟩
  have result := M.refinementAssignmentLabel_represents_active_term lower upper projection
    pairing unions powers separation collection lowerGround upperGround lowerOrder inclusionGround
    hLevels hAlpha hT valid idx hIdx U Rc Rf cutCoordinates H ordinary term hu
    (density term hu).1 (density term hu).2 ⟨q, hq, active⟩
  exact equal ▸ result

end PartitionPilot.Forcing.TransitiveGround

end OAI
