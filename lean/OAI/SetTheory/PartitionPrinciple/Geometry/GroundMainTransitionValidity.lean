import OAI.SetTheory.PartitionPrinciple.Definability.MainTransitionValidityCodes

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace GroundMainTransition
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source target : GroundMainStage M C D rD}

theorem laws (transition : GroundMainTransition source target) :
    MainTransitionLaws source.carrier target.carrier source.order target.order source.meetGraph
      target.meetGraph source.actors target.actors source.multiplication target.multiplication
      source.identity target.identity source.action target.action source.bottom target.bottom
      source.height target.height transition.points transition.actors :=
  ⟨transition.point_embedding, transition.order_iff, transition.group_embedding,
    transition.equivariant, transition.bottom, transition.height, transition.agreement⟩

def ofLaws {points actors : ZFSet.{u}}
    (hPoints : points ∈ M.sets) (hActors : actors ∈ M.sets)
    (valid : MainTransitionLaws source.carrier target.carrier source.order target.order source.meetGraph
      target.meetGraph source.actors target.actors source.multiplication target.multiplication
      source.identity target.identity source.action target.action source.bottom target.bottom
      source.height target.height points actors) : GroundMainTransition source target where
  points := points
  actors := actors
  points_ground := hPoints
  actors_ground := hActors
  point_embedding := valid.point_embedding
  order_iff := valid.order_iff
  group_embedding := valid.group_embedding
  equivariant := valid.equivariant
  bottom := valid.bottom
  height := valid.height
  agreement := valid.agreement

theorem ofLaws_code {points actors : ZFSet.{u}}
    (hPoints : points ∈ M.sets) (hActors : actors ∈ M.sets)
    (valid : MainTransitionLaws source.carrier target.carrier source.order target.order source.meetGraph
      target.meetGraph source.actors target.actors source.multiplication target.multiplication
      source.identity target.identity source.action target.action source.bottom target.bottom
      source.height target.height points actors) :
    (ofLaws hPoints hActors valid).code = ZFSet.pair points actors := rfl

theorem ofLaws_self (transition : GroundMainTransition source target) :
    ofLaws transition.points_ground transition.actors_ground transition.laws = transition :=
  ext rfl rfl

theorem exists_code_iff (z : ZFSet.{u}) :
    (∃ transition : GroundMainTransition source target, transition.code = z) ↔
      ∃ points ∈ M.sets, ∃ actors ∈ M.sets, z = ZFSet.pair points actors ∧
        MainTransitionLaws source.carrier target.carrier source.order target.order source.meetGraph
          target.meetGraph source.actors target.actors source.multiplication target.multiplication
          source.identity target.identity source.action target.action source.bottom target.bottom
          source.height target.height points actors := by
  constructor
  · rintro ⟨transition, equal⟩
    exact ⟨transition.points, transition.points_ground, transition.actors, transition.actors_ground,
      equal.symm, transition.laws⟩
  · rintro ⟨points, hp, actors, ha, equal, valid⟩
    exact ⟨ofLaws hp ha valid, equal.symm⟩

end GroundMainTransition

namespace BoundedFormula

def validMainTransitionCodeFormula {n}
    (z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors : Fin n) :
    BoundedFormula n :=
  .conj (orderedPairFormula z points actors)
    (mainTransitionLawsFormula P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ
      heightP heightQ points actors)

theorem truth_validMainTransitionCodeFormula {n}
    (z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (validMainTransitionCodeFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ
      heightP heightQ points actors) env ↔
      env z = ZFSet.pair (env points) (env actors) ∧
      MainTransitionLaws (env P) (env Q) (env rP) (env rQ) (env μP) (env μQ) (env G) (env H)
        (env mG) (env mH) (env oneG) (env oneH) (env AP) (env AQ) (env bP) (env bQ)
        (env heightP) (env heightQ) (env points) (env actors) := by
  simp only [validMainTransitionCodeFormula, Truth, truth_orderedPairFormula,
    truth_mainTransitionLawsFormula]

theorem realize_validMainTransitionCodeFormula (M : TransitiveGround.{u}) {n}
    (z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (validMainTransitionCodeFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ
      heightP heightQ points actors).toFormula env ↔
      env z = ZFSet.pair (env points) (env actors) ∧
      MainTransitionLaws (env P) (env Q) (env rP) (env rQ) (env μP) (env μQ) (env G) (env H)
        (env mG) (env mH) (env oneG) (env oneH) (env AP) (env AQ) (env bP) (env bQ)
        (env heightP) (env heightQ) (env points) (env actors) :=
  (realize_toFormula M _ env members).trans
    (truth_validMainTransitionCodeFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ
      heightP heightQ points actors env)

end BoundedFormula
end PartitionPilot.Forcing

end

end OAI
