import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundTwoStageMainDiagram

namespace OAI

section

namespace PartitionPilot.Forcing.GroundChronologicalMainDiagram
open SetFormula
universe u v w
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Preorder I] {J : Type w} [Preorder J]
variable (diagram : GroundChronologicalMainDiagram M C D rD pairing unions powers separation I)
variable (f : J → I) (mono : Monotone f)

def reindex : GroundChronologicalMainDiagram M C D rD pairing unions powers separation J where
  stage j := diagram.stage (f j)
  transition before := diagram.transition (mono before)
  self j := diagram.self (f j)
  comp first second := diagram.comp (mono first) (mono second)

theorem CoversOldBirths.reindex (coverage : diagram.CoversOldBirths) :
    (diagram.reindex f mono).CoversOldBirths :=
  fun before => coverage (mono before)

end PartitionPilot.Forcing.GroundChronologicalMainDiagram



namespace PartitionPilot.Forcing.GroundChronologicalMainDiagram
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Preorder I]
variable (diagram : GroundChronologicalMainDiagram M C D rD pairing unions powers separation I)

structure Cone (target : GroundChronologicalMainStage M C D rD) where
  leg : ∀ i, GroundChronologicalMainTransition (diagram.stage i) target
  coherent : ∀ {i j} (before : i ≤ j),
    (diagram.transition before).comp pairing unions powers separation (leg j) = leg i

noncomputable def coneOfLast (last : I) (greatest : ∀ i, i ≤ last)
    {target : GroundChronologicalMainStage M C D rD}
    (step : GroundChronologicalMainTransition (diagram.stage last) target) : diagram.Cone target where
  leg i := (diagram.transition (greatest i)).comp pairing unions powers separation step
  coherent := by
    intro i j before
    rw [← GroundChronologicalMainTransition.comp_assoc, ← diagram.comp]

namespace Cone
variable {diagram} {target : GroundChronologicalMainStage M C D rD} (cone : diagram.Cone target)

def appendStage (_cone : diagram.Cone target) : WithTop I → GroundChronologicalMainStage M C D rD
  | none => target
  | some i => diagram.stage i

noncomputable def appendTransition {i j : WithTop I} (before : i ≤ j) :
    GroundChronologicalMainTransition (cone.appendStage i) (cone.appendStage j) := by
  cases i with
  | top =>
    cases j with
    | top => exact GroundChronologicalMainTransition.identity pairing unions powers separation target
    | coe j => exact False.elim (WithTop.not_top_le_coe j before)
  | coe i =>
    cases j with
    | top => exact cone.leg i
    | coe j => exact diagram.transition (WithTop.coe_le_coe.mp before)

theorem appendTransition_self (i : WithTop I) :
    cone.appendTransition (le_refl i) =
      GroundChronologicalMainTransition.identity pairing unions powers separation (cone.appendStage i) := by
  cases i with
  | top => rfl
  | coe i => exact diagram.self i

theorem appendTransition_comp {i j k : WithTop I} (hij : i ≤ j) (hjk : j ≤ k) :
    cone.appendTransition (le_trans hij hjk) =
      (cone.appendTransition hij).comp pairing unions powers separation (cone.appendTransition hjk) := by
  cases i with
  | top =>
    cases j with
    | coe j => exact False.elim (WithTop.not_top_le_coe j hij)
    | top =>
      cases k with
      | coe k => exact False.elim (WithTop.not_top_le_coe k hjk)
      | top => exact (GroundChronologicalMainTransition.identity_comp pairing unions powers separation _).symm
  | coe i =>
    cases j with
    | top =>
      cases k with
      | coe k => exact False.elim (WithTop.not_top_le_coe k hjk)
      | top => exact (GroundChronologicalMainTransition.comp_identity pairing unions powers separation _).symm
    | coe j =>
      cases k with
      | top => exact (cone.coherent (WithTop.coe_le_coe.mp hij)).symm
      | coe k => exact diagram.comp (WithTop.coe_le_coe.mp hij) (WithTop.coe_le_coe.mp hjk)

noncomputable def append :
    GroundChronologicalMainDiagram M C D rD pairing unions powers separation (WithTop I) where
  stage := cone.appendStage
  transition := cone.appendTransition
  self := cone.appendTransition_self
  comp := cone.appendTransition_comp

theorem append_reindex : cone.append.reindex (fun i : I => (i : WithTop I)) WithTop.coe_mono = diagram := rfl

theorem append_coverage (old : diagram.CoversOldBirths)
    (legs : ∀ i, (cone.leg i).CoversOldBirths) : cone.append.CoversOldBirths := by
  intro i j before
  cases i with
  | top =>
    cases j with
    | top => exact GroundChronologicalMainTransition.identity_coversOldBirths pairing unions powers separation target
    | coe j => exact False.elim (WithTop.not_top_le_coe j before)
  | coe i =>
    cases j with
    | top => exact legs i
    | coe j => exact old (WithTop.coe_le_coe.mp before)

end Cone

theorem coneOfLast_coverage (last : I) (greatest : ∀ i, i ≤ last)
    {target : GroundChronologicalMainStage M C D rD}
    (step : GroundChronologicalMainTransition (diagram.stage last) target)
    (old : diagram.CoversOldBirths) (covered : step.CoversOldBirths) :
    (diagram.coneOfLast last greatest step).append.CoversOldBirths :=
  Cone.append_coverage _ old (fun i => (old (greatest i)).comp pairing unions powers separation covered)

end PartitionPilot.Forcing.GroundChronologicalMainDiagram

end

end OAI
