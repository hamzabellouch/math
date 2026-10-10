import OAI.SetTheory.PartitionPrinciple.Definability.GroundBelowFunctionGraphs

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def groundBelowMembers (R K : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun A => GroundBelow M A K) R

theorem mem_groundBelowMembers (R K A : ZFSet.{u}) :
    A ∈ M.groundBelowMembers R K ↔ A ∈ R ∧ GroundBelow M A K := by
  rw [groundBelowMembers, ZFSet.mem_sep]

theorem groundBelowMembers_mem (separation : SeparationSchema M.sets)
    {R K : ZFSet.{u}} (hR : R ∈ M.sets) (hK : K ∈ M.sets) :
    M.groundBelowMembers R K ∈ M.sets := by
  let params := extend K Fin.elim0
  have selected := M.separation_mem separation (groundBelowFormula 0 1) params
    (Fin.cases hK (fun i => Fin.elim0 i)) hR
  have equal : ZFSet.sep (fun A => Realize M.sets (groundBelowFormula 0 1)
      (extend A params)) R = M.groundBelowMembers R K := by
    apply ZFSet.ext
    intro A
    rw [ZFSet.mem_sep, M.mem_groundBelowMembers]
    apply and_congr_right
    intro hA
    exact M.realize_groundBelowFormula 0 1 _
      (Fin.cases (M.transitive hR hA) (Fin.cases hK (fun i => Fin.elim0 i)))
  exact equal ▸ selected

noncomputable def groundBelowSubsets (B K : ZFSet.{u}) : ZFSet.{u} :=
  M.groundBelowMembers (M.groundPower B) K

theorem mem_groundBelowSubsets (B K A : ZFSet.{u}) :
    A ∈ M.groundBelowSubsets B K ↔ A ∈ M.sets ∧ A ⊆ B ∧ GroundBelow M A K := by
  rw [groundBelowSubsets, M.mem_groundBelowMembers, M.mem_groundPower]
  exact and_assoc

theorem groundBelowSubsets_mem (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) {B K : ZFSet.{u}}
    (hB : B ∈ M.sets) (hK : K ∈ M.sets) : M.groundBelowSubsets B K ∈ M.sets :=
  M.groundBelowMembers_mem separation (M.groundPower_mem powers hB) hK

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
