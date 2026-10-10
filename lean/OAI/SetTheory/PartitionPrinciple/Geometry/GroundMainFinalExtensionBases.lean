import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainFinalChronology

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalChronology
open SetFormula
universe u v
variable {M N : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K}
variable (chronology : run.FinalChronology level)
include chronology

theorem exists_extension_basis (i₀ : I)
    (includes : M.sets ⊆ N.sets)
    (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize N.sets SetFormula.union Fin.elim0)
    (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
    (infiniteN : Realize N.sets infinity Fin.elim0)
    (choiceN : Realize N.sets SetFormula.choice Fin.elim0)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    {F : ZFSet.{u}} (hF : F ∈ N.sets)
    (filter : MeetFilterCode (run.finalGeometry i₀).carrier (run.finalGeometry i₀).order
      (run.finalGeometry i₀).meetGraph F) :
    ∃ B ∈ N.sets, ∃ f ∈ N.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
      ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ (run.finalGeometry i₀).order := by
  have terminal := chronology.terminal_values i₀
  have atTerminal : MeetFilterCode (chronology.serial.toHistory.space run.cutoffLimit)
      (chronology.serial.toHistory.order run.cutoffLimit)
      (chronology.serial.toHistory.meetGraph run.cutoffLimit) F := by
    simpa only [terminal.1, terminal.2.1, terminal.2.2.1] using filter
  have basis := chronology.serial.toHistory.exists_extension_basis includes pairingN unionsN powersN
    separationN infiniteN choiceN
    (M.insert_mem pairing unions run.cutoffLimit_ground run.cutoffLimit_ground)
    (run.finalGeometry i₀).columns_ground (run.finalGeometry i₀).coordinates_ground
    chronology.serial.ordinal smallD irreflexive (ZFSet.mem_insert run.cutoffLimit run.cutoffLimit)
    hF atTerminal
  simpa only [terminal.2.1] using basis

end PartitionPilot.Forcing.GroundMainPrefix.FinalChronology

end

end OAI
