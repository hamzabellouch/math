import OAI.SetTheory.PartitionPrinciple.Forcing.GeneratedMeetFilters
import OAI.SetTheory.PartitionPrinciple.Forcing.SmallCodedMeetActions
import OAI.SetTheory.PartitionPrinciple.Geometry.TileStarIncomingCodes

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

noncomputable def meetGeneratorSteps (P μ A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ P, ∃ y ∈ P, ∃ a ∈ A,
    z = ZFSet.pair x y ∧ ZFSet.pair (ZFSet.pair x a) y ∈ μ) (ZFSet.prod P P)

theorem pair_mem_meetGeneratorSteps (P μ A x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ meetGeneratorSteps P μ A ↔
      x ∈ P ∧ y ∈ P ∧ ∃ a ∈ A, ZFSet.pair (ZFSet.pair x a) y ∈ μ := by
  rw [meetGeneratorSteps, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, x', hx, y', hy, a, ha, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx, hy, a, ha, entry⟩
  · rintro ⟨hx, hy, a, ha, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, x, hx, y, hy, a, ha, rfl, entry⟩

namespace BoundedFormula

def meetGeneratorStepFormula {n} (z P μ A : Fin n) : BoundedFormula n :=
  .exMem P (.exMem P.succ (.exMem A.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 2 1)
      (tripleMembershipFormula 2 0 1 μ.succ.succ.succ))))

theorem truth_meetGeneratorStepFormula {n} (z P μ A : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (meetGeneratorStepFormula z P μ A) env ↔
      ∃ x ∈ env P, ∃ y ∈ env P, ∃ a ∈ env A,
        env z = ZFSet.pair x y ∧ ZFSet.pair (ZFSet.pair x a) y ∈ env μ := by
  simp only [meetGeneratorStepFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_tripleMembershipFormula]
  rfl

end BoundedFormula

theorem TransitiveGround.meetGeneratorSteps_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P μ A : ZFSet.{u}} (hP : P ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) :
    meetGeneratorSteps P μ A ∈ M.sets := by
  let params := extend P (extend μ (extend A Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.meetGeneratorStepFormula 0 1 2 3) params
    (Fin.cases hP (Fin.cases hμ (Fin.cases hA (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hP hP)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.meetGeneratorStepFormula 0 1 2 3) (extend z params))
      (ZFSet.prod P P) = meetGeneratorSteps P μ A := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, meetGeneratorSteps, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_meetGeneratorStepFormula _ _ _ _ _)
  exact equal ▸ selected

theorem MeetOrderCode.meetGeneratorSteps_iff {P r μ A : ZFSet.{u}}
    (code : MeetOrderCode P r μ) (subset : A ⊆ P) (x y : SetMembers P) :
    ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ meetGeneratorSteps P μ A ↔
      meetGeneratorStep code.toSmallMeetOrder (fun a => SetMembers.raw a ∈ A) x y := by
  rw [pair_mem_meetGeneratorSteps]
  constructor
  · rintro ⟨_, _, a, ha, entry⟩
    refine ⟨SetMembers.ofMem a (subset ha), ?_, ?_⟩
    · simpa only [SetMembers.raw_ofMem] using ha
    · apply Eq.symm
      apply (code.toSmallMeetOrder_meet_eq_iff _ _ _).2
      simpa only [SetMembers.raw_ofMem] using entry
  · rintro ⟨a, ha, equal⟩
    exact ⟨SetMembers.raw_mem x, SetMembers.raw_mem y, SetMembers.raw a, ha,
      (code.toSmallMeetOrder_meet_eq_iff _ _ _).1 equal.symm⟩

end PartitionPilot.Forcing

end

end OAI
