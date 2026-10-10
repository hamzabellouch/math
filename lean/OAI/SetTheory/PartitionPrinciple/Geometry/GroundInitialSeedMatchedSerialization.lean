import OAI.SetTheory.PartitionPrinciple.Transfinite.CodedMainPrefixSystems

namespace OAI

section

namespace PartitionPilot.Forcing.GroundInitialMainSeedData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K C : ZFSet.{u}}
variable (seed : GroundInitialMainSeedData M K C)

theorem exists_matchedInitialSerialization
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K) :
    ∃ serial : GroundSerializedChronology M (insert seed.source.cutoff seed.source.cutoff)
        C (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode),
      serial.code ∈ M.sets ∧ ZFSet.rank serial.code < ZFSet.rank K ∧
        ∀ j t, t ∈ insert seed.source.cutoff seed.source.cutoff →
          serial.fields.value j t = seed.source.history.fieldValue j t := by
  obtain ⟨injection, _, injected, hInjection, ground, rank, _⟩ :=
    seed.exists_rankedInitialSerialization pairing unions powers separation infinite hK conditions
  let original := seed.source.stage.initialSerializedChronology pairing unions powers separation hInjection injected
  have timeEq : (insert (∅ : ZFSet.{u}) ∅ : ZFSet.{u}) = insert seed.source.cutoff seed.source.cutoff :=
    congrArg (fun t => insert t t) seed.cutoff_zero.symm
  let serial := original.castTime timeEq
  refine ⟨serial, ?_, ?_, ?_⟩
  · exact (original.castTime_code timeEq).symm ▸ ground
  · exact (congrArg ZFSet.rank (original.castTime_code timeEq)).symm ▸ rank
  · intro j t ht
    have zeroDomain : t ∈ (insert (∅ : ZFSet.{u}) ∅ : ZFSet.{u}) := timeEq.symm ▸ ht
    exact (original.castTime_value timeEq j t).trans
      (seed.initialSerialization_agreement pairing unions powers separation hInjection injected j t zeroDomain)

end PartitionPilot.Forcing.GroundInitialMainSeedData

end

end OAI
