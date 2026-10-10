import OAI.SetTheory.PartitionPrinciple.Geometry.CompressionExternalTileOverlaps
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundSerializedChronologyTimeEquality

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

structure GroundChronologicalCompression (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P0 C Q qlt original Targets Separators Filters base old T0 : ZFSet.{u})
    (prior : GroundChronologicalHistory M T0 C Q qlt) where
  born : GroundBornCompression M initial I Sources Reps G m one T τ P0 C Q qlt original
    Targets Separators Filters base old
  history : GroundChronologicalHistory M (insert born.births.limit born.births.limit) C Q qlt
  original_height : prior.height base = original
  old_values : ∀ s, s ∈ base ∨ s = base →
    history.space s = prior.space s ∧ history.order s = prior.order s ∧
      history.meetGraph s = prior.meetGraph s ∧ history.birth s = prior.birth s ∧
        history.height s = prior.height s
  stamp_values : ∀ n,
    history.space (compressionStamp base n) = (initial.iterate M I Sources Reps G T (n + 1)).D ∧
    history.order (compressionStamp base n) = (initial.iterate M I Sources Reps G T (n + 1)).rD ∧
    history.meetGraph (compressionStamp base n) = (initial.iterate M I Sources Reps G T (n + 1)).μD ∧
    history.birth (compressionStamp base n) =
      graphRestriction (initial.iterate M I Sources Reps G T (n + 1)).D born.births.birth ∧
    history.height (compressionStamp base n) = born.profiled.heighted.heights.function.natValue (n + 1)
  limit_values :
    history.space born.births.limit = born.profiled.heighted.completion.algebra.union.fields 0 ∧
    history.order born.births.limit = born.profiled.heighted.completion.algebra.union.fields 1 ∧
    history.meetGraph born.births.limit = born.profiled.heighted.completion.algebra.union.fields 2 ∧
    history.birth born.births.limit = born.births.birth ∧
    history.height born.births.limit = born.profiled.heighted.heights.height

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundChronologicalCompression
open SetFormula
universe u
variable {M N : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 C Q qlt original Targets Separators Filters base old T0 : ZFSet.{u}}
variable {prior : GroundChronologicalHistory M T0 C Q qlt}
variable (compression : GroundChronologicalCompression M initial I Sources Reps G m one T τ
  P0 C Q qlt original Targets Separators Filters base old T0 prior)

theorem exists_extension_basis
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (includes : M.sets ⊆ N.sets)
    (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize N.sets SetFormula.union Fin.elim0)
    (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
    (infiniteN : Realize N.sets SetFormula.infinity Fin.elim0)
    (choiceN : Realize N.sets SetFormula.choice Fin.elim0)
    (hC : C ∈ M.sets) (hQ : Q ∈ M.sets)
    (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    {F : ZFSet.{u}} (hF : F ∈ N.sets)
    (filter : MeetFilterCode (compression.born.profiled.heighted.completion.algebra.union.fields 0)
      (compression.born.profiled.heighted.completion.algebra.union.fields 1)
      (compression.born.profiled.heighted.completion.algebra.union.fields 2) F) :
    ∃ B ∈ N.sets, ∃ f ∈ N.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
      ∀ x ∈ F, ∃ b ∈ B,
        ZFSet.pair b x ∈ compression.born.profiled.heighted.completion.algebra.union.fields 1 := by
  have filterAtLimit : MeetFilterCode (compression.history.space compression.born.births.limit)
      (compression.history.order compression.born.births.limit)
      (compression.history.meetGraph compression.born.births.limit) F := by
    simpa only [compression.limit_values.1, compression.limit_values.2.1,
      compression.limit_values.2.2.1] using filter
  have basis := compression.history.exists_extension_basis includes pairingN unionsN powersN
    separationN infiniteN choiceN
    (M.insert_mem pairing unions compression.born.births.limit_ground compression.born.births.limit_ground)
    hC hQ (ordinalSetProperty_succ compression.born.births.times.ordinal) smallQ irreflexive
    (ZFSet.mem_insert compression.born.births.limit compression.born.births.limit) hF filterAtLimit
  simpa only [compression.limit_values.2.1] using basis

end PartitionPilot.Forcing.GroundChronologicalCompression

end

end OAI
