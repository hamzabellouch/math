import OAI.SetTheory.PartitionPrinciple.Definability.InitialMainAlgebraCodes

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula InitialMainAlgebra
universe u
variable (M : TransitiveGround.{u})

theorem initialMainAlgebra_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0) :
    carrier ∈ M.sets ∧ actors ∈ M.sets ∧ order ∈ M.sets ∧ meetGraph ∈ M.sets ∧
      multiplication ∈ M.sets ∧ inverse ∈ M.sets ∧ action ∈ M.sets := by
  have h0 := M.natSetCode_mem separation infinite 0
  have h1 := M.natSetCode_mem separation infinite 1
  have h2 := M.natSetCode_mem separation infinite 2
  have p00 := M.orderedPair_mem pairing h0 h0
  have p01 := M.orderedPair_mem pairing h0 h1
  have p10 := M.orderedPair_mem pairing h1 h0
  have p11 := M.orderedPair_mem pairing h1 h1
  have m000 := M.orderedPair_mem pairing p00 h0
  have m010 := M.orderedPair_mem pairing p01 h0
  have m100 := M.orderedPair_mem pairing p10 h0
  have m111 := M.orderedPair_mem pairing p11 h1
  have a011 := M.orderedPair_mem pairing p01 h1
  refine ⟨h2, h1, ?_, ?_, ?_, ?_, ?_⟩
  · exact M.insert_mem pairing unions p00 (M.unorderedPair_mem pairing p01 p11)
  · exact M.insert_mem pairing unions m000
      (M.insert_mem pairing unions m010 (M.unorderedPair_mem pairing m100 m111))
  · simpa only [multiplication, identity, bottom, ZFSet.pair_eq_singleton] using
      M.unorderedPair_mem pairing m000 m000
  · simpa only [inverse, identity, bottom, ZFSet.pair_eq_singleton] using
      M.unorderedPair_mem pairing p00 p00
  · exact M.unorderedPair_mem pairing m000 a011

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
