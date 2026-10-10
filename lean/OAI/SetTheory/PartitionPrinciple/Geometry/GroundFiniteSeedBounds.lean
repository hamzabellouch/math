import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundHistoryUnionBounds

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem natSetCode_identity_injection_omega (n : Nat) :
    InjectionCode (natSetCode n) ZFSet.omega (identityFunctionGraph (natSetCode n) : ZFSet.{u}) := by
  apply (identityFunctionGraph_injection (natSetCode n)).retarget
  intro x hx
  obtain ⟨k, _, rfl⟩ := (mem_natSetCode x n).1 hx
  exact natSetCode_mem_omega k

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem natSetCode_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (n : Nat) :
    M.groundEmbeddable (natSetCode n) ZFSet.omega :=
  ⟨identityFunctionGraph (natSetCode n),
    M.identityFunctionGraph_mem pairing unions powers separation
      (M.natSetCode_mem separation infinite n), natSetCode_identity_injection_omega n⟩

end TransitiveGround

namespace GroundInaccessibleConditions
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}

theorem finite_seed_bounds (conditions : GroundInaccessibleConditions M K)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (hK : K ∈ M.sets) (n : Nat) :
    natSetCode n ∈ M.sets ∧ M.groundEmbeddable (natSetCode n) ZFSet.omega ∧
      GroundBelow M (natSetCode n) K ∧ ZFSet.rank (natSetCode n) < ZFSet.rank K := by
  have bounds := conditions.natural pairing unions powers separation infinite hK n
  exact ⟨bounds.1, M.natSetCode_countable pairing unions powers separation infinite n,
    bounds.2, rank_natSetCode_lt
      (conditions.rank_isLimit pairing unions powers separation infinite hK) n⟩

end GroundInaccessibleConditions

end PartitionPilot.Forcing

end

end OAI
