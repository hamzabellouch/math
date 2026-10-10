import OAI.SetTheory.PartitionPrinciple.Forcing.GroundProductSizeWitnesses

namespace OAI

section

namespace PartitionPilot.Forcing.GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {A B K : ZFSet.{u}}

theorem product
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (first : GroundBelow M A K) (second : GroundBelow M B K) :
    GroundBelow M (ZFSet.prod A B) K := by
  obtain ⟨γ, hγ, first, second⟩ := first.common_bound second ordinal
  have hγM := M.transitive hK hγ
  have squareGround := M.prod_mem pairing unions powers separation hγM hγM
  have powerGround := M.groundPower_mem powers hγM
  have twice := strong.power_closed pairing unions powers separation powerGround hK (strong γ hγ)
  have square := twice.restrict separation squareGround hK (M.square_subset_groundPower_twice pairing hγM)
  exact square.of_embeddable pairing unions powers separation
    (M.prod_mem pairing unions powers separation hA hB) squareGround hK
    (M.groundEmbeddable_product_targets pairing unions powers separation hA hB hγM hγM first second)

end PartitionPilot.Forcing.GroundBelow



namespace PartitionPilot.Forcing.GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {A B K : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

include pairing unions powers separation

theorem relations (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (first : GroundBelow M A K) (second : GroundBelow M B K) :
    GroundBelow M (M.groundRelations A B) K :=
  strong.power_closed pairing unions powers separation
    (M.prod_mem pairing unions powers separation hA hB) hK
    (product pairing unions powers separation hA hB hK ordinal strong first second)

theorem partialFunctions (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (first : GroundBelow M A K) (second : GroundBelow M B K) :
    GroundBelow M (M.partialFunctions A B) K :=
  (relations pairing unions powers separation hA hB hK ordinal strong first second).restrict
    separation (M.partialFunctions_mem pairing unions powers separation hA hB) hK
    (fun _ member => (ZFSet.mem_sep.1 member).1)

end PartitionPilot.Forcing.GroundBelow

end

end OAI
