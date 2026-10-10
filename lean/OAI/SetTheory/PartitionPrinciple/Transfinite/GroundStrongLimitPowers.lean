import OAI.SetTheory.PartitionPrinciple.Definability.GroundBelowFunctionGraphs
import OAI.SetTheory.PartitionPrinciple.Definability.GroundPowerImageGraphs

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

def GroundStrongLimit (M : TransitiveGround.{u}) (K : ZFSet.{u}) : Prop :=
  ∀ α ∈ K, GroundBelow M (M.groundPower α) K

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem groundEmbeddable_power
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (embedding : M.groundEmbeddable A B) :
    M.groundEmbeddable (M.groundPower A) (M.groundPower B) := by
  obtain ⟨f, hf, injection⟩ := embedding
  exact ⟨M.groundPowerImageGraph A B f,
    M.groundPowerImageGraph_mem pairing unions powers separation hA hB hf,
    M.groundPowerImageGraph_injection separation hB hf injection⟩

end TransitiveGround

namespace GroundStrongLimit
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}} (strong : GroundStrongLimit M K)

include strong in
theorem power_closed
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) (hK : K ∈ M.sets) (small : GroundBelow M A K) :
    GroundBelow M (M.groundPower A) K := by
  obtain ⟨α, hα, embedding⟩ := small
  have hAlpha := M.transitive hK hα
  exact (strong α hα).of_embeddable pairing unions powers separation
    (M.groundPower_mem powers hA) (M.groundPower_mem powers hAlpha) hK
    (M.groundEmbeddable_power pairing unions powers separation hA hAlpha embedding)

end GroundStrongLimit
end PartitionPilot.Forcing

end

end OAI
