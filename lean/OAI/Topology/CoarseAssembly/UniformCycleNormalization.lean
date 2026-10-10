import OAI.Topology.CoarseAssembly.SigmaCycle
import OAI.Topology.CoarseAssembly.RepresentedNormalization

namespace OAI

/-! # Uniformly bounded representatives for countable families -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped ZeroAtInfty

theorem involution_norm_le_one {H : HilbertSpace} (F : End H)
    (hself : IsSelfAdjoint F) (hsq : F * F = 1) : ‖F‖ ≤ 1 := by
  have he : ‖F‖ ^ 2 = ‖(1 : End H)‖ := by
    rw [← hself.norm_mul_self, hsq]
  have hi : ‖(1 : End H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg F]

variable {A : Type} [CStarAlgebra A]

def normalizedCycle (c : OddCycle A) : OddCycle A :=
  (exists_represented_involutive_representative c).choose

theorem normalizedCycle_class (c : OddCycle A) :
    cycleClass A (normalizedCycle c) = cycleClass A c :=
  (exists_represented_involutive_representative c).choose_spec.1

theorem normalizedCycle_selfAdjoint (c : OddCycle A) :
    IsSelfAdjoint (normalizedCycle c).operator :=
  (exists_represented_involutive_representative c).choose_spec.2.1

theorem normalizedCycle_sq (c : OddCycle A) :
    (normalizedCycle c).operator * (normalizedCycle c).operator = 1 :=
  (exists_represented_involutive_representative c).choose_spec.2.2.1

theorem normalizedCycle_norm (c : OddCycle A) : ‖(normalizedCycle c).operator‖ ≤ 1 :=
  involution_norm_le_one _ (normalizedCycle_selfAdjoint c) (normalizedCycle_sq c)

variable (Y : ℕ → Type) [∀ j, TopologicalSpace (Y j)] [∀ j, CompactSpace (Y j)]

/-- Actual locally finite cycle for an arbitrary countable family of compact-source cycles. -/
def normalizedFamilyCycle (c : ∀ j, OddCycle C(Y j, ℂ)) : OddCycle C₀(Sigma Y, ℂ) :=
  sigmaCycle Y (fun j => normalizedCycle (c j)) 1 (by norm_num)
    (fun j => normalizedCycle_norm (c j)) (fun j => normalizedCycle_selfAdjoint (c j))
    (fun j => normalizedCycle_sq (c j))

end CoarseAssembly.Analytic

end

end OAI
