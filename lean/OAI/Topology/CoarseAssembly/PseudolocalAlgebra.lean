import OAI.Topology.CoarseAssembly.LocallyCompactAlgebra
import Mathlib.Tactic.NoncommRing

namespace OAI

/-! # Pseudolocal operators and the controlled structure algebra -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open scoped ZeroAtInfty CStarAlgebra

variable {X H : Type*} [DecidableEq X] [TopologicalSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance : IsScalarTower ℂ (Operator X H) (Operator X H) where
  smul_assoc c T S := by ext v; simp
local instance : SMulCommClass ℂ (Operator X H) (Operator X H) where
  smul_comm c T S := by ext v; simp

def Pseudolocal (T : Operator X H) : Prop :=
  ∀ f : C₀(X, ℂ), IsCompactOperator (T * diagonalMultiplier (H := H) f -
    diagonalMultiplier (H := H) f * T)

omit [DecidableEq X] [CompleteSpace H] in
theorem LocallyCompact.pseudolocal {T : Operator X H} (hT : LocallyCompact T) :
    Pseudolocal T := fun f => (hT f).2.sub (hT f).1

omit [DecidableEq X] [CompleteSpace H] in
theorem Pseudolocal.add {T S : Operator X H} (hT : Pseudolocal T) (hS : Pseudolocal S) :
    Pseudolocal (T + S) := by
  intro f
  have he : (T + S) * diagonalMultiplier (H := H) f - diagonalMultiplier (H := H) f * (T + S) =
      (T * diagonalMultiplier (H := H) f - diagonalMultiplier (H := H) f * T) +
      (S * diagonalMultiplier (H := H) f - diagonalMultiplier (H := H) f * S) := by
    simp only [add_mul, mul_add]
    abel
  rw [he]
  exact (hT f).add (hS f)

omit [DecidableEq X] [CompleteSpace H] in
theorem Pseudolocal.mul {T S : Operator X H} (hT : Pseudolocal T) (hS : Pseudolocal S) :
    Pseudolocal (T * S) := by
  intro f
  have he : (T * S) * diagonalMultiplier (H := H) f - diagonalMultiplier (H := H) f * (T * S) =
      T * (S * diagonalMultiplier (H := H) f - diagonalMultiplier (H := H) f * S) +
      (T * diagonalMultiplier (H := H) f - diagonalMultiplier (H := H) f * T) * S := by
    simp only [mul_sub, sub_mul, mul_assoc]
    abel
  rw [he]
  exact ((hS f).clm_comp T).add ((hT f).comp_clm S)

omit [DecidableEq X] [CompleteSpace H] in
theorem Pseudolocal.smul {T : Operator X H} (hT : Pseudolocal T) (z : ℂ) :
    Pseudolocal (z • T) := by
  intro f
  have he : (z • T) * diagonalMultiplier (H := H) f -
      diagonalMultiplier (H := H) f * (z • T) =
      z • (T * diagonalMultiplier (H := H) f - diagonalMultiplier (H := H) f * T) := by
    apply ContinuousLinearMap.ext
    intro v
    simp [map_smul, smul_sub]
  rw [he]
  exact (hT f).smul z

omit [DecidableEq X] in
theorem pseudolocal_closed : IsClosed {T : Operator X H | Pseudolocal T} := by
  simp only [Pseudolocal, Set.ofPred_forall]
  apply isClosed_iInter
  intro f
  exact isClosed_setOfPred_isCompactOperator.preimage
    ((continuous_id.mul continuous_const).sub (continuous_const.mul continuous_id))

def pseudolocalAlgebra : StarSubalgebra ℂ (Operator X H) where
  carrier := {T | Pseudolocal T ∧ Pseudolocal (star T)}
  zero_mem' := by
    change Pseudolocal (0 : Operator X H) ∧ Pseudolocal (star (0 : Operator X H))
    rw [star_zero (Operator X H)]
    constructor <;> intro f <;> simp only [zero_mul, mul_zero, sub_self]
    all_goals exact isCompactOperator_zero
  one_mem' := by
    change Pseudolocal (1 : Operator X H) ∧ Pseudolocal (star (1 : Operator X H))
    rw [star_one (Operator X H)]
    constructor <;> intro f <;> simp only [one_mul, mul_one, sub_self]
    all_goals exact isCompactOperator_zero
  add_mem' hT hS := ⟨hT.1.add hS.1, by simpa only [star_add] using hT.2.add hS.2⟩
  mul_mem' hT hS := ⟨hT.1.mul hS.1, by simpa only [star_mul] using hS.2.mul hT.2⟩
  algebraMap_mem' z := by
    have hz (w : ℂ) : Pseudolocal (algebraMap ℂ (Operator X H) w) := by
      intro f
      rw [(Algebra.commutes w (diagonalMultiplier (H := H) f)), sub_self]
      exact isCompactOperator_zero
    refine ⟨hz z, ?_⟩
    have he : star (algebraMap ℂ (Operator X H) z) = algebraMap ℂ (Operator X H) (star z) := by
      simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one]
    rw [he]
    exact hz (star z)
  star_mem' hT := ⟨hT.2, by simpa only [star_star] using hT.1⟩

omit [DecidableEq X] in
theorem pseudolocalAlgebra_closed :
    IsClosed (pseudolocalAlgebra (X := X) (H := H) : Set (Operator X H)) :=
  pseudolocal_closed.inter (pseudolocal_closed.preimage operator_star_continuous)

variable [PseudoMetricSpace X]

def StructureGenerator (T : Operator X H) : Prop :=
  (∃ r : ℝ, 0 ≤ r ∧ PropagationLE r T) ∧ Pseudolocal T ∧ Pseudolocal (star T)

/-- The controlled pseudolocal algebra used to form the analytic-index quotient. -/
def structureAlgebra : NonUnitalStarSubalgebra ℂ (Operator X H) :=
  (NonUnitalStarAlgebra.adjoin ℂ {T : Operator X H | StructureGenerator T}).topologicalClosure

theorem structureAlgebra_pseudolocal {T : Operator X H}
    (hT : T ∈ structureAlgebra (X := X) (H := H)) : Pseudolocal T := by
  have hle : NonUnitalStarAlgebra.adjoin ℂ {S : Operator X H | StructureGenerator S} ≤
      (pseudolocalAlgebra (X := X) (H := H)).toNonUnitalStarSubalgebra :=
    NonUnitalStarAlgebra.adjoin_le (fun _ h => h.2)
  exact (NonUnitalStarSubalgebra.topologicalClosure_minimal _ hle pseudolocalAlgebra_closed hT).1

variable [DiscreteTopology X]

theorem roe_le_structureAlgebra
    (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite) :
    algebra (X := X) (H := H) ≤ structureAlgebra (X := X) (H := H) := by
  apply NonUnitalStarSubalgebra.topologicalClosure_mono
  apply NonUnitalStarAlgebra.adjoin_mono
  intro T hT
  refine ⟨hT.1, (generator_locallyCompact finiteBalls hT).pseudolocal, ?_⟩
  obtain ⟨⟨r, _, hp⟩, _, hc⟩ := hT
  exact (locallyCompact_of_propagation finiteBalls hp.star hc).pseudolocal

end CoarseAssembly.DiscreteRoe

end

end OAI
