import OAI.Topology.CoarseAssembly.BlockOperators
import OAI.Topology.CoarseAssembly.RoeRows
import Mathlib.Analysis.CStarAlgebra.ContinuousMap

namespace OAI

/-! # The concrete multiplication representation on a discrete ample module -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open scoped ZeroAtInfty

variable {X H : Type*} [TopologicalSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem scalarBlock_norm_le (z : ℂ) : ‖z • (1 : H →L[ℂ] H)‖ ≤ ‖z‖ := by
  exact (norm_smul_le z (1 : H →L[ℂ] H)).trans
    (mul_le_of_le_one_right (norm_nonneg z) ContinuousLinearMap.norm_id_le)

def diagonalMultiplier (f : C₀(X, ℂ)) : Operator X H :=
  blockOperator (fun x => f x • (1 : H →L[ℂ] H)) ‖f‖ (norm_nonneg f)
    (fun x => (scalarBlock_norm_le (f x)).trans (f.toBCF.norm_coe_le_norm x))

@[simp] theorem diagonalMultiplier_apply (f : C₀(X, ℂ)) (v : Module X H) (x : X) :
    diagonalMultiplier f v x = f x • v x := rfl

theorem diagonalMultiplier_norm (f : C₀(X, ℂ)) :
    ‖diagonalMultiplier (H := H) f‖ ≤ ‖f‖ := blockOperator_norm_le _ _ _ _

theorem diagonalMultiplier_sub (f g : C₀(X, ℂ)) :
    diagonalMultiplier (H := H) (f - g) = diagonalMultiplier f - diagonalMultiplier g := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext x
  exact sub_smul _ _ _

variable [DecidableEq X]

def finiteDiagonal (f : X → ℂ) (s : Finset X) : Operator X H :=
  ∑ x ∈ s, f x • ((insert x).comp (coordinate x))

omit [TopologicalSpace X] in
@[simp] theorem finiteDiagonal_apply (f : X → ℂ) (s : Finset X)
    (v : Module X H) (x : X) :
    finiteDiagonal f s v x = if x ∈ s then f x • v x else 0 := by
  classical
  simp only [finiteDiagonal, sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, insert_apply, coordinate_apply,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, lp.single_apply]
  by_cases hx : x ∈ s
  · rw [Finset.sum_eq_single x]
    · simp [hx]
    · intro y _ hy
      simp [Pi.single_eq_of_ne (Ne.symm hy)]
    · exact fun h => (h hx).elim
  · rw [ite_eq_right hx]
    apply Finset.sum_eq_zero
    intro y hy
    have hxy : x ≠ y := fun h => hx (h ▸ hy)
    simp [Pi.single_eq_of_ne hxy]

end CoarseAssembly.DiscreteRoe

end

end OAI
