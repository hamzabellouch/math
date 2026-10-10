import OAI.Topology.CoarseAssembly.UnitalCycleNormalization
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace OAI

/-! # Finite-dimensional kernels from the compact square defect

The kernel of `F` lies in the `-1` eigenspace of the compact operator
`F² - 1`. This supplies the finite-dimensional obstruction needed before
replacing a unital odd Fredholm operator by an invertible one.
-/

noncomputable section

namespace CoarseAssembly.Analytic

theorem finiteDimensional_ker_of_compact_square {H : HilbertSpace} (F : End H)
    (hF : IsCompactOperator (F * F - 1 : End H)) :
    FiniteDimensional ℂ F.ker := by
  let K : End H := F * F - 1
  let V : Submodule ℂ H := Module.End.eigenspace K.toLinearMap (-1)
  have hV : FiniteDimensional ℂ V :=
    ContinuousLinearMap.finite_dimensional_eigenspace hF (-1) (by norm_num)
  have hi : F.ker ≤ V := by
    intro x hx
    have hx' : F x = 0 := hx
    change x ∈ Module.End.eigenspace K.toLinearMap (-1)
    rw [Module.End.mem_eigenspace_iff]
    simp [K, hx']
  let := hV
  exact FiniteDimensional.of_injective (Submodule.inclusion hi)
    (Submodule.inclusion_injective hi)

theorem OddCycle.finiteDimensional_ker {A : Type} [CStarAlgebra A]
    (c : OddCycle A) (hunital : c.representation 1 = 1) :
    FiniteDimensional ℂ c.operator.ker := by
  apply finiteDimensional_ker_of_compact_square
  simpa only [hunital, mul_one] using c.square_compact 1

end CoarseAssembly.Analytic

end

end OAI
