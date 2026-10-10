import OAI.Topology.CoarseAssembly.CycleCompactPerturbation
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

namespace OAI

/-! # Finite-dimensional odd cycles vanish

Every change of operator is compact on a finite-dimensional Hilbert space.
Changing the operator to the identity gives a degenerate odd cycle.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [NonUnitalCStarAlgebra A]

theorem finiteDimensional_cycleClass_zero (c : OddCycle A) [FiniteDimensional ℂ c.space] :
    cycleClass A c = 0 := by
  let K : End c.space := 1 - c.operator
  have hi : IsCompactOperator (id : c.space → c.space) :=
    (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℂ)).2 inferInstance
  have hK : IsCompactOperator K := hi.comp_clm K
  have hKs : IsCompactOperator (star K : End c.space) :=
    hi.comp_clm (star K : End c.space)
  let d := c.compactPerturb K hK hKs
  have hd : d.operator = 1 := by
    change c.operator + (1 - c.operator) = 1
    abel
  have hdeg : d.Degenerate := by
    constructor
    · intro a
      rw [hd]
      simp
    constructor
    · intro a
      rw [hd]
      simp
    · intro a
      rw [hd]
      simp
  exact (compactPerturb_class c K hK hKs).symm.trans (degenerate_zero d hdeg)

end CoarseAssembly.Analytic

end

end OAI
