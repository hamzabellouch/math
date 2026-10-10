import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.AnalyticKHomology
import Mathlib.Tactic.NoncommRing

namespace OAI

/-! # Compact changes of a Fredholm operator

The straight-line path between operators differing by a compact operator
preserves all three Fredholm defects. This is the normalization step used
when discharging the odd coefficient and circle-index inputs.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem compact_mul_right {K : End H} (hK : IsCompactOperator K) (T : End H) :
    IsCompactOperator (K * T) := hK.comp_clm T

theorem compact_mul_left {K : End H} (hK : IsCompactOperator K) (T : End H) :
    IsCompactOperator (T * K) := hK.clm_comp T

variable {A : Type} [NonUnitalCStarAlgebra A]

theorem compact_star_real_smul {K : End H} (hKs : IsCompactOperator (star K : End H)) (t : ℝ) :
    IsCompactOperator (star (t • K) : End H) := by
  rw [star_smul, star_trivial]
  exact hKs.smul t

def OddCycle.compactPerturbHomotopy (c : OddCycle A) (K : End c.space)
    (hK : IsCompactOperator K) (hKs : IsCompactOperator (star K : End c.space)) : OddHomotopy A where
  space := c.space
  representation _ := c.representation
  operator t := c.operator + (t : ℝ) • K
  continuous_representation _ := continuous_const
  continuous_operator := continuous_const.add (continuous_subtype_val.smul continuous_const)
  commutator_compact t a :=
    (c.compactPerturb ((t : ℝ) • K) (hK.smul _) (compact_star_real_smul hKs _)).commutator_compact a
  square_compact t a :=
    (c.compactPerturb ((t : ℝ) • K) (hK.smul _) (compact_star_real_smul hKs _)).square_compact a
  adjoint_compact t a :=
    (c.compactPerturb ((t : ℝ) • K) (hK.smul _) (compact_star_real_smul hKs _)).adjoint_compact a

theorem OddCycle.compactPerturbHomotopy_start (c : OddCycle A) (K : End c.space)
    (hK : IsCompactOperator K) (hKs : IsCompactOperator (star K : End c.space)) :
    (c.compactPerturbHomotopy K hK hKs).eval start = c := by
  cases c
  simp only [compactPerturbHomotopy, OddHomotopy.eval, start, zero_smul, add_zero]

theorem OddCycle.compactPerturbHomotopy_finish (c : OddCycle A) (K : End c.space)
    (hK : IsCompactOperator K) (hKs : IsCompactOperator (star K : End c.space)) :
    (c.compactPerturbHomotopy K hK hKs).eval finish = c.compactPerturb K hK hKs := by
  simp only [compactPerturbHomotopy, OddHomotopy.eval, finish, compactPerturb, one_smul]

theorem compactPerturb_class (c : OddCycle A) (K : End c.space)
    (hK : IsCompactOperator K) (hKs : IsCompactOperator (star K : End c.space)) :
    cycleClass A (c.compactPerturb K hK hKs) = cycleClass A c := by
  have hh := homotopy_eq (c.compactPerturbHomotopy K hK hKs)
  rw [c.compactPerturbHomotopy_start, c.compactPerturbHomotopy_finish] at hh
  exact hh.symm

end CoarseAssembly.Analytic

end

end OAI
