import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.CycleCompactPerturbation

namespace OAI

/-! # Locally compact changes of Fredholm operators

This also permits changing an operator on the subspace where its
representation vanishes. Compactness is required only after multiplying
by a represented coefficient.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [NonUnitalCStarAlgebra A]

theorem compact_local_smul_right (c : OddCycle A) (K : End c.space)
    (hr : ∀ a, IsCompactOperator (K * c.representation a : End c.space)) (t : ℝ) (a : A) :
    IsCompactOperator ((t • K) * c.representation a : End c.space) := by
  rw [smul_mul_assoc]
  exact (hr a).smul t

theorem compact_local_smul_left (c : OddCycle A) (K : End c.space)
    (hl : ∀ a, IsCompactOperator (c.representation a * K : End c.space)) (t : ℝ) (a : A) :
    IsCompactOperator (c.representation a * (t • K) : End c.space) := by
  rw [mul_smul_comm]
  exact (hl a).smul t

theorem compact_local_smul_star (c : OddCycle A) (K : End c.space)
    (hs : ∀ a, IsCompactOperator (star K * c.representation a : End c.space)) (t : ℝ) (a : A) :
    IsCompactOperator (star (t • K) * c.representation a : End c.space) := by
  rw [star_smul, star_trivial, smul_mul_assoc]
  exact (hs a).smul t

def OddCycle.localCompactHomotopy (c : OddCycle A) (K : End c.space)
    (hr : ∀ a, IsCompactOperator (K * c.representation a : End c.space))
    (hl : ∀ a, IsCompactOperator (c.representation a * K : End c.space))
    (hs : ∀ a, IsCompactOperator (star K * c.representation a : End c.space)) : OddHomotopy A where
  space := c.space
  representation _ := c.representation
  operator t := c.operator + (t : ℝ) • K
  continuous_representation _ := continuous_const
  continuous_operator := continuous_const.add (continuous_subtype_val.smul continuous_const)
  commutator_compact t :=
    (c.localCompactPerturb _ (compact_local_smul_right c K hr t)
      (compact_local_smul_left c K hl t) (compact_local_smul_star c K hs t)).commutator_compact
  square_compact t :=
    (c.localCompactPerturb _ (compact_local_smul_right c K hr t)
      (compact_local_smul_left c K hl t) (compact_local_smul_star c K hs t)).square_compact
  adjoint_compact t :=
    (c.localCompactPerturb _ (compact_local_smul_right c K hr t)
      (compact_local_smul_left c K hl t) (compact_local_smul_star c K hs t)).adjoint_compact

theorem localCompactPerturb_class (c : OddCycle A) (K : End c.space)
    (hr : ∀ a, IsCompactOperator (K * c.representation a : End c.space))
    (hl : ∀ a, IsCompactOperator (c.representation a * K : End c.space))
    (hs : ∀ a, IsCompactOperator (star K * c.representation a : End c.space)) :
    cycleClass A (c.localCompactPerturb K hr hl hs) = cycleClass A c := by
  have hstart : (c.localCompactHomotopy K hr hl hs).eval start = c := by
    cases c
    simp only [OddCycle.localCompactHomotopy, OddHomotopy.eval, start, zero_smul, add_zero]
  have hfinish : (c.localCompactHomotopy K hr hl hs).eval finish =
      c.localCompactPerturb K hr hl hs := by
    simp only [OddCycle.localCompactHomotopy, OddHomotopy.eval, finish,
      OddCycle.localCompactPerturb, one_smul]
  have hh := homotopy_eq (c.localCompactHomotopy K hr hl hs)
  rw [hstart, hfinish] at hh
  exact hh.symm

end CoarseAssembly.Analytic

end

end OAI
