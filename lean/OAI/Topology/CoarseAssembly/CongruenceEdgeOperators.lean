import OAI.Topology.CoarseAssembly.CongruenceSurjective
import OAI.Topology.CoarseAssembly.FiniteFiberMaps

namespace OAI

/-! # The concrete one-step congruence-fiber operators

The normalized child map is now instantiated with the proved surjective
congruence reduction. Its adjoint and the equal-depth permutations preserve
constants and have coefficients supported precisely on the prescribed
right-holonomy edge relation.
-/

noncomputable section

namespace CoarseAssembly.Congruence

def childIsometry (t : ℤ_[2]ˣ) (k : ℕ) (a : ℤ) :
    lp (fun _ : Quotient k => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : Quotient (k + 1) => ℂ) 2 := by
  classical
  exact twistedQuotientCopy (quotientMap (Nat.le_succ k))
    (quotientMap_successor_surjective k) (holonomy t k ^ a)

theorem childIsometry_constant (t : ℤ_[2]ˣ) (k : ℕ) (a : ℤ) :
    childIsometry t k a (fiberConstant (Quotient k) (1 : ℂ)) =
      fiberConstant (Quotient (k + 1)) 1 := by
  classical
  exact twistedQuotientCopy_constant _ _ _

theorem childAdjoint_constant (t : ℤ_[2]ˣ) (k : ℕ) (a : ℤ) :
    (childIsometry t k a).toContinuousLinearMap.adjoint
        (fiberConstant (Quotient (k + 1)) (1 : ℂ)) =
      fiberConstant (Quotient k) 1 := by
  rw [← childIsometry_constant t k a, adjoint_apply_isometry]

theorem childIsometry_support (t : ℤ_[2]ˣ) (k : ℕ) (a : ℤ)
    (q : Quotient k) (z : Quotient (k + 1))
    (hne : quotientMap (Nat.le_succ k) z ≠ q * holonomy t k ^ a) :
    childIsometry t k a (lp.single 2 q (1 : ℂ)) z = 0 := by
  classical
  let f := quotientMap (Nat.le_succ k)
  change twistedQuotientCopy f (quotientMap_successor_surjective k) (holonomy t k ^ a)
    (lp.single 2 q 1) z = 0
  rw [twistedQuotientCopy_apply]
  have harg : f z * (holonomy t k ^ a)⁻¹ ≠ q := by
    intro he
    apply hne
    calc
      f z = (f z * (holonomy t k ^ a)⁻¹) * holonomy t k ^ a := by group
      _ = q * holonomy t k ^ a := by rw [he]
  rw [lp.single_apply_ne 2 q 1 harg, mul_zero]

theorem childAdjoint_support (t : ℤ_[2]ˣ) (k : ℕ) (a : ℤ)
    (q : Quotient k) (z : Quotient (k + 1))
    (hne : quotientMap (Nat.le_succ k) z ≠ q * holonomy t k ^ a) :
    (childIsometry t k a).toContinuousLinearMap.adjoint (lp.single 2 z (1 : ℂ)) q = 0 := by
  have he := ContinuousLinearMap.adjoint_inner_right
    (childIsometry t k a).toContinuousLinearMap (lp.single 2 q 1) (lp.single 2 z 1)
  simp only [lp.inner_single_left, lp.inner_single_right] at he
  change inner ℂ (1 : ℂ) (_) = inner ℂ (childIsometry t k a (lp.single 2 q 1) z) 1 at he
  rw [childIsometry_support t k a q z hne] at he
  simpa only [RCLike.inner_apply, map_one, map_zero, mul_one, mul_zero, inner_zero_left] using he

def sameLevelIsometry (t : ℤ_[2]ˣ) (k : ℕ) (a : ℤ) :
    lp (fun _ : Quotient k => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : Quotient k => ℂ) 2 :=
  reindexFiber (Equiv.mulRight (holonomy t k ^ a))

theorem sameLevelIsometry_constant (t : ℤ_[2]ˣ) (k : ℕ) (a : ℤ) :
    sameLevelIsometry t k a (fiberConstant (Quotient k) (1 : ℂ)) =
      fiberConstant (Quotient k) 1 := reindexFiber_constant _ _

theorem sameLevelIsometry_support (t : ℤ_[2]ˣ) (k : ℕ) (a : ℤ)
    (q z : Quotient k) (hne : z ≠ q * holonomy t k ^ a) :
    sameLevelIsometry t k a (lp.single 2 q (1 : ℂ)) z = 0 := by
  change (lp.single (E := fun _ : Quotient k => ℂ) 2 q 1)
    (z * (holonomy t k ^ a)⁻¹) = 0
  apply lp.single_apply_ne
  intro he
  apply hne
  calc
    z = (z * (holonomy t k ^ a)⁻¹) * holonomy t k ^ a := by group
    _ = q * holonomy t k ^ a := by rw [he]

end CoarseAssembly.Congruence

end

end OAI
