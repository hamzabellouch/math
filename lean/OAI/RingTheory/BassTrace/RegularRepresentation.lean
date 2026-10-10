import Mathlib

namespace OAI

/-! The regular representation on square-summable functions. -/

open scoped Classical BigOperators ComplexInnerProductSpace
noncomputable section
namespace TorsionFreeBass.Regular

/-- Square-summable functions on the discrete group. -/
abbrev Hilbert (G : Type*) := lp (fun _ : G => ℂ) 2

/-- Permuting coordinates is unitary on ℓ², including for arbitrary index sets. -/
def permute {X : Type*} (s : Equiv.Perm X) : Hilbert X ≃ₗᵢ[ℂ] Hilbert X where
  toFun x := ⟨fun i => x (s.symm i), memℓp_gen <|
    (s.symm.summable_iff).mpr (x.2.summable (by norm_num))⟩
  invFun x := ⟨fun i => x (s i), memℓp_gen <|
    (s.summable_iff).mpr (x.2.summable (by norm_num))⟩
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_add' x y := by ext i; rfl
  map_smul' a x := by ext i; rfl
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact s.symm.tsum_eq (fun i => ‖x i‖ ^ (2 : ENNReal).toReal)

@[simp] lemma permute_apply {X : Type*} (s : Equiv.Perm X) (x : Hilbert X) (i : X) :
    permute s x i = x (s.symm i) := rfl

variable {G : Type*} [Group G]

def leftShift (g : G) : Hilbert G ≃ₗᵢ[ℂ] Hilbert G := permute (Equiv.mulLeft g)
def rightShift (g : G) : Hilbert G ≃ₗᵢ[ℂ] Hilbert G := permute (Equiv.mulRight g)

@[simp] lemma leftShift_apply (g : G) (x : Hilbert G) (h : G) :
    leftShift g x h = x (g⁻¹ * h) := rfl
@[simp] lemma rightShift_apply (g : G) (x : Hilbert G) (h : G) :
    rightShift g x h = x (h * g⁻¹) := rfl

lemma left_right_commute (g h : G) (x : Hilbert G) :
    leftShift g (rightShift h x) = rightShift h (leftShift g x) := by
  ext k
  simp [mul_assoc]

@[simp] lemma rightShift_inv (g : G) (x : Hilbert G) :
    rightShift g (rightShift g⁻¹ x) = x := by
  ext k
  simp [mul_assoc]

/-- The left regular representation by bounded operators. -/
def leftRegular : G →* (Hilbert G →L[ℂ] Hilbert G) where
  toFun g := (leftShift g).toContinuousLinearEquiv.toContinuousLinearMap
  map_one' := by ext x h; simp
  map_mul' g h := by ext x k; simp [mul_assoc]

@[simp] lemma leftRegular_apply (g : G) (x : Hilbert G) :
    leftRegular g x = leftShift g x := rfl

/-- Convolution is the algebra homomorphism extending the left regular representation. -/
def convolution : MonoidAlgebra ℂ G →ₐ[ℂ] (Hilbert G →L[ℂ] Hilbert G) :=
  MonoidAlgebra.lift ℂ _ G leftRegular

lemma convolution_apply (a : MonoidAlgebra ℂ G) (x : Hilbert G) :
    convolution a x = ∑ g ∈ a.coeff.support, a.coeff g • leftShift g x := by
  simp [convolution, MonoidAlgebra.lift_apply, Finsupp.sum]

lemma convolution_rightShift (a : MonoidAlgebra ℂ G) (g : G) (x : Hilbert G) :
    convolution a (rightShift g x) = rightShift g (convolution a x) := by
  simp only [convolution_apply, map_sum, map_smul, left_right_commute]

/-- The usual delta functions. -/
def delta (g : G) : Hilbert G := lp.single 2 g 1

omit [Group G] in
@[simp] lemma delta_apply (g h : G) : delta g h = if h = g then 1 else 0 := by
  simp [delta, lp.single_apply, Pi.single_apply]

@[simp] lemma leftShift_delta (g h : G) : leftShift g (delta h) = delta (g * h) := by
  ext k
  simp [inv_mul_eq_iff_eq_mul]

@[simp] lemma rightShift_delta (g h : G) : rightShift g (delta h) = delta (h * g) := by
  ext k
  simp [mul_inv_eq_iff_eq_mul]

lemma convolution_delta (a : MonoidAlgebra ℂ G) (g : G) :
    convolution a (delta 1) g = a.coeff g := by
  simp only [convolution_apply, leftShift_delta, mul_one, lp.coeFn_sum,
    Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, delta_apply,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hg
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hg).symm

omit [Group G] in
lemma inner_delta (g : G) (x : Hilbert G) : inner ℂ (delta g) x = x g := by
  simp [delta, lp.inner_single_left]

/-- Traciality against a finite convolution operator follows just from right invariance. -/
lemma trace_commute (a : MonoidAlgebra ℂ G) (T : Hilbert G →L[ℂ] Hilbert G)
    (hT : ∀ g x, T (rightShift g x) = rightShift g (T x)) :
    T (convolution a (delta 1)) 1 = convolution a (T (delta 1)) 1 := by
  simp only [convolution_apply, map_sum, map_smul, leftShift_delta, mul_one]
  have hh (g : G) : T (delta g) = rightShift g (T (delta 1)) := by
    simpa only [rightShift_delta, one_mul] using hT g (delta 1)
  change (∑ g ∈ a.coeff.support, a.coeff g • T (delta g)) 1 =
    (∑ g ∈ a.coeff.support, a.coeff g • leftShift g (T (delta 1))) 1
  have heq (g : G) : T (delta g) 1 = leftShift g (T (delta 1)) 1 := by
    rw [hh]
    simp only [rightShift_apply, leftShift_apply, one_mul, mul_one]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, heq]

end TorsionFreeBass.Regular
end


/-! Faithfulness of the coefficient trace on complex group-ring idempotents. -/

open scoped Classical BigOperators ComplexInnerProductSpace
noncomputable section
namespace TorsionFreeBass.Regular

variable {G : Type*} [Group G]

/-- A right-translation-invariant closed subspace has a right-invariant orthogonal projection. -/
lemma projection_rightShift (M : Submodule ℂ (Hilbert G)) [M.HasOrthogonalProjection]
    (hM : ∀ g x, x ∈ M → rightShift g x ∈ M) (g : G) (x : Hilbert G) :
    M.starProjection (rightShift g x) = rightShift g (M.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hM g _ (M.starProjection_apply_mem x)
  · intro w hw
    calc
      inner ℂ (rightShift g x - rightShift g (M.starProjection x)) w =
          inner ℂ (rightShift g (x - M.starProjection x))
            (rightShift g (rightShift g⁻¹ w)) := by rw [map_sub, rightShift_inv]
      _ = inner ℂ (x - M.starProjection x) (rightShift g⁻¹ w) :=
        (rightShift g).inner_map_map _ _
      _ = 0 := M.starProjection_inner_eq_zero x _ (hM _ _ hw)

/-- The coefficient trace detects zero idempotents in the complex group ring.
We project onto the closed range of left convolution. This projection has the
same coefficient trace as the idempotent, and its trace is faithful. -/
theorem idempotent_eq_zero_of_coeff_one_eq_zero (a : MonoidAlgebra ℂ G)
    (ha : a * a = a) (hzero : a.coeff 1 = 0) : a = 0 := by
  let E := convolution a
  have hEE (x : Hilbert G) : E (E x) = E x := by
    change (convolution a * convolution a) x = convolution a x
    rw [← map_mul, ha]
  let M : Submodule ℂ (Hilbert G) := (E - 1).ker
  have memM (x : Hilbert G) : x ∈ M ↔ E x = x := by
    change (E - 1) x = 0 ↔ _
    simp only [sub_apply, one_apply_eq_self, sub_eq_zero]
  have hEP (x : Hilbert G) : E (M.starProjection x) = M.starProjection x :=
    (memM _).mp (M.starProjection_apply_mem x)
  have hPE (x : Hilbert G) : M.starProjection (E x) = E x :=
    Submodule.starProjection_eq_self_iff.mpr ((memM _).mpr (hEE x))
  have hM (g : G) (x : Hilbert G) (hx : x ∈ M) : rightShift g x ∈ M := by
    apply (memM _).mpr
    change convolution a (rightShift g x) = rightShift g x
    rw [convolution_rightShift, (memM x).mp hx]
  have hPcomm := projection_rightShift M hM
  have ht : (M.starProjection (delta 1)) 1 = 0 := by
    have h := trace_commute a M.starProjection hPcomm
    change M.starProjection (E (delta 1)) 1 = E (M.starProjection (delta 1)) 1 at h
    rw [hPE, hEP] at h
    rw [← h]
    exact (convolution_delta a 1).trans hzero
  have hPδ : M.starProjection (delta 1) = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [M.inner_starProjection_left_eq_right]
    rw [Submodule.starProjection_eq_self_iff.mpr (M.starProjection_apply_mem _)]
    exact (inner_delta _ _).trans ht
  have hPδg (g : G) : M.starProjection (delta g) = 0 := by
    have h := hPcomm g (delta 1)
    rw [rightShift_delta, one_mul, hPδ, map_zero] at h
    exact h
  have hP (x : Hilbert G) : M.starProjection x = 0 := by
    ext g
    have h := M.inner_starProjection_left_eq_right (delta g) x
    rw [hPδg, inner_zero_left, inner_delta] at h
    exact h.symm
  have hEδ : E (delta 1) = 0 := (hPE _).symm.trans (hP _)
  ext g
  change a.coeff g = 0
  rw [← convolution_delta]
  change E (delta 1) g = 0
  rw [hEδ]
  rfl

end TorsionFreeBass.Regular
end

end OAI
