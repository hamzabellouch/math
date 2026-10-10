import OAI.RingTheory.BassTrace.ExteriorDetector

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Detector

open scoped BigOperators

lemma rawTwoForm_map {I J : Type*} [Fintype I] (f : I → J) (B : I → I → ℂ) :
    ExteriorAlgebra.map (coordinateMap f) (rawTwoForm B) =
      ∑ i, ∑ j, B i j • (ExteriorAlgebra.ι ℂ (coordinate (f i)) *
        ExteriorAlgebra.ι ℂ (coordinate (f j))) := by
  simp only [rawTwoForm, map_sum, map_smul, map_mul,
    ExteriorAlgebra.map_apply_ι, coordinateMap_coordinate]

lemma twoForm_row {n : ℕ} (B : Fin (n+1) → Fin (n+1) → ℂ)
    (hB : ∀ i j, B i j = -B j i) (i : Fin (n+1)) :
    twoForm B =
      ExteriorAlgebra.map (coordinateMap i.succAbove)
        (twoForm (fun k l => B (i.succAbove k) (i.succAbove l))) +
      ExteriorAlgebra.ι ℂ (coordinate i) * ExteriorAlgebra.ι ℂ (coordinateVector (B i)) := by
  let a (k l : Fin (n+1)) : CoordinateAlgebra (Fin (n+1)) :=
    B k l • (ExteriorAlgebra.ι ℂ (coordinate k) * ExteriorAlgebra.ι ℂ (coordinate l))
  have ha (k l) : a k l = a l k := by
    dsimp only [a]
    rw [hB k l, ι_mul_ι_neg (coordinate k) (coordinate l), neg_smul, smul_neg, neg_neg]
  have hai : a i i = 0 := by simp only [a, ExteriorAlgebra.ι_sq_zero, smul_zero]
  have hsum : (∑ k, ∑ l, a k l) =
      (∑ k : Fin n, ∑ l : Fin n, a (i.succAbove k) (i.succAbove l)) +
        (∑ l, a i l) + (∑ l, a i l) := by
    rw [Fin.sum_univ_succAbove (fun k => ∑ l, a k l) i]
    have he : (∑ k : Fin n, ∑ l, a (i.succAbove k) l) =
        (∑ k : Fin n, a (i.succAbove k) i) +
          ∑ k : Fin n, ∑ l : Fin n, a (i.succAbove k) (i.succAbove l) := by
      simp_rw [Fin.sum_univ_succAbove (fun l => a (i.succAbove _) l) i]
      rw [Finset.sum_add_distrib]
    rw [he]
    have hr : (∑ k : Fin n, a (i.succAbove k) i) = ∑ l, a i l := by
      conv_rhs => rw [Fin.sum_univ_succAbove (a i) i, hai, zero_add]
      exact Finset.sum_congr rfl fun k _ => ha _ _
    rw [hr]
    abel
  have hrow : (∑ l, a i l) =
      ExteriorAlgebra.ι ℂ (coordinate i) * ExteriorAlgebra.ι ℂ (coordinateVector (B i)) := by
    simp only [coordinateVector, map_sum, map_smul, Finset.mul_sum, mul_smul_comm, a]
  simp only [twoForm, map_smul, rawTwoForm_map]
  change (2 : ℂ)⁻¹ • (∑ k, ∑ l, a k l) = _
  rw [hsum, hrow]
  change (2 : ℂ)⁻¹ • (_ + _ + _) = (2 : ℂ)⁻¹ •
    (∑ k : Fin n, ∑ l : Fin n, a (i.succAbove k) (i.succAbove l)) + _
  module

lemma multiplyVector_pfaffian_minor (m : ℕ)
    (B : Fin (2*m+1) → Fin (2*m+1) → ℂ) (hB : ∀ i j, B i j = -B j i)
    (i : Fin (2*m+1)) :
    multiplyVector (2*m) (coordinate i) (pfaffianForm m B) =
      insertCoordinate i (pfaffianForm m (fun k l => B (i.succAbove k) (i.succAbove l))) := by
  apply Subtype.ext
  simp only [multiplyVector_coe, insertCoordinate, LinearMap.comp_apply, exteriorMap_coe,
    pfaffianForm, map_smul, map_pow]
  rw [twoForm_row B hB i, mul_smul_comm, mul_smul_comm]
  congr 1
  apply gauge_invariance
  have h := (exteriorPower.map 2 (coordinateMap i.succAbove)
    (⟨twoForm (fun k l => B (i.succAbove k) (i.succAbove l)), twoForm_mem _⟩ :
      ⋀[ℂ]^2 (CoordinateSpace (Fin (2*m))))).property
  simpa only [exteriorMap_coe] using h

lemma detector_pfaffian_sum (m : ℕ)
    (B : Fin (2*m+1) → Fin (2*m+1) → ℂ) (hB : ∀ i j, B i j = -B j i) :
    detector m B = ∑ i : Fin (2*m+1), (-1 : ℂ)^i.val *
      pfaffian m (fun k l => B (i.succAbove k) (i.succAbove l)) := by
  have he : detectorForm m B = ∑ i : Fin (2*m+1),
      multiplyVector (2*m) (coordinate i) (pfaffianForm m B) := by
    apply Subtype.ext
    simp only [detectorForm, multiplyVector_coe, Submodule.coe_sum, coordinateVector,
      one_smul, map_sum, Finset.sum_mul]
  unfold detector
  rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [multiplyVector_pfaffian_minor m B hB i, topCoefficient_insertCoordinate]
  rfl

lemma twoForm_eq_upper {I : Type*} [Fintype I] [LinearOrder I]
    (B : I → I → ℂ) (hB : ∀ i j, B i j = -B j i) :
    twoForm B = ∑ i, ∑ j, if i < j then
      B i j • (ExteriorAlgebra.ι ℂ (coordinate i) * ExteriorAlgebra.ι ℂ (coordinate j))
      else 0 := by
  classical
  let a (i j : I) : CoordinateAlgebra I :=
    B i j • (ExteriorAlgebra.ι ℂ (coordinate i) * ExteriorAlgebra.ι ℂ (coordinate j))
  have ha (i j) : a i j = a j i := by
    dsimp only [a]
    rw [hB i j, ι_mul_ι_neg (coordinate i) (coordinate j), neg_smul, smul_neg, neg_neg]
  have hd (i) : a i i = 0 := by simp only [a, ExteriorAlgebra.ι_sq_zero, smul_zero]
  have he (i j) : a i j = (if i < j then a i j else 0) +
      (if j < i then a i j else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp only [h, not_lt_of_gt h, ite_true, ite_false, add_zero]
    · simp only [lt_self_iff_false, ite_false, zero_add, hd]
    · simp only [h, not_lt_of_gt h, ite_true, ite_false, zero_add]
  have hs : (∑ i, ∑ j, a i j) =
      (∑ i, ∑ j, if i < j then a i j else 0) +
      (∑ i, ∑ j, if i < j then a i j else 0) := by
    calc
      _ = ∑ i, ∑ j, ((if i < j then a i j else 0) +
          (if j < i then a i j else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact he i j
      _ = _ := ?_
    simp only [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [ha j i]
  change (2 : ℂ)⁻¹ • (∑ i, ∑ j, a i j) = _
  rw [hs]
  change (2 : ℂ)⁻¹ • (_ + _) = ∑ i, ∑ j, if i < j then a i j else 0
  module

end Detector

/-! Alternating functions on vertex labels extend to oriented exterior chains. -/

namespace Oriented

open scoped BigOperators

variable {Y A : Type*} [AddCommGroup A] [Module ℂ A]

instance {n : ℕ} : CoeFun (AltFunction Y n A) (fun _ => (Fin n → Y) → A) :=
  ⟨AltFunction.toFun⟩

variable [LinearOrder Y]

end Oriented

/-! The augmented exterior chain complex and contraction on homogeneous exterior submodules. -/

namespace Detector

open scoped BigOperators

lemma scalar_alt_zero {Y : Type*} {n : ℕ} (f : (Fin n → Y) → ℂ)
    (hf : ∀ v (σ : Equiv.Perm (Fin n)), f (v ∘ σ) = σ.sign • f v)
    (v : Fin n → Y) (hv : ¬ Function.Injective v) : f v = 0 := by
  classical
  obtain ⟨i, j, hvij, hij⟩ := Function.not_injective_iff.mp hv
  have he : v ∘ Equiv.swap i j = v := by
    funext k
    by_cases hki : k = i
    · subst k; simp [hvij]
    by_cases hkj : k = j
    · subst k; simp [hvij]
    simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hh := hf v (Equiv.swap i j)
  rw [he, Equiv.Perm.sign_swap hij] at hh
  change f v = (-1 : ℤ) • f v at hh
  have hn : f v = - f v := by simpa only [neg_one_zsmul] using hh
  linear_combination (1 / 2 : ℂ) * hn

def pfaffianAlt {Y : Type*} (m : ℕ) (β : Y → Y → ℂ) :
    Oriented.AltFunction Y (2*m) ℂ where
  toFun v := pfaffian m (fun i j => β (v i) (v j))
  perm v σ := pfaffian_perm m (fun i j => β (v i) (v j)) σ
  zero v hv := scalar_alt_zero (fun w => pfaffian m (fun i j => β (w i) (w j)))
    (fun w σ => pfaffian_perm m (fun i j => β (w i) (w j)) σ) v hv

def detectorAlt {Y : Type*} (m : ℕ) (β : Y → Y → ℂ) :
    Oriented.AltFunction Y (2*m+1) ℂ where
  toFun v := detector m (fun i j => β (v i) (v j))
  perm v σ := detector_perm m (fun i j => β (v i) (v j)) σ
  zero v hv := scalar_alt_zero (fun w => detector m (fun i j => β (w i) (w j)))
    (fun w σ => detector_perm m (fun i j => β (w i) (w j)) σ) v hv

open scoped BigOperators

open Oriented ChainHomotopy

variable {Y : Type*} [LinearOrder Y]

def cocycle (m : ℕ) (β : Y → Y → ℂ) : Degree Y (2*m+1) →ₗ[ℂ] ℂ :=
  (detectorAlt m β).lift

lemma cocycle_wedge (m : ℕ) (β : Y → Y → ℂ) (v : Fin (2*m+1) → Y) :
    cocycle m β (wedge (2*m+1) v) = detector m (fun i j => β (v i) (v j)) :=
  (detectorAlt m β).lift_wedge v

lemma cocycle_eq_coboundary (m : ℕ) (β : Y → Y → ℂ)
    (hβ : ∀ y z, β y z = -β z y) :
    cocycle m β = (pfaffianAlt m β).lift.comp (d (2*m)) := by
  apply linearMap_ext_wedge
  intro v
  rw [cocycle_wedge, detector_pfaffian_sum m _ (fun i j => hβ (v i) (v j))]
  simp only [LinearMap.comp_apply, d_wedge, map_sum, map_smul,
    AltFunction.lift_wedge, smul_eq_mul]
  rfl

lemma cocycle_closed (m : ℕ) (β : Y → Y → ℂ)
    (hβ : ∀ y z, β y z = -β z y) (x : Degree Y (2*m+2)) :
    cocycle m β (d (2*m+1) x) = 0 := by
  rw [cocycle_eq_coboundary m β hβ, LinearMap.comp_apply, d_square, map_zero]

lemma cocycle_lift_independent (m : ℕ) (β : Y → Y → ℂ) (r : Y → ℂ) :
    cocycle m (fun y z => β y z + r z - r y) = cocycle m β := by
  apply linearMap_ext_wedge
  intro v
  rw [cocycle_wedge, cocycle_wedge]
  exact detector_lift_independent m (fun i j => β (v i) (v j)) (fun i => r (v i))

end Detector

end BassTrace

end

end OAI
