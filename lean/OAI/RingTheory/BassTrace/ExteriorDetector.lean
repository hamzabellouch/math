import OAI.RingTheory.BassTrace.PathWeights

namespace OAI

noncomputable section

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

/-! Exterior identities for the lift-independent Pfaffian detector. -/

namespace BassTrace.Detector

section

open scoped BigOperators

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

lemma ι_mul_ι_neg (u v : M) :
    ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v =
      -(ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u v)

lemma ι_commute_two (u v w : M) :
    Commute (ExteriorAlgebra.ι R u)
      (ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w) := by
  change _ * _ = _ * _
  calc
    _ = (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) * ExteriorAlgebra.ι R w :=
      (mul_assoc _ _ _).symm
    _ = -(ExteriorAlgebra.ι R v * (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R w)) := by
      rw [ι_mul_ι_neg u v, neg_mul, mul_assoc]
    _ = ExteriorAlgebra.ι R v * (ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R u) := by
      rw [ι_mul_ι_neg u w, mul_neg, neg_neg]
    _ = _ := (mul_assoc _ _ _).symm

lemma ι_commute_degree_two (u : M) {b : ExteriorAlgebra R M} (hb : b ∈ ⋀[R]^2 M) :
    Commute (ExteriorAlgebra.ι R u) b := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree R 2] at hb
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨v, rfl⟩ := hb
    simpa [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
      Matrix.vecTail] using ι_commute_two u (v 0) (v 1)
  | zero => exact Commute.zero_right _
  | add b c _ _ hb hc => exact hb.add_right hc
  | smul a b _ hb =>
    show ExteriorAlgebra.ι R u * (a • b) = (a • b) * ExteriorAlgebra.ι R u
    rw [mul_smul_comm, smul_mul_assoc, hb.eq]

lemma gauge_invariance (u v : M) {b : ExteriorAlgebra R M}
    (hb : b ∈ ⋀[R]^2 M) (m : ℕ) :
    ExteriorAlgebra.ι R u *
        (b + ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v)^m =
      ExteriorAlgebra.ι R u * b^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_add, pow_succ, ← mul_assoc]
    have hcomm := (ι_commute_degree_two u hb).pow_right m
    have hz : ExteriorAlgebra.ι R u * b^m *
        (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) = 0 := by
      rw [hcomm.eq, mul_assoc, ← mul_assoc (ExteriorAlgebra.ι R u),
        ExteriorAlgebra.ι_sq_zero, zero_mul, mul_zero]
    simp only [mul_assoc] at hz ⊢
    rw [hz, add_zero]

end

open scoped BigOperators

section

variable {I : Type*} [Fintype I]

abbrev CoordinateSpace (I : Type*) := I →₀ ℂ

abbrev CoordinateAlgebra (I : Type*) := ExteriorAlgebra ℂ (CoordinateSpace I)

def coordinate (i : I) : CoordinateSpace I := Finsupp.single i 1

def coordinateVector (a : I → ℂ) : CoordinateSpace I := ∑ i, a i • coordinate i

def rawTwoForm (B : I → I → ℂ) : CoordinateAlgebra I :=
  ∑ i, ∑ j, B i j • (ExteriorAlgebra.ι ℂ (coordinate i) * ExteriorAlgebra.ι ℂ (coordinate j))

def twoForm (B : I → I → ℂ) : CoordinateAlgebra I := (2 : ℂ)⁻¹ • rawTwoForm B

lemma rawTwoForm_add (A B : I → I → ℂ) :
    rawTwoForm (fun i j => A i j + B i j) = rawTwoForm A + rawTwoForm B := by
  simp only [rawTwoForm, add_smul, Finset.sum_add_distrib]

lemma rawTwoForm_sub (A B : I → I → ℂ) :
    rawTwoForm (fun i j => A i j - B i j) = rawTwoForm A - rawTwoForm B := by
  simp only [rawTwoForm, sub_smul, Finset.sum_sub_distrib]

lemma rawTwoForm_rank_one (a b : I → ℂ) :
    rawTwoForm (fun i j => a i * b j) =
      ExteriorAlgebra.ι ℂ (coordinateVector a) * ExteriorAlgebra.ι ℂ (coordinateVector b) := by
  simp only [rawTwoForm, coordinateVector, map_sum, map_smul, Finset.sum_mul,
    Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

lemma twoForm_add (A B : I → I → ℂ) :
    twoForm (fun i j => A i j + B i j) = twoForm A + twoForm B := by
  simp only [twoForm, rawTwoForm_add, smul_add]

lemma twoForm_decomposable (a b : I → ℂ) :
    twoForm (fun i j => a i * b j - b i * a j) =
      ExteriorAlgebra.ι ℂ (coordinateVector a) * ExteriorAlgebra.ι ℂ (coordinateVector b) := by
  rw [twoForm, rawTwoForm_sub, rawTwoForm_rank_one, rawTwoForm_rank_one,
    ι_mul_ι_neg (coordinateVector b) (coordinateVector a), sub_neg_eq_add]
  module

lemma twoForm_mem (B : I → I → ℂ) : twoForm B ∈ ⋀[ℂ]^2 (CoordinateSpace I) := by
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  change _ ∈ (ExteriorAlgebra.ι ℂ).range^2
  rw [pow_two]
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)

lemma twoForm_lift_change (B : I → I → ℂ) (r : I → ℂ) :
    twoForm (fun i j => B i j + r j - r i) = twoForm B +
      ExteriorAlgebra.ι ℂ (coordinateVector (fun _ : I => 1)) *
        ExteriorAlgebra.ι ℂ (coordinateVector r) := by
  have he : (fun i j => B i j + r j - r i) =
      (fun i j => B i j + ((1 : ℂ)*r j-r i*1)) := by funext i j; ring
  rw [he, twoForm_add, twoForm_decomposable]

lemma detector_form_lift_independent (B : I → I → ℂ) (r : I → ℂ) (m : ℕ) :
    ExteriorAlgebra.ι ℂ (coordinateVector (fun _ : I => 1)) *
        ((m.factorial : ℂ)⁻¹ • (twoForm (fun i j => B i j + r j - r i))^m) =
      ExteriorAlgebra.ι ℂ (coordinateVector (fun _ : I => 1)) *
        ((m.factorial : ℂ)⁻¹ • (twoForm B)^m) := by
  rw [twoForm_lift_change, mul_smul_comm, mul_smul_comm,
    gauge_invariance _ _ (twoForm_mem B)]

def coordinateMap {J : Type*} (f : I → J) : CoordinateSpace I →ₗ[ℂ] CoordinateSpace J :=
  Finsupp.lmapDomain ℂ ℂ f

omit [Fintype I] in
@[simp] lemma coordinateMap_coordinate {J : Type*} (f : I → J) (i : I) :
    coordinateMap f (coordinate i) = coordinate (f i) := Finsupp.mapDomain_single

lemma coordinateMap_vector {J : Type*} [Fintype J] (f : I ≃ J) (a : I → ℂ) :
    coordinateMap f (coordinateVector a) = coordinateVector (a ∘ f.symm) := by
  simp only [coordinateVector, map_sum, map_smul, coordinateMap_coordinate]
  simpa only [Equiv.symm_apply_apply, Function.comp_def] using
    Equiv.sum_comp f (fun j => a (f.symm j) • coordinate j)

lemma twoForm_map {J : Type*} [Fintype J] (f : I ≃ J) (B : J → J → ℂ) :
    ExteriorAlgebra.map (coordinateMap f) (twoForm (fun i j => B (f i) (f j))) =
      twoForm B := by
  simp only [twoForm, rawTwoForm, map_smul, map_sum, map_mul,
    ExteriorAlgebra.map_apply_ι, coordinateMap_coordinate]
  apply congrArg (fun x : CoordinateAlgebra J => (2 : ℂ)⁻¹ • x)
  calc
    _ = ∑ i : I, ∑ j : J, B (f i) j •
        (ExteriorAlgebra.ι ℂ (coordinate (f i)) * ExteriorAlgebra.ι ℂ (coordinate j)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp f (fun j : J => B (f i) j •
        (ExteriorAlgebra.ι ℂ (coordinate (f i)) * ExteriorAlgebra.ι ℂ (coordinate j)))
    _ = _ := Equiv.sum_comp f (fun i : J => ∑ j : J, B i j •
        (ExteriorAlgebra.ι ℂ (coordinate i) * ExteriorAlgebra.ι ℂ (coordinate j)))

end

section

abbrev coordinateBasis (n : ℕ) : Module.Basis (Fin n) ℂ (CoordinateSpace (Fin n)) :=
  Finsupp.basisSingleOne

def topIndex (n : ℕ) : Set.powersetCard (Fin n) n :=
  Set.powersetCard.ofFinEmbEquiv ((OrderIso.refl (Fin n)).toOrderEmbedding)

lemma topIndex_val (n : ℕ) : (topIndex n).val = Finset.univ := by
  ext i
  simp only [Finset.mem_univ, iff_true]
  change i ∈ Set.powersetCard.ofFinEmbEquiv ((OrderIso.refl (Fin n)).toOrderEmbedding)
  rw [Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]
  exact ⟨i, rfl⟩

lemma topIndex_unique (n : ℕ) (s : Set.powersetCard (Fin n) n) : s = topIndex n := by
  apply Subtype.ext
  rw [topIndex_val]
  apply Finset.eq_univ_of_card
  simp only [Fintype.card_fin]
  exact s.property

abbrev topBasis (n : ℕ) := (coordinateBasis n).exteriorPower n

def topVolume (n : ℕ) : ⋀[ℂ]^n (CoordinateSpace (Fin n)) :=
  exteriorPower.ιMulti ℂ n coordinate

lemma topBasis_topIndex (n : ℕ) : topBasis n (topIndex n) = topVolume n := by
  rw [exteriorPower.basis_apply]
  simp only [exteriorPower.ιMulti_family, topIndex, Equiv.symm_apply_apply]
  rfl

def topCoefficient (n : ℕ) : (⋀[ℂ]^n (CoordinateSpace (Fin n))) →ₗ[ℂ] ℂ :=
  (topBasis n).coord (topIndex n)

lemma topCoefficient_topVolume (n : ℕ) : topCoefficient n (topVolume n) = 1 := by
  rw [← topBasis_topIndex]
  change (topBasis n).repr (topBasis n (topIndex n)) (topIndex n) = 1
  rw [Module.Basis.repr_self, Finsupp.single_eq_same]

lemma top_scalar (n : ℕ) (x : ⋀[ℂ]^n (CoordinateSpace (Fin n))) :
    x = topCoefficient n x • topVolume n := by
  classical
  have hsum : (∑ s : Set.powersetCard (Fin n) n,
      (topBasis n).repr x s • topBasis n s) =
      (topBasis n).repr x (topIndex n) • topBasis n (topIndex n) := by
    apply Finset.sum_eq_single (topIndex n)
    · intro s _ hs; exact (hs (topIndex_unique n s)).elim
    · simp
  calc
    x = ∑ s, (topBasis n).repr x s • topBasis n s := ((topBasis n).sum_repr x).symm
    _ = _ := hsum
    _ = _ := by rw [topBasis_topIndex]; rfl

lemma homogeneous_mul {I : Type*} {n m : ℕ} {x y : CoordinateAlgebra I}
    (hx : x ∈ ⋀[ℂ]^n (CoordinateSpace I)) (hy : y ∈ ⋀[ℂ]^m (CoordinateSpace I)) :
    x*y ∈ ⋀[ℂ]^(n+m) (CoordinateSpace I) := by
  change _ ∈ (ExteriorAlgebra.ι ℂ).range^(n+m)
  rw [pow_add]
  exact Submodule.mul_mem_mul hx hy

lemma homogeneous_pow {I : Type*} {n : ℕ} {x : CoordinateAlgebra I}
    (hx : x ∈ ⋀[ℂ]^n (CoordinateSpace I)) (m : ℕ) :
    x^m ∈ ⋀[ℂ]^(n*m) (CoordinateSpace I) := by
  induction m with
  | zero => simp [ExteriorAlgebra.exteriorPower]
  | succ m ih =>
    rw [pow_succ, Nat.mul_succ]
    exact homogeneous_mul ih hx

def pfaffian (m : ℕ) (B : Fin (2*m) → Fin (2*m) → ℂ) : ℂ :=
  topCoefficient (2*m) ⟨(m.factorial : ℂ)⁻¹ • (twoForm B)^m,
    Submodule.smul_mem _ _ (homogeneous_pow (twoForm_mem B) m)⟩

lemma topVolume_map_perm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    exteriorPower.map n (coordinateMap σ) (topVolume n) =
      σ.sign • topVolume n := by
  simp only [topVolume, exteriorPower.map_apply_ιMulti]
  have he : (coordinateMap σ) ∘ coordinate = coordinate ∘ σ := by
    funext i
    exact coordinateMap_coordinate _ _
  rw [he]
  exact (exteriorPower.ιMulti ℂ n).map_perm coordinate σ

lemma topCoefficient_map_perm (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : ⋀[ℂ]^n (CoordinateSpace (Fin n))) :
    topCoefficient n (exteriorPower.map n (coordinateMap σ) x) =
      σ.sign • topCoefficient n x := by
  conv_lhs => rw [top_scalar n x]
  rw [map_smul, topVolume_map_perm]
  simp only [Units.smul_def, map_zsmul, map_smul, topCoefficient_topVolume, smul_eq_mul]
  ring

end

lemma exteriorMap_coe {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (n : ℕ) (f : M →ₗ[ℂ] N) (x : ⋀[ℂ]^n M) :
    (exteriorPower.map n f x : ExteriorAlgebra ℂ N) =
      ExteriorAlgebra.map f (x : ExteriorAlgebra ℂ M) := by
  have he : (⋀[ℂ]^n N).subtype.comp (exteriorPower.map n f) =
      (ExteriorAlgebra.map f).toLinearMap.comp (⋀[ℂ]^n M).subtype := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, AlgHom.toLinearMap_apply, exteriorPower.map_apply_ιMulti,
      exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti]
  exact LinearMap.congr_fun he x

def multiplyVector {I : Type*} (n : ℕ) (v : CoordinateSpace I) :
    (⋀[ℂ]^n (CoordinateSpace I)) →ₗ[ℂ] ⋀[ℂ]^(n+1) (CoordinateSpace I) where
  toFun x := ⟨ExteriorAlgebra.ι ℂ v * x, by
    change _ ∈ (ExteriorAlgebra.ι ℂ).range ^ (n+1)
    rw [pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range.mpr ⟨v, rfl⟩) x.property⟩
  map_add' x y := by apply Subtype.ext; exact mul_add _ _ _
  map_smul' a x := by apply Subtype.ext; exact mul_smul_comm _ _ _

@[simp] lemma multiplyVector_coe {I : Type*} (n : ℕ) (v : CoordinateSpace I)
    (x : ⋀[ℂ]^n (CoordinateSpace I)) :
    (multiplyVector n v x : CoordinateAlgebra I) = ExteriorAlgebra.ι ℂ v * x := rfl

def insertCoordinate {n : ℕ} (i : Fin (n+1)) :
    (⋀[ℂ]^n (CoordinateSpace (Fin n))) →ₗ[ℂ] ⋀[ℂ]^(n+1) (CoordinateSpace (Fin (n+1))) :=
  (multiplyVector n (coordinate i)).comp (exteriorPower.map n (coordinateMap i.succAbove))

lemma insertCoordinate_topVolume {n : ℕ} (i : Fin (n+1)) :
    insertCoordinate i (topVolume n) = (-1 : ℂ)^i.val • topVolume (n+1) := by
  apply Subtype.ext
  simp only [insertCoordinate, LinearMap.comp_apply, multiplyVector_coe,
    exteriorMap_coe, topVolume, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.map_apply_ιMulti, Submodule.coe_smul]
  have he : (coordinateMap i.succAbove) ∘ coordinate = fun j => coordinate (i.succAbove j) := by
    funext j
    exact coordinateMap_coordinate _ _
  rw [he]
  have hi : i.insertNth (coordinate i) (fun j => coordinate (i.succAbove j)) = coordinate := by
    exact Fin.insertNth_eq_iff.mpr ⟨rfl, rfl⟩
  have hh := (ExteriorAlgebra.ιMulti ℂ (n+1)).neg_one_pow_smul_map_insertNth i
    (coordinate i) (fun j => coordinate (i.succAbove j))
  rw [hi, ← Int.cast_smul_eq_zsmul ℂ] at hh
  simpa only [ExteriorAlgebra.ιMulti_succ_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.vecTail, Function.comp_def, Int.cast_pow, Int.cast_neg, Int.cast_one] using hh.symm

lemma topCoefficient_insertCoordinate {n : ℕ} (i : Fin (n+1))
    (x : ⋀[ℂ]^n (CoordinateSpace (Fin n))) :
    topCoefficient (n+1) (insertCoordinate i x) = (-1 : ℂ)^i.val * topCoefficient n x := by
  conv_lhs => rw [top_scalar n x]
  rw [map_smul, insertCoordinate_topVolume, map_smul, map_smul, topCoefficient_topVolume]
  simp only [smul_eq_mul, one_mul, mul_comm]

def pfaffianForm {I : Type*} [Fintype I] (m : ℕ) (B : I → I → ℂ) :
    ⋀[ℂ]^(2*m) (CoordinateSpace I) :=
  ⟨(m.factorial : ℂ)⁻¹ • (twoForm B)^m,
    Submodule.smul_mem _ _ (homogeneous_pow (twoForm_mem B) m)⟩

def detectorForm {I : Type*} [Fintype I] (m : ℕ) (B : I → I → ℂ) :
    ⋀[ℂ]^(2*m+1) (CoordinateSpace I) :=
  multiplyVector (2*m) (coordinateVector (fun _ => 1)) (pfaffianForm m B)

def detector (m : ℕ) (B : Fin (2*m+1) → Fin (2*m+1) → ℂ) : ℂ :=
  topCoefficient (2*m+1) (detectorForm m B)

lemma detector_lift_independent (m : ℕ)
    (B : Fin (2*m+1) → Fin (2*m+1) → ℂ) (r : Fin (2*m+1) → ℂ) :
    detector m (fun i j => B i j + r j - r i) = detector m B := by
  apply congrArg (topCoefficient (2*m+1))
  apply Subtype.ext
  exact detector_form_lift_independent B r m

lemma pfaffianForm_map {I J : Type*} [Fintype I] [Fintype J] (f : I ≃ J)
    (m : ℕ) (B : J → J → ℂ) :
    exteriorPower.map (2*m) (coordinateMap f) (pfaffianForm m (fun i j => B (f i) (f j))) =
      pfaffianForm m B := by
  apply Subtype.ext
  simp only [exteriorMap_coe, pfaffianForm, map_smul, map_pow, twoForm_map]

lemma detectorForm_map {I J : Type*} [Fintype I] [Fintype J] (f : I ≃ J)
    (m : ℕ) (B : J → J → ℂ) :
    exteriorPower.map (2*m+1) (coordinateMap f) (detectorForm m (fun i j => B (f i) (f j))) =
      detectorForm m B := by
  apply Subtype.ext
  simp only [exteriorMap_coe, detectorForm, multiplyVector_coe, map_mul,
    ExteriorAlgebra.map_apply_ι, coordinateMap_vector, pfaffianForm, map_smul, map_pow, twoForm_map]
  rfl

lemma pfaffian_perm (m : ℕ) (B : Fin (2*m) → Fin (2*m) → ℂ) (σ : Equiv.Perm (Fin (2*m))) :
    pfaffian m (fun i j => B (σ i) (σ j)) = σ.sign • pfaffian m B := by
  have he := congrArg (topCoefficient (2*m)) (pfaffianForm_map σ m B)
  rw [topCoefficient_map_perm] at he
  change σ.sign • pfaffian m (fun i j => B (σ i) (σ j)) = pfaffian m B at he
  rw [← he, smul_smul, Int.units_mul_self, one_smul]

lemma detector_perm (m : ℕ) (B : Fin (2*m+1) → Fin (2*m+1) → ℂ)
    (σ : Equiv.Perm (Fin (2*m+1))) :
    detector m (fun i j => B (σ i) (σ j)) = σ.sign • detector m B := by
  have he := congrArg (topCoefficient (2*m+1)) (detectorForm_map σ m B)
  rw [topCoefficient_map_perm] at he
  change σ.sign • detector m (fun i j => B (σ i) (σ j)) = detector m B at he
  rw [← he, smul_smul, Int.units_mul_self, one_smul]

end BassTrace.Detector

end

end OAI
