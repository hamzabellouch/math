import OAI.RingTheory.BassTrace.AdmissibleCuts

namespace OAI

/-! Euclidean coordinate simplex volume from the volume of the ℓ¹ ball and sign symmetry. -/

namespace BassTrace.Sparse

open MeasureTheory Set

open scoped ENNReal

def standardSolidSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

def l1UnitPolytope (n : ℕ) : Set (Fin n → ℝ) := {x | ∑ i, |x i| ≤ 1}

def signReflection {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if ε i then x i else -x i

def signChamber {n : ℕ} (ε : Fin n → Bool) : Set (Fin n → ℝ) :=
  signReflection ε ⁻¹' standardSolidSimplex n

lemma measurableSet_standardSolidSimplex (n : ℕ) :
    MeasurableSet (standardSolidSimplex n) := by
  change MeasurableSet ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} ∩ {x | ∑ i, x i ≤ 1})
  apply MeasurableSet.inter
  · simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      (show MeasurableSet {x : Fin n → ℝ | 0 ≤ x i} from
        measurableSet_le measurable_const (measurable_pi_apply i))
  · exact measurableSet_le (by fun_prop) measurable_const

lemma signReflection_measurePreserving {n : ℕ} (ε : Fin n → Bool) :
    MeasurePreserving (signReflection ε) := by
  unfold signReflection
  apply volume_preserving_pi (f := fun i t => if ε i then t else -t)
  intro i
  cases h : ε i
  · simpa only [h, Bool.false_eq_true, ↓reduceIte] using
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  · simp only [↓reduceIte]
    exact MeasurePreserving.id (volume : Measure ℝ)

lemma measurableSet_signChamber {n : ℕ} (ε : Fin n → Bool) :
    MeasurableSet (signChamber ε) :=
  (signReflection_measurePreserving ε).measurable (measurableSet_standardSolidSimplex n)

lemma volume_signChamber {n : ℕ} (ε : Fin n → Bool) :
    volume (signChamber ε) = volume (standardSolidSimplex n) :=
  (signReflection_measurePreserving ε).measure_preimage
    (measurableSet_standardSolidSimplex n).nullMeasurableSet

lemma signChamber_mem_iff {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℝ) :
    x ∈ signChamber ε ↔
      (∀ i, if ε i then 0 ≤ x i else x i ≤ 0) ∧ x ∈ l1UnitPolytope n := by
  change ((∀ i, 0 ≤ if ε i then x i else -x i) ∧
    ∑ i, (if ε i then x i else -x i) ≤ 1) ↔ _
  have hcond : (∀ i, 0 ≤ if ε i then x i else -x i) ↔
      (∀ i, if ε i then 0 ≤ x i else x i ≤ 0) := by
    apply forall_congr'
    intro i
    cases ε i <;> simp
  rw [hcond]
  constructor
  · rintro ⟨h,hx⟩
    refine ⟨h,?_⟩
    change ∑ i, |x i| ≤ 1
    convert hx using 1
    apply Finset.sum_congr rfl
    intro i _
    have hi := h i
    cases he : ε i <;> simp only [he, ↓reduceIte] at hi ⊢
    · exact abs_of_nonpos hi
    · exact abs_of_nonneg hi
  · rintro ⟨h,hx⟩
    refine ⟨h,?_⟩
    change ∑ i, |x i| ≤ 1 at hx
    convert hx using 1
    apply Finset.sum_congr rfl
    intro i _
    have hi := h i
    cases he : ε i <;> simp only [he, ↓reduceIte] at hi ⊢
    · exact (abs_of_nonpos hi).symm
    · exact (abs_of_nonneg hi).symm

lemma union_signChamber (n : ℕ) :
    (⋃ ε : Fin n → Bool, signChamber ε) = l1UnitPolytope n := by
  classical
  ext x
  simp only [mem_iUnion,signChamber_mem_iff]
  constructor
  · rintro ⟨ε,_,hx⟩
    exact hx
  · intro hx
    refine ⟨fun i => decide (0 ≤ x i),?_,hx⟩
    intro i
    by_cases hi : 0 ≤ x i
    · simp [hi]
    · simp [hi, (not_le.mp hi).le]

lemma signChamber_aedisjoint {n : ℕ} :
    Pairwise (fun ε η : Fin n → Bool =>
      AEDisjoint (volume : Measure (Fin n → ℝ)) (signChamber ε) (signChamber η)) := by
  intro ε η hne
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hne
  change volume (signChamber ε ∩ signChamber η) = 0
  apply measure_mono_null (t := {x | x i = 0})
  · intro x hx
    have hε := ((signChamber_mem_iff ε x).mp hx.1).1 i
    have hη := ((signChamber_mem_iff η x).mp hx.2).1 i
    cases he : ε i <;> cases hh : η i <;> simp_all <;> linarith
  · exact Measure.pi_hyperplane (fun _ : Fin n => (volume : Measure ℝ)) i 0

lemma volume_l1UnitPolytope (n : ℕ) :
    volume (l1UnitPolytope n) = ENNReal.ofReal ((2 : ℝ)^n / n.factorial) := by
  cases n with
  | zero =>
    have he : l1UnitPolytope 0 = Set.univ := by ext x; simp [l1UnitPolytope]
    rw [he, Measure.volume_pi_eq_dirac (fun i : Fin 0 => Fin.elim0 i)]
    simp
  | succ n =>
    have h := volume_sum_rpow_le (Fin (n+1)) (p := 1) (by norm_num) 1
    norm_num only [div_one, Real.rpow_one, Fintype.card_fin, ENNReal.ofReal_one,
      one_pow,one_mul] at h
    rw [Real.Gamma_two, mul_one, Real.Gamma_nat_eq_factorial] at h
    exact h

theorem volume_standardSolidSimplex (n : ℕ) :
    volume (standardSolidSimplex n) = ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  have hsum := measure_iUnion₀ (signChamber_aedisjoint (n := n))
    (fun ε => (measurableSet_signChamber ε).nullMeasurableSet)
  rw [union_signChamber, volume_l1UnitPolytope] at hsum
  simp only [volume_signChamber,tsum_fintype,Finset.sum_const,Finset.card_univ,
    Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_pow,Nat.cast_ofNat] at hsum
  have hc : (2 : ℝ≥0∞)^n ≠ 0 := by positivity
  have hf : (2 : ℝ≥0∞)^n ≠ ⊤ := by finiteness
  apply (ENNReal.mul_right_inj hc hf).mp
  rw [← hsum]
  conv_rhs => rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
  rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end BassTrace.Sparse

end OAI
