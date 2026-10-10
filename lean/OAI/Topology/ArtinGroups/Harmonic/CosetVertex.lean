import Mathlib
import OAI.Topology.ArtinGroups.DeligneDefinitions
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver

namespace OAI

namespace HarmonicArtin
universe u
variable {S : Type u}

 theorem artinParabolic_mono (M : CoxeterMatrix S) {T U : Set S} (h : T ⊆ U) :
    artinParabolic M T ≤ artinParabolic M U :=
  Subgroup.closure_mono (Set.image_mono h)

 theorem spherical_empty (M : CoxeterMatrix S) : IsSpherical M ∅ := by
  simp only [IsSpherical, coxeterParabolic, Set.image_empty, Subgroup.closure_empty]
  infer_instance

 theorem spherical_singleton (M : CoxeterMatrix S) (s : S) : IsSpherical M {s} := by
  have horder : IsOfFinOrder (M.simple s) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, M.toCoxeterSystem.simple_sq s⟩
  unfold IsSpherical coxeterParabolic
  rw [Set.image_singleton, ← Subgroup.zpowers_eq_closure]
  exact horder.finite_zpowers

 def cosetVertex (M : CoxeterMatrix S) (T : Set S) (hT : IsSpherical M T)
    (x : Artin M) : Deligne M := ⟨(T, rightCoset M T x), hT, x, rfl⟩

 theorem rightCoset_empty (M : CoxeterMatrix S) (x : Artin M) :
    rightCoset M ∅ x = {x} := by
  ext g
  simp [rightCoset, artinParabolic, mul_inv_eq_one]

 theorem elementVertex_le (M : CoxeterMatrix S) (T : Set S) (hT : IsSpherical M T)
    (x g : Artin M) (hg : g * x⁻¹ ∈ artinParabolic M T) :
    cosetVertex M ∅ (spherical_empty M) g ≤ cosetVertex M T hT x := by
  change (∅ : Set S) ⊆ T ∧ rightCoset M ∅ g ⊆ rightCoset M T x
  refine ⟨Set.empty_subset T, ?_⟩
  rw [rightCoset_empty]
  exact Set.singleton_subset_iff.mpr hg

 theorem deligne_connected (M : CoxeterMatrix S) : CategoryTheory.IsConnected (Deligne M) := by
  apply CategoryTheory.IsConnected.of_induct (j₀ := cosetVertex M ∅ (spherical_empty M) 1)
  intro p hbase hmor P
  have hstep (s : S) (x : Artin M) :
      cosetVertex M ∅ (spherical_empty M) x ∈ p ↔
        cosetVertex M ∅ (spherical_empty M) (generator M s * x) ∈ p := by
    have hx : x * x⁻¹ ∈ artinParabolic M {s} := by simp
    have hs : (generator M s * x) * x⁻¹ ∈ artinParabolic M {s} := by
      simp only [mul_assoc, mul_inv_cancel, mul_one]
      exact Subgroup.subset_closure (Set.mem_image_of_mem _ (Set.mem_singleton s))
    exact (hmor (CategoryTheory.homOfLE
      (elementVertex_le M {s} (spherical_singleton M s) x x hx))).trans
      (hmor (CategoryTheory.homOfLE
        (elementVertex_le M {s} (spherical_singleton M s) x (generator M s * x) hs))).symm
  have hall (x : Artin M) : cosetVertex M ∅ (spherical_empty M) x ∈ p := by
    have hgen : Subgroup.closure (Set.range (generator M)) = ⊤ :=
      PresentedGroup.closure_range_of (braidRelators M)
    have hx : x ∈ Subgroup.closure (Set.range (generator M)) := by rw [hgen]; trivial
    induction hx using Subgroup.closure_induction_left with
    | one => exact hbase
    | mul_left g hg y _ hy =>
      rcases hg with ⟨s, rfl⟩
      exact (hstep s y).mp hy
    | inv_mul_cancel g hg y _ hy =>
      rcases hg with ⟨s, rfl⟩
      apply (hstep s ((generator M s)⁻¹ * y)).mpr
      simpa only [mul_inv_cancel_left] using hy
  rcases P with ⟨⟨T, C⟩, hT, x, hx⟩
  change C = rightCoset M T x at hx
  subst C
  exact (hmor (CategoryTheory.homOfLE
    (elementVertex_le M T hT x x (by simp)))).mp (hall x)

open Matrix

theorem harmonic_minimum_principle {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hC : C.PosDef)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ (C *ᵥ x) i) : ∀ i, 0 ≤ x i := by
  classical
  let y : ι → ℝ := fun i => min (x i) 0
  let z : ι → ℝ := fun i => max (x i) 0
  have hy : ∀ i, y i ≤ 0 := fun i => min_le_right _ _
  have hz : ∀ i, 0 ≤ z i := fun i => le_max_right _ _
  have hsplit : x = y + z := by
    funext i
    simp only [Pi.add_apply, y, z, min_add_max, add_zero]
  have hyz : ∀ i, y i * z i = 0 := by
    intro i
    dsimp [y, z]
    by_cases hi : x i ≤ 0
    · simp [min_eq_left hi, max_eq_right hi]
    · simp [min_eq_right (le_of_not_ge hi), max_eq_left (le_of_not_ge hi)]
  have hcross : 0 ≤ y ⬝ᵥ (C *ᵥ z) := by
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_nonneg
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_nonneg
    intro j _
    by_cases hij : i = j
    · subst j
      apply le_of_eq
      calc
        0 = C i i * (y i * z i) := by rw [hyz i, mul_zero]
        _ = y i * (C i i * z i) := by ring
    · simpa only [mul_assoc] using
        mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (hy i) (hOff i j hij)) (hz j)
  have htotal : y ⬝ᵥ (C *ᵥ x) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (hy i) (hx i)
  have hym : y ⬝ᵥ (C *ᵥ y) ≤ 0 := by
    rw [hsplit, Matrix.mulVec_add, dotProduct_add] at htotal
    linarith
  have hy0 : y = 0 := by
    by_contra h
    have hp := hC.dotProduct_mulVec_pos h
    exact (not_lt_of_ge hym) (by simpa only [star_trivial] using hp)
  intro i
  have hi : min (x i) 0 = 0 := congrFun hy0 i
  exact (min_eq_right_iff).mp hi

theorem harmonic_solve {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosDef) (v : ι → ℝ) :
    C *ᵥ (C⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv C ((Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit),
    Matrix.one_mulVec]

theorem harmonic_extension_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosDef)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) : ∀ i, 0 ≤ (C⁻¹ *ᵥ v) i := by
  apply harmonic_minimum_principle C hC hOff
  simpa only [harmonic_solve C hC v] using hv

theorem harmonic_inverse_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosDef)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0) (i j : ι) : 0 ≤ C⁻¹ i j := by
  have hv : ∀ k : ι, (0 : ℝ) ≤ (Pi.single j (1 : ℝ) : ι → ℝ) k := by
    intro k
    simp only [Pi.single_apply]
    split_ifs <;> positivity
  have hi := harmonic_extension_nonneg C hC hOff (Pi.single j 1) hv i
  simpa [Matrix.mulVec_single] using hi

theorem harmonic_positive_neighbor {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hCx : ∀ i, 0 ≤ (C *ᵥ x) i)
    {i j : ι} (hij : C i j < 0) (hj : 0 < x j) : 0 < x i := by
  classical
  by_contra hi
  have hi0 : x i = 0 := le_antisymm (le_of_not_gt hi) (hx i)
  have hterm : ∀ k ∈ (Finset.univ : Finset ι), C i k * x k ≤ 0 := by
    intro k _
    by_cases hik : i = k
    · subst k
      rw [hi0, mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (hOff i k hik) (hx k)
  have hsum : (C *ᵥ x) i < 0 :=
    Finset.sum_neg' hterm ⟨j, Finset.mem_univ j, mul_neg_of_neg_of_pos hij hj⟩
  exact (not_lt_of_ge (hCx i)) hsum

theorem harmonic_positive_path {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hCx : ∀ i, 0 ≤ (C *ᵥ x) i)
    {i j : ι} (hij : Relation.ReflTransGen (fun a b => C a b < 0) i j)
    (hj : 0 < x j) : 0 < x i := by
  induction hij using Relation.ReflTransGen.head_induction_on with
  | refl => exact hj
  | @head a b hab _ ih => exact harmonic_positive_neighbor C hOff x hx hCx hab ih

theorem harmonic_inverse_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosDef)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0) {i j : ι}
    (hij : Relation.ReflTransGen (fun a b => C a b < 0) i j) : 0 < C⁻¹ i j := by
  have hv : ∀ k : ι, (0 : ℝ) ≤ (Pi.single j (1 : ℝ) : ι → ℝ) k := by
    intro k
    simp only [Pi.single_apply]
    split_ifs <;> positivity
  have hdiag : 0 < (C⁻¹ *ᵥ Pi.single j (1 : ℝ)) j := by
    simpa [Matrix.mulVec_single] using (hC.inv.diag_pos (i := j))
  have hp := harmonic_positive_path C hOff (C⁻¹ *ᵥ Pi.single j (1 : ℝ))
    (harmonic_extension_nonneg C hC hOff _ hv)
    (by simpa only [harmonic_solve C hC] using hv) hij hdiag
  simpa [Matrix.mulVec_single] using hp

theorem harmonic_two_point_equality {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hC : C.PosDef)
    (p p' a a' : ι → ℝ)
    (hrow : a' - a = -(C *ᵥ (p' - p)))
    (hforward : 0 ≤ a' ⬝ᵥ (p' - p))
    (hreverse : 0 ≤ a ⬝ᵥ (p - p')) : p = p' ∧ a = a' := by
  have hneg : p - p' = -(p' - p) := by abel
  have hbound : 0 ≤ (a' - a) ⬝ᵥ (p' - p) := by
    rw [hneg, dotProduct_neg] at hreverse
    rw [sub_dotProduct]
    linarith
  rw [hrow, neg_dotProduct, dotProduct_comm] at hbound
  have hdelta : p' - p = 0 := by
    by_contra h
    have hp := hC.dotProduct_mulVec_pos h
    simp only [star_trivial] at hp
    linarith
  have heq : p = p' := (sub_eq_zero.mp hdelta).symm
  refine ⟨heq, ?_⟩
  rw [hdelta, Matrix.mulVec_zero, neg_zero] at hrow
  exact (sub_eq_zero.mp hrow).symm

theorem harmonic_scaled_form {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (v w : ι → ℝ) :
    (v * w) ⬝ᵥ (C *ᵥ (v * w)) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, (-C i j * v i * v j) * (w i - w j)^2 +
      ∑ i, v i * (C *ᵥ v) i * (w i)^2 := by
  classical
  have hswap : (∑ i, ∑ j, C i j * v i * v j * (w j)^2) =
      ∑ i, ∑ j, C i j * v i * v j * (w i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hSym j i]
    ring
  have hexpand : (∑ i, ∑ j, (-C i j * v i * v j) * (w i - w j)^2) =
      -(∑ i, ∑ j, C i j * v i * v j * (w i)^2) +
      2 * (∑ i, ∑ j, C i j * v i * v j * w i * w j) -
      (∑ i, ∑ j, C i j * v i * v j * (w j)^2) := by
    simp only [← Finset.sum_neg_distrib, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hdiag : (∑ i, v i * (C *ᵥ v) i * (w i)^2) =
      ∑ i, ∑ j, C i j * v i * v j * (w i)^2 := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hquad : (v * w) ⬝ᵥ (C *ᵥ (v * w)) =
      ∑ i, ∑ j, C i j * v i * v j * w i * w j := by
    simp only [Matrix.mulVec, dotProduct, Pi.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand, hswap, hdiag, hquad]
  ring

theorem harmonic_posDef_of_strict_row {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (hConn : ∀ i j, Relation.ReflTransGen (fun a b => C a b < 0) i j)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (hCv : ∀ i, 0 ≤ (C *ᵥ v) i) (hStrict : ∃ k, 0 < (C *ᵥ v) k) : C.PosDef := by
  classical
  have hHerm : C.IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    exact hSym j i
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hHerm
  intro x hx
  simp only [star_trivial]
  let w : ι → ℝ := fun i => x i / v i
  have hxw : x = v * w := by
    funext i
    dsimp [w]
    exact (mul_div_cancel₀ (x i) (ne_of_gt (hv i))).symm
  let e : ι → ι → ℝ := fun i j => (-C i j * v i * v j) * (w i - w j)^2
  let f : ι → ℝ := fun i => v i * (C *ᵥ v) i * (w i)^2
  have he : ∀ i j, 0 ≤ e i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [e]
    · exact mul_nonneg (mul_nonneg (mul_nonneg (neg_nonneg.mpr (hOff i j hij))
        (le_of_lt (hv i))) (le_of_lt (hv j))) (sq_nonneg _)
  have hf : ∀ i, 0 ≤ f i := by
    intro i
    exact mul_nonneg (mul_nonneg (le_of_lt (hv i)) (hCv i)) (sq_nonneg _)
  have hE : 0 ≤ ∑ i, ∑ j, e i j := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => he i j
  have hF : 0 ≤ ∑ i, f i := Finset.sum_nonneg fun i _ => hf i
  have hformula : x ⬝ᵥ (C *ᵥ x) = (1 / 2 : ℝ) * (∑ i, ∑ j, e i j) + ∑ i, f i := by
    rw [hxw]
    exact harmonic_scaled_form C hSym v w
  by_contra hn
  have hE0 : (∑ i, ∑ j, e i j) = 0 := by linarith
  have hF0 : (∑ i, f i) = 0 := by linarith
  have hedge : ∀ i j, C i j < 0 → w i = w j := by
    intro i j hij
    have hsum0 : (∑ j, e i j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg fun j _ => he i j)).mp hE0 i (Finset.mem_univ i)
    have he0 : e i j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => he i j)).mp hsum0 j (Finset.mem_univ j)
    have hc : 0 < -C i j * v i * v j :=
      mul_pos (mul_pos (neg_pos.mpr hij) (hv i)) (hv j)
    have hs : (w i - w j)^2 = 0 := (mul_eq_zero.mp he0).resolve_left (ne_of_gt hc)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  obtain ⟨k, hk⟩ := hStrict
  have hfk : f k = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hf i)).mp hF0 k (Finset.mem_univ k)
  have hwk : w k = 0 := by
    have hc : 0 < v k * (C *ᵥ v) k := mul_pos (hv k) hk
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hfk).resolve_left (ne_of_gt hc))
  have hwzero : w = 0 := by
    funext i
    have hi : w i = w k := by
      induction hConn i k using Relation.ReflTransGen.head_induction_on with
      | refl => rfl
      | @head a b hab _ ih => exact (hedge a b hab).trans ih
    exact hi.trans hwk
  apply hx
  rw [hxw, hwzero, mul_zero]

end HarmonicArtin

end OAI
