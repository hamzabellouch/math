import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver

namespace OAI

namespace HarmonicArtin
universe u
variable {S : Type u}
open Matrix
open scoped Classical

theorem cartan_pairing_symm {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i) (c y : ι → ℝ) :
    c ⬝ᵥ (C *ᵥ y) = (C *ᵥ c) ⬝ᵥ y := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hSym j i]
  ring

theorem harmonic_null_boundary {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0) (I : Set ι)
    (c y : ι → ℝ) (hc : ∀ i ∈ I, 0 < c i) (hcOut : ∀ i ∉ I, c i = 0)
    (hcNull : ∀ i ∈ I, (C *ᵥ c) i = 0) (hy : ∀ i, 0 ≤ y i)
    (hpair : 0 ≤ c ⬝ᵥ (C *ᵥ y)) :
    c ⬝ᵥ (C *ᵥ y) = 0 ∧
      ∀ j ∉ I, (∃ i ∈ I, C i j < 0) → y j = 0 := by
  classical
  have hcNonneg (i : ι) : 0 ≤ c i := by
    by_cases hi : i ∈ I
    · exact (hc i hi).le
    · rw [hcOut i hi]
  have hterm (j : ι) (hj : j ∉ I) (i : ι) : C j i * c i ≤ 0 := by
    by_cases hji : j = i
    · subst i; rw [hcOut j hj, mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (hOff j i hji) (hcNonneg i)
  have hrow (j : ι) : (C *ᵥ c) j ≤ 0 := by
    by_cases hj : j ∈ I
    · rw [hcNull j hj]
    · exact Finset.sum_nonpos (fun i _ => hterm j hj i)
  have heq : c ⬝ᵥ (C *ᵥ y) = 0 := by
    apply le_antisymm _ hpair
    rw [cartan_pairing_symm C hSym c y]
    exact Finset.sum_nonpos fun j _ => mul_nonpos_of_nonpos_of_nonneg (hrow j) (hy j)
  refine ⟨heq, ?_⟩
  intro j hj ⟨i, hi, hij⟩
  have hneg : (C *ᵥ c) j < 0 := by
    apply Finset.sum_neg' (fun a _ => hterm j hj a)
    exact ⟨i, Finset.mem_univ _, mul_neg_of_neg_of_pos ((hSym i j) ▸ hij) (hc i hi)⟩
  rw [cartan_pairing_symm C hSym c y] at heq
  have hz : (C *ᵥ c) j * y j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos
      (fun a _ => mul_nonpos_of_nonpos_of_nonneg (hrow a) (hy a))).mp
        heq j (Finset.mem_univ _)
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_lt hneg)

theorem linear_zero_of_interior_convexHull {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : E →L[ℝ] ℝ) (V : Set E) (e : E)
    (he : e ∈ interior (convexHull ℝ V)) (hV : ∀ v ∈ V, L v ≤ L e) : L = 0 := by
  have hconv : Convex ℝ {v | L v ≤ L e} :=
    (convex_Iic (L e)).linear_preimage L.toLinearMap
  have hHull : ∀ v ∈ convexHull ℝ V, L v ≤ L e := convexHull_min hV hconv
  have hlocal : IsLocalMax L e :=
    (show IsMaxOn L (convexHull ℝ V) e from hHull).isLocalMax
      (mem_interior_iff_mem_nhds.mp he)
  exact hlocal.hasFDerivAt_eq_zero L.hasFDerivAt

theorem dotProduct_restrict_support {ι : Type*} [Fintype ι]
    (J : Set ι) (v z : ι → ℝ) (hOut : ∀ i ∉ J, v i = 0) :
    v ⬝ᵥ z = (fun i : J => v i) ⬝ᵥ (fun i : J => z i) := by
  classical
  change (∑ i, v i * z i) = _
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ J)]
  have hz : (∑ i : {i // i ∉ J}, v i * z i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hOut i i.property, zero_mul]
  rw [hz, add_zero]
  rfl

theorem harmonic_convex_separation {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0) (I J : Set ι)
    (c m y : ι → ℝ) (hc : ∀ i ∈ I, 0 < c i) (hcOut : ∀ i ∉ I, c i = 0)
    (hcNull : ∀ i ∈ I, (C *ᵥ c) i = 0) (hy : ∀ i, 0 ≤ y i)
    (hmOut : ∀ i ∉ J, m i = c i)
    (V : Set (J → ℝ))
    (he : (fun i : J => m i - c i) ∈ interior (convexHull ℝ V))
    (D h : ℝ) (hD : 0 < D) (hh : 0 ≤ h)
    (hV : ∀ s ∈ V, h ≤ D * (m ⬝ᵥ (C *ᵥ y) - s ⬝ᵥ (fun i : J => (C *ᵥ y) i))) :
    h = 0 ∧ c ⬝ᵥ (C *ᵥ y) = 0 ∧ m ⬝ᵥ (C *ᵥ y) = 0 ∧
      (∀ j ∈ J, (C *ᵥ y) j = 0) ∧
      (∀ j ∉ I, (∃ i ∈ I, C i j < 0) → y j = 0) := by
  classical
  let e : J → ℝ := fun i => m i - c i
  let L : (J → ℝ) →L[ℝ] ℝ := ∑ i : J, (C *ᵥ y) i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) i
  have hL (s : J → ℝ) : L s = s ⬝ᵥ (fun i : J => (C *ᵥ y) i) := by
    simp only [L, _root_.sum_apply, _root_.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have heval : L e = m ⬝ᵥ (C *ᵥ y) - c ⬝ᵥ (C *ᵥ y) := by
    rw [hL, ← sub_dotProduct]
    symm
    exact dotProduct_restrict_support J (m - c) (C *ᵥ y)
      (fun i hi => sub_eq_zero.mpr (hmOut i hi))
  have hbound (s : J → ℝ) (hs : s ∈ V) : L s ≤ m ⬝ᵥ (C *ᵥ y) - h / D := by
    have hhV := hV s hs
    rw [← hL] at hhV
    have hd : h / D ≤ m ⬝ᵥ (C *ᵥ y) - L s := by
      apply (div_le_iff₀ hD).mpr
      nlinarith
    linarith
  have hHull : ∀ s ∈ convexHull ℝ V, L s ≤ m ⬝ᵥ (C *ᵥ y) - h / D :=
    convexHull_min hbound ((convex_Iic _).linear_preimage L.toLinearMap)
  have heBound := hHull e (interior_subset he)
  rw [heval] at heBound
  have hpair : 0 ≤ c ⬝ᵥ (C *ᵥ y) := by
    have := div_nonneg hh hD.le
    linarith
  obtain ⟨hzero, hboundary⟩ := harmonic_null_boundary C hSym hOff I c y hc hcOut hcNull hy hpair
  have hhzero : h = 0 := by
    rw [hzero] at heBound
    have hdiv : h / D ≤ 0 := by linarith
    have : h ≤ 0 := by simpa only [zero_mul] using (div_le_iff₀ hD).mp hdiv
    exact le_antisymm this hh
  have hLe : L = 0 := by
    apply linear_zero_of_interior_convexHull L V e he
    intro s hs
    have h := hbound s hs
    rw [hhzero, zero_div, sub_zero] at h
    rw [heval, hzero, sub_zero]
    exact h
  have hrow : ∀ j ∈ J, (C *ᵥ y) j = 0 := by
    intro j hj
    have hz : L (Pi.single (⟨j, hj⟩ : J) 1) = 0 := by rw [hLe]; rfl
    simpa only [hL, single_dotProduct, one_mul] using hz
  have hmzero : m ⬝ᵥ (C *ᵥ y) = 0 := by
    have hz : L e = 0 := by rw [hLe]; rfl
    rw [heval, hzero, sub_zero] at hz
    exact hz
  exact ⟨hhzero, hzero, hmzero, hrow, hboundary⟩

end HarmonicArtin

end OAI
