import Mathlib

namespace OAI

namespace HarmonicArtin
namespace NullBoundary

open scoped Matrix Classical
open Set Filter

lemma continuousLinearMap_eq_zero_of_interior_max
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E →L[ℝ] ℝ) (s : Set E) {x : E}
    (hx : x ∈ interior s) (hmax : ∀ y ∈ s, f y ≤ f x) : f = 0 := by
  have hlocal : IsLocalMax f x := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hx] with y hy
    exact hmax y hy
  simpa only [f.fderiv] using hlocal.fderiv_eq_zero

variable {V : Type*}

noncomputable def extend (J : Set V) (s : J → ℝ) : V → ℝ := by
  classical
  exact fun i => if hi : i ∈ J then s ⟨i, hi⟩ else 0

@[simp] lemma extend_apply_mem (J : Set V) (s : J → ℝ) (i : J) :
    extend J s i = s i := by
  classical
  simp [extend, i.property]

@[simp] lemma extend_apply_not_mem (J : Set V) (s : J → ℝ) (i : V) (hi : i ∉ J) :
    extend J s i = 0 := by
  classical
  simp [extend, hi]

lemma extend_restrict (J : Set V) (v : V → ℝ) (hv : ∀ i ∉ J, v i = 0) :
    extend J (fun i => v i) = v := by
  classical
  funext i
  by_cases hi : i ∈ J
  · simp [extend, hi]
  · simp [extend, hi, hv i hi]

variable [Fintype V]

lemma extend_dot (J : Set V) (s : J → ℝ) (v : V → ℝ) :
    extend J s ⬝ᵥ v = ∑ j : J, s j * v j := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ J)
    (fun i => extend J s i * v i)
  have hc : (∑ i : {x // x ∉ J}, extend J s i * v i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [extend, i.property]
  simpa only [dotProduct, extend_apply_mem, hc, add_zero] using h.symm

noncomputable def coordFunctional (J : Set V) (v : V → ℝ) : (J → ℝ) →L[ℝ] ℝ :=
  ∑ j : J, (ContinuousLinearMap.proj j).smulRight (v j)

lemma coordFunctional_apply (J : Set V) (v : V → ℝ) (s : J → ℝ) :
    coordFunctional J v s = extend J s ⬝ᵥ v := by
  classical
  simp [coordFunctional, extend_dot, mul_comm]

lemma null_mulVec_nonpos (C : Matrix V V ℝ) (I : Set V) (c : V → ℝ)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (hc : ∀ i, 0 ≤ c i) (hsupp : ∀ i ∉ I, c i = 0)
    (hnull : ∀ i ∈ I, (C *ᵥ c) i = 0) : ∀ i, (C *ᵥ c) i ≤ 0 := by
  intro i
  by_cases hi : i ∈ I
  · exact le_of_eq (hnull i hi)
  · apply Finset.sum_nonpos
    intro j _
    by_cases hij : i = j
    · subst j; simp [hsupp i hi]
    · exact mul_nonpos_of_nonpos_of_nonneg (hOff i j hij) (hc j)

lemma null_pairing_nonpos (C : Matrix V V ℝ) (I : Set V) (c y : V → ℝ)
    (hSym : ∀ i j, C i j = C j i) (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (hc : ∀ i, 0 ≤ c i) (hsupp : ∀ i ∉ I, c i = 0)
    (hnull : ∀ i ∈ I, (C *ᵥ c) i = 0) (hy : ∀ i, 0 ≤ y i) :
    c ⬝ᵥ (C *ᵥ y) ≤ 0 := by
  have hCt : C.transpose = C := by ext i j; exact hSym j i
  rw [← hCt, Matrix.dotProduct_transpose_mulVec]
  exact Finset.sum_nonpos fun i _ =>
    mul_nonpos_of_nonneg_of_nonpos (hy i) (null_mulVec_nonpos C I c hOff hc hsupp hnull i)

lemma null_pairing_eq_zero_boundary (C : Matrix V V ℝ) (I : Set V) (c y : V → ℝ)
    (hSym : ∀ i j, C i j = C j i) (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (hc : ∀ i, 0 ≤ c i) (hsupp : ∀ i ∉ I, c i = 0)
    (hpos : ∀ i ∈ I, 0 < c i)
    (hnull : ∀ i ∈ I, (C *ᵥ c) i = 0) (hy : ∀ i, 0 ≤ y i)
    (heq : c ⬝ᵥ (C *ᵥ y) = 0) :
    ∀ a ∉ I, (∃ i ∈ I, C a i < 0) → y a = 0 := by
  intro a ha ⟨i, hi, hai⟩
  have hn := null_mulVec_nonpos C I c hOff hc hsupp hnull
  have haz : (C *ᵥ c) a < 0 := by
    apply Finset.sum_neg'
    · intro j _
      by_cases haj : a = j
      · subst j; simp [hsupp a ha]
      · exact mul_nonpos_of_nonpos_of_nonneg (hOff a j haj) (hc j)
    · exact ⟨i, Finset.mem_univ _, mul_neg_of_neg_of_pos hai (hpos i hi)⟩
  have hs : y ⬝ᵥ (C *ᵥ c) = 0 := by
    have hCt : C.transpose = C := by ext i j; exact hSym j i
    simpa only [hCt] using (Matrix.dotProduct_transpose_mulVec C y c).trans heq
  have hz : y a * (C *ᵥ c) a = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos (fun j _ =>
      mul_nonpos_of_nonneg_of_nonpos (hy j) (hn j))).mp hs a (Finset.mem_univ _)
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_lt haz)

lemma convexHull_bound (J : Set V) (m r : V → ℝ) (B : Set (J → ℝ)) (a : ℝ)
    (hb : ∀ s ∈ B, a ≤ (m - extend J s) ⬝ᵥ r) :
    ∀ s ∈ convexHull ℝ B, a ≤ (m - extend J s) ⬝ᵥ r := by
  let f := coordFunctional J r
  have hs : B ⊆ f ⁻¹' Iic (m ⬝ᵥ r - a) := by
    intro s hs
    have h := hb s hs
    change f s ≤ m ⬝ᵥ r - a
    dsimp [f]
    rw [coordFunctional_apply]
    rw [sub_dotProduct] at h
    linarith
  have hc := convexHull_min hs ((convex_Iic (m ⬝ᵥ r - a)).linear_preimage f.toLinearMap)
  intro s hs
  have h := hc hs
  change f s ≤ m ⬝ᵥ r - a at h
  dsimp [f] at h
  rw [coordFunctional_apply] at h
  rw [sub_dotProduct]
  linarith

theorem convex_null_boundary_separation
    (C : Matrix V V ℝ) (I J : Set V) (c m y : V → ℝ) (B : Set (J → ℝ)) (a : ℝ)
    (hSym : ∀ i j, C i j = C j i) (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (hc : ∀ i, 0 ≤ c i) (hsupp : ∀ i ∉ I, c i = 0)
    (hpos : ∀ i ∈ I, 0 < c i)
    (hnull : ∀ i ∈ I, (C *ᵥ c) i = 0) (hy : ∀ i, 0 ≤ y i)
    (hext : ∀ i ∉ J, m i = c i)
    (he : (fun j : J => m j - c j) ∈ interior (convexHull ℝ B))
    (ha : 0 ≤ a) (hb : ∀ s ∈ B, a ≤ (m - extend J s) ⬝ᵥ (C *ᵥ y)) :
    (∀ b ∉ I, (∃ i ∈ I, C b i < 0) → y b = 0) ∧
    (∀ j ∈ J, (C *ᵥ y) j = 0) ∧ a = 0 ∧ m ⬝ᵥ (C *ᵥ y) = 0 := by
  let e : J → ℝ := fun j => m j - c j
  have hex : extend J e = m - c :=
    extend_restrict J (m-c) (fun i hi => by simp [hext i hi])
  have hbound := convexHull_bound J m (C *ᵥ y) B a hb
  have havg : a ≤ c ⬝ᵥ (C *ᵥ y) := by
    have h := hbound e (interior_subset he)
    simpa only [hex, sub_sub_cancel] using h
  have hsign := null_pairing_nonpos C I c y hSym hOff hc hsupp hnull hy
  have hzero : c ⬝ᵥ (C *ᵥ y) = 0 := le_antisymm hsign (ha.trans havg)
  have haz : a = 0 := le_antisymm (by linarith) ha
  have hmax : ∀ s ∈ convexHull ℝ B,
      coordFunctional J (C *ᵥ y) s ≤ coordFunctional J (C *ᵥ y) e := by
    intro s hs
    have h := hbound s hs
    rw [haz, sub_dotProduct] at h
    rw [coordFunctional_apply, coordFunctional_apply, hex, sub_dotProduct, hzero, sub_zero]
    linarith
  have hfzero := continuousLinearMap_eq_zero_of_interior_max
    (coordFunctional J (C *ᵥ y)) (convexHull ℝ B) he hmax
  refine ⟨null_pairing_eq_zero_boundary C I c y hSym hOff hc hsupp hpos hnull hy hzero,
    ?_, haz, ?_⟩
  · intro j hj
    have h := congrArg (fun f : (J → ℝ) →L[ℝ] ℝ => f (Pi.single ⟨j, hj⟩ 1)) hfzero
    simpa [coordFunctional, Pi.single_apply] using h
  · have h := congrArg (fun f : (J → ℝ) →L[ℝ] ℝ => f e) hfzero
    rw [coordFunctional_apply, hex, sub_dotProduct, hzero] at h
    simpa using h

end NullBoundary
end HarmonicArtin

end OAI
