import Mathlib

namespace OAI

/-! Invariant products from convex relations among integral characters. -/

noncomputable section
open scoped BigOperators

namespace ExactOrders.Partial

def realVector {δ : Type*} (p : δ → ℚ) : δ → ℝ := fun j => p j

lemma rational_barycentric_coordinates
    {ι δ : Type*} [Fintype ι] [Fintype δ]
    (p : ι → δ → ℚ) (w : ι → ℝ)
    (hp : AffineIndependent ℝ (fun i => realVector (p i)))
    (hw : ∑ i, w i = 1)
    (hz : ∑ i, w i • realVector (p i) = 0) :
    ∃ q : ι → ℚ, ∀ i, (q i : ℝ) = w i := by
  classical
  let u : ι → Option δ → ℚ := fun i j => j.elim 1 (p i)
  let A : (ι → ℚ) →ₗ[ℚ] (Option δ → ℚ) :=
    { toFun := fun a => ∑ i, a i • u i
      map_add' := by
        intro a b
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        simp [Finset.smul_sum, mul_smul] }
  have hker : LinearMap.ker A = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro a ha
    have hsum : ∑ i, (a i : ℝ) = 0 := by
      have h := congrFun ha none
      simp only [A, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, u, Option.elim_none, mul_one, Pi.zero_apply] at h
      exact_mod_cast h
    have hlin : ∑ i, (a i : ℝ) • realVector (p i) = 0 := by
      ext j
      have h := congrFun ha (some j)
      simp only [A, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, u, Option.elim_some, Pi.zero_apply] at h
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        realVector, Pi.zero_apply]
      exact_mod_cast h
    have hzero := hp.eq_zero_of_sum_eq_zero hsum hlin
    ext i
    exact_mod_cast hzero i (Finset.mem_univ i)
  obtain ⟨B, hBA⟩ := A.exists_leftInverse_of_injective hker
  let e : Option δ → Option δ → ℚ := fun j k => if j = k then 1 else 0
  have hBu (k : ι) : B (u k) = fun i => if k = i then 1 else 0 := by
    have h := LinearMap.congr_fun hBA (fun i => if k = i then 1 else 0)
    simpa [A] using h
  have hcoef (k i : ι) :
      ∑ j, (u k j : ℝ) * (B (e j) i : ℝ) = if k = i then 1 else 0 := by
    have h := congrFun (hBu k) i
    rw [B.pi_apply_eq_sum_univ] at h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    by_cases hki : k = i <;>
      simpa [e, hki] using congrArg (fun x : ℚ => (x : ℝ)) h
  have haug (j : Option δ) :
      (e none j : ℝ) = ∑ k, w k * (u k j : ℝ) := by
    cases j with
    | none => simpa [e, u] using hw.symm
    | some j =>
      have h := congrFun hz j
      simpa [e, u, realVector] using h.symm
  refine ⟨B (e none), fun i => ?_⟩
  calc
    (B (e none) i : ℝ) = ∑ j, (e none j : ℝ) * (B (e j) i : ℝ) := by
      simp [e]
    _ = ∑ j, (∑ k, w k * (u k j : ℝ)) * (B (e j) i : ℝ) := by
      simp_rw [haug]
    _ = ∑ k, w k * (∑ j, (u k j : ℝ) * (B (e j) i : ℝ)) := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
    _ = ∑ k, w k * (if k = i then 1 else 0) := by simp_rw [hcoef]
    _ = w i := by simp

theorem zero_mem_rational_convexHull
    {δ : Type*} [Fintype δ] (s : Set (δ → ℚ))
    (h : (0 : δ → ℝ) ∈ convexHull ℝ (realVector '' s)) :
    (0 : δ → ℚ) ∈ convexHull ℚ s := by
  classical
  obtain ⟨ι, _, z, w, hzs, hz, hwpos, hw, hwz⟩ :=
    eq_pos_convex_span_of_mem_convexHull h
  have hpre : ∀ i, ∃ p ∈ s, realVector p = z i :=
    fun i => hzs ⟨i, rfl⟩
  choose p hps hpz using hpre
  have hpz' : (fun i => realVector (p i)) = z := funext hpz
  rw [← hpz'] at hz hwz
  obtain ⟨q, hq⟩ := rational_barycentric_coordinates p w hz hw hwz
  apply mem_convexHull_of_exists_fintype q p
  · intro i
    have : 0 < (q i : ℝ) := by rw [hq]; exact hwpos i
    exact_mod_cast this.le
  · have : ∑ i, (q i : ℝ) = 1 := by simp_rw [hq]; exact hw
    exact_mod_cast this
  · exact hps
  · ext j
    have h := congrFun hwz j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, realVector,
      Pi.zero_apply] at h ⊢
    simp_rw [← hq] at h
    exact_mod_cast h

lemma natural_common_denominator
    {ι : Type*} [Fintype ι] (a : ι → ℚ) (ha : ∀ i, 0 ≤ a i) :
    ∃ d : ℕ, 0 < d ∧ ∃ n : ι → ℕ, ∀ i, (n i : ℚ) = d * a i := by
  classical
  let d := ∏ i, (a i).den
  let n : ι → ℕ := fun i => (a i).num.toNat *
    ∏ j ∈ Finset.univ.erase i, (a j).den
  refine ⟨d, Finset.prod_pos (fun i _ => (a i).den_pos), n, fun i => ?_⟩
  have hnum : ((a i).num.toNat : ℚ) = (a i).num := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (ha i))
  have hd : (a i).den * (∏ j ∈ Finset.univ.erase i, (a j).den) = d :=
    Finset.mul_prod_erase Finset.univ (fun j => (a j).den) (Finset.mem_univ i)
  calc
    (n i : ℚ) = (a i).num * (∏ j ∈ Finset.univ.erase i, (a j).den : ℕ) := by
      simp only [n, Nat.cast_mul, hnum]
    _ = (a i * (a i).den) * (∏ j ∈ Finset.univ.erase i, (a j).den : ℕ) := by
      rw [Rat.mul_den_eq_num]
    _ = a i * ((a i).den * (∏ j ∈ Finset.univ.erase i, (a j).den) : ℕ) := by
      push_cast
      ring
    _ = d * a i := by rw [hd, mul_comm]

lemma integral_weight_relation
    {ι δ : Type*} [Fintype ι]
    (r : ι → ℕ) (α : ι → δ → ℤ) (c : ι → ℚ)
    (hr : ∀ i, 0 < r i) (hc : ∀ i, 0 ≤ c i)
    (hc1 : ∑ i, c i = 1)
    (hzero : ∑ i, c i • (fun j => (α i j : ℚ) / r i) = 0) :
    ∃ n : ι → ℕ, 0 < ∑ i, n i * r i ∧ ∑ i, n i • α i = 0 := by
  classical
  let a : ι → ℚ := fun i => c i / r i
  have hri (i : ι) : (r i : ℚ) ≠ 0 := by exact_mod_cast (hr i).ne'
  obtain ⟨d, hd, n, hn⟩ := natural_common_denominator a
    (fun i => div_nonneg (hc i) (by positivity))
  have hdeg : (∑ i, n i * r i : ℕ) = d := by
    apply Nat.cast_injective (R := ℚ)
    push_cast
    calc
      ∑ i, (n i : ℚ) * r i = ∑ i, (d : ℚ) * c i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hn]
        dsimp [a]
        field_simp [hri i]
      _ = d := by rw [← Finset.mul_sum, hc1, mul_one]
  refine ⟨n, hdeg ▸ hd, ?_⟩
  ext j
  have hz := congrFun hzero j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hz
  have hsum : ∑ i, (n i : ℚ) * (α i j : ℚ) = 0 := by
    calc
      ∑ i, (n i : ℚ) * (α i j : ℚ) =
          ∑ i, (d : ℚ) * (c i * ((α i j : ℚ) / r i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hn]
        dsimp [a]
        ring
      _ = 0 := by rw [← Finset.mul_sum, hz, mul_zero]
  simpa only [Finset.sum_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply,
    Pi.zero_apply, Pi.natCast_apply] using
    (show ∑ i, (n i : ℤ) * α i j = 0 by exact_mod_cast hsum)

def character {δ : Type*} [Fintype δ] (α : δ → ℤ) : (δ → ℂˣ) →* ℂˣ where
  toFun t := ∏ j, t j ^ α j
  map_one' := by simp
  map_mul' t u := by simp [mul_zpow, Finset.prod_mul_distrib]

@[simp] lemma character_zero {δ : Type*} [Fintype δ] (t : δ → ℂˣ) :
    character (0 : δ → ℤ) t = 1 := by
  simp [character]

lemma character_add {δ : Type*} [Fintype δ] (α β : δ → ℤ) (t : δ → ℂˣ) :
    character (α + β) t = character α t * character β t := by
  simp [character, zpow_add, Finset.prod_mul_distrib]

lemma character_nsmul {δ : Type*} [Fintype δ]
    (n : ℕ) (α : δ → ℤ) (t : δ → ℂˣ) :
    character (n • α) t = character α t ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, character_add, ih, pow_succ]

lemma character_sum {ι δ : Type*} [Fintype δ]
    (F : Finset ι) (α : ι → δ → ℤ) (t : δ → ℂˣ) :
    character (∑ i ∈ F, α i) t = ∏ i ∈ F, character (α i) t := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih => simp only [Finset.sum_insert hi, character_add, ih,
      Finset.prod_insert hi]

theorem invariant_product_of_integral_relation
    {ι δ R : Type*} [Fintype ι] [Fintype δ]
    [CommRing R] [IsDomain R] [Algebra ℂ R]
    (A : ℕ → Submodule ℂ R) [SetLike.GradedMonoid A]
    (ρ : (δ → ℂˣ) →* (R ≃ₐ[ℂ] R))
    (r : ι → ℕ) (α : ι → δ → ℤ) (s : ι → R)
    (hmem : ∀ i, s i ∈ A (r i)) (hne : ∀ i, s i ≠ 0)
    (heigen : ∀ t i, ρ t (s i) = (character (α i) t : ℂ) • s i)
    (n : ι → ℕ) (hdeg : 0 < ∑ i, n i * r i)
    (hweight : ∑ i, n i • α i = 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ z : R, z ∈ A m ∧ z ≠ 0 ∧ ∀ t, ρ t z = z := by
  classical
  refine ⟨∑ i, n i * r i, hdeg, ∏ i, s i ^ n i, ?_, ?_, ?_⟩
  · simpa only [Nat.nsmul_eq_mul] using
      (SetLike.prod_pow_mem_graded A r s n (fun i _ => hmem i))
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hne i))
  · intro t
    have hchar : ∏ i, character (α i) t ^ n i = 1 := by
      rw [← character_zero t, ← hweight, character_sum]
      simp_rw [character_nsmul]
    have hscalar : ∏ i, (character (α i) t : ℂ) ^ n i = 1 := by
      have h := congrArg (Units.coeHom ℂ) hchar
      simpa only [map_prod, map_pow, map_one, Units.coeHom_apply] using h
    calc
      ρ t (∏ i, s i ^ n i) = ∏ i, (ρ t (s i)) ^ n i := by simp only [map_prod, map_pow]
      _ = ∏ i, ((character (α i) t : ℂ) • s i) ^ n i := by simp_rw [heigen]
      _ = (∏ i, (character (α i) t : ℂ) ^ n i) • ∏ i, s i ^ n i := by
        simp only [smul_pow, Finset.prod_smul]
      _ = ∏ i, s i ^ n i := by rw [hscalar, one_smul]

theorem invariant_of_zero_mem_convexHull
    {κ δ R : Type*} [Fintype δ]
    [CommRing R] [IsDomain R] [Algebra ℂ R]
    (A : ℕ → Submodule ℂ R) [SetLike.GradedMonoid A]
    (ρ : (δ → ℂˣ) →* (R ≃ₐ[ℂ] R))
    (r : κ → ℕ) (α : κ → δ → ℤ) (s : κ → R)
    (hr : ∀ i, 0 < r i)
    (hmem : ∀ i, s i ∈ A (r i)) (hne : ∀ i, s i ≠ 0)
    (heigen : ∀ t i, ρ t (s i) = (character (α i) t : ℂ) • s i)
    (hconvex : (0 : δ → ℝ) ∈ convexHull ℝ
      (Set.range (fun i j => (α i j : ℝ) / r i))) :
    ∃ m : ℕ, 0 < m ∧ ∃ z : R, z ∈ A m ∧ z ≠ 0 ∧ ∀ t, ρ t z = z := by
  classical
  let p : κ → δ → ℚ := fun i j => (α i j : ℚ) / r i
  have hrat : (0 : δ → ℚ) ∈ convexHull ℚ (Set.range p) := by
    apply zero_mem_rational_convexHull
    rw [← Set.range_comp']
    change (0 : δ → ℝ) ∈ convexHull ℝ
      (Set.range (fun i j => (((α i j : ℚ) / r i : ℚ) : ℝ)))
    simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using hconvex
  obtain ⟨ι, _, c, q, hc, hc1, hq, hzero⟩ :=
    mem_convexHull_iff_exists_fintype.mp hrat
  choose f hf using hq
  have hzero' : ∑ i, c i • (fun j => (α (f i) j : ℚ) / r (f i)) = 0 := by
    simpa only [← hf, p] using hzero
  obtain ⟨n, hn, hα⟩ := integral_weight_relation (r ∘ f) (α ∘ f) c
    (fun i => hr (f i)) hc hc1 hzero'
  exact invariant_product_of_integral_relation A ρ (r ∘ f) (α ∘ f) (s ∘ f)
    (fun i => hmem (f i)) (fun i => hne (f i)) (fun t i => heigen t (f i)) n hn hα

end ExactOrders.Partial

end

end OAI
