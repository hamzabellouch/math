import Mathlib

namespace OAI

/-! Trace ideals, trace one from free field-valued points, adic unit lifting and degree bounds. -/

noncomputable section

namespace DescentExponents

universe u v

section AlgebraicTrace

variable (G : Type v) [Group G] [Fintype G]
variable (R : Type u) [CommRing R] [MulSemiringAction G R]

def groupTrace (r : R) : R := ∑ g : G, g • r

lemma groupTrace_fixed (r : R) (h : G) : h • groupTrace G R r = groupTrace G R r := by
  simp only [groupTrace, Finset.smul_sum, ← mul_smul]
  exact Equiv.sum_comp (Equiv.mulLeft h) (fun g : G => g • r)

def invariantTrace (r : R) : FixedPoints.subring R G :=
  ⟨groupTrace G R r, groupTrace_fixed G R r⟩

@[simp]
lemma invariantTrace_zero : invariantTrace G R 0 = 0 := by
  apply Subtype.ext
  simp [invariantTrace, groupTrace]

lemma invariantTrace_add (r s : R) :
    invariantTrace G R (r + s) = invariantTrace G R r + invariantTrace G R s := by
  apply Subtype.ext
  simp [invariantTrace, groupTrace, smul_add, Finset.sum_add_distrib]

lemma invariantTrace_mul (a : FixedPoints.subring R G) (r : R) :
    invariantTrace G R ((a : R) * r) = a * invariantTrace G R r := by
  apply Subtype.ext
  change (∑ g : G, g • ((a : R) * r)) = (a : R) * ∑ g : G, g • r
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [smul_mul', a.property g]

def traceIdeal : Ideal (FixedPoints.subring R G) where
  carrier := Set.range (invariantTrace G R)
  zero_mem' := ⟨0, invariantTrace_zero G R⟩
  add_mem' := by
    rintro _ _ ⟨r, rfl⟩ ⟨s, rfl⟩
    exact ⟨r + s, invariantTrace_add G R r s⟩
  smul_mem' := by
    rintro a _ ⟨r, rfl⟩
    exact ⟨(a : R) * r, invariantTrace_mul G R a r⟩

lemma trace_not_killed_by_free_point {Ω : Type u} [Field Ω] (x : R →+* Ω)
    (hfree : ∀ g : G, x.comp (MulSemiringAction.toRingHom G R g) = x → g = 1) :
    ∃ r : R, x (groupTrace G R r) ≠ 0 := by
  classical
  let χ : G → R →* Ω := fun g =>
    (x.comp (MulSemiringAction.toRingHom G R g)).toMonoidHom
  have hinj : Function.Injective χ := by
    intro a b hab
    have hcomp : x.comp (MulSemiringAction.toRingHom G R (a * b⁻¹)) = x := by
      ext r
      have h := congrArg (fun f : R →* Ω => f (b⁻¹ • r)) hab
      change x (a • (b⁻¹ • r)) = x (b • (b⁻¹ • r)) at h
      simpa only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply,
        mul_smul, smul_inv_smul] using h
    exact mul_inv_eq_one.mp (hfree (a * b⁻¹) hcomp)
  have hlin : LinearIndependent Ω (fun g : G => (χ g : R → Ω)) :=
    (linearIndependent_monoidHom R Ω).comp χ hinj
  by_contra! hzero
  have hsum : ∑ g : G, (1 : Ω) • (χ g : R → Ω) = 0 := by
    ext r
    simp only [Finset.sum_apply, one_smul, Pi.zero_apply]
    change (∑ g : G, x (g • r)) = 0
    simpa only [groupTrace, map_sum] using hzero r
  exact one_ne_zero (Fintype.linearIndependent_iff.mp hlin (fun _ => 1) hsum (1 : G))

theorem algebraic_trace_one
    (hfree : ∀ (Ω : Type u) [Field Ω] (x : R →+* Ω) (g : G),
      x.comp (MulSemiringAction.toRingHom G R g) = x → g = 1) :
    ∃ r : R, groupTrace G R r = 1 := by
  classical
  let A := FixedPoints.subring R G
  let : Algebra.IsInvariant A R G :=
    ⟨fun r hr => ⟨⟨r, hr⟩, rfl⟩⟩
  let : Algebra.IsIntegral A R := Algebra.IsInvariant.isIntegral A R G
  by_contra hn
  have hproper : traceIdeal G R ≠ ⊤ := by
    intro htop
    have hone : (1 : A) ∈ traceIdeal G R := by rw [htop]; trivial
    obtain ⟨r, hr⟩ := hone
    apply hn
    exact ⟨r, congrArg Subtype.val hr⟩
  obtain ⟨q, hq, htrace⟩ := Ideal.exists_le_maximal (traceIdeal G R) hproper
  let : q.IsMaximal := hq
  have hker : RingHom.ker (algebraMap A R) ≤ q := by
    have hinj : Function.Injective (algebraMap A R) := Subtype.val_injective
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  obtain ⟨P, hP, hcomap⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := R) q hker
  let : P.IsMaximal := hP
  let : Field (R ⧸ P) := Ideal.Quotient.field P
  let x : R →+* R ⧸ P := Ideal.Quotient.mk P
  obtain ⟨r, hr⟩ := trace_not_killed_by_free_point G R x (hfree (R ⧸ P) x)
  apply hr
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have ht : invariantTrace G R r ∈ q := htrace ⟨r, rfl⟩
  rw [← hcomap] at ht
  exact ht

end AlgebraicTrace

section AdicLifting

variable (G : Type v) [Group G] [Fintype G]
variable (R : Type u) [CommRing R] [MulSemiringAction G R]

lemma map_groupTrace {S : Type*} [CommRing S] [MulSemiringAction G S]
    (f : R →+* S) (hequiv : ∀ (g : G) (r : R), f (g • r) = g • f r)
    (r : R) : f (groupTrace G R r) = groupTrace G S (f r) := by
  simp only [groupTrace, map_sum, hequiv]

theorem unit_trace_of_complete_target
    (I : Ideal R) [MulSemiringAction G (R ⧸ I)]
    (hequiv : ∀ (g : G) (r : R),
      Ideal.Quotient.mk I (g • r) = g • Ideal.Quotient.mk I r)
    (hfree : ∀ (Ω : Type u) [Field Ω] (x : (R ⧸ I) →+* Ω) (g : G),
      x.comp (MulSemiringAction.toRingHom G (R ⧸ I) g) = x → g = 1)
    {S : Type*} [CommRing S] (f : R →+* S)
    (J : Ideal S) [IsAdicComplete J S]
    (hIJ : I ≤ J.comap f) :
    ∃ z : R, IsUnit (f (groupTrace G R z)) := by
  obtain ⟨zbar, hzbar⟩ := algebraic_trace_one G (R ⧸ I) hfree
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective zbar
  refine ⟨z, Ideal.isUnit_of_sub_one_mem_jacobson_bot _ ?_⟩
  apply IsAdicComplete.le_jacobson_bot J
  have hmod : Ideal.Quotient.mk I (groupTrace G R z) = 1 := by
    rw [map_groupTrace G R (Ideal.Quotient.mk I) hequiv, hz, hzbar]
  have hmem : groupTrace G R z - 1 ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hmod, map_one, sub_self]
  simpa only [Ideal.mem_comap, map_sub, map_one] using hIJ hmem

end AdicLifting

section DegreeArithmetic

lemma exponent_page_bound (p : ℕ) (hp : 5 ≤ p) :
    p ^ 2 + 2 < 2 * (p - 1) ^ 2 + 1 := by
  have hsub : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  nlinarith [sq_nonneg (p - 1 - 2 : ℤ)]

lemma exists_obstruction_power (p : ℕ) (hp : 5 ≤ p) :
    ∃ N : ℕ, 0 < N ∧ p ∣ N ∧ p ^ 2 + 2 < 2 * N := by
  refine ⟨p * (p + 1), by positivity, dvd_mul_right p (p + 1), ?_⟩
  nlinarith

lemma exponent_page_bound_int (p : ℤ) (hp : 5 ≤ p) :
    p ^ 2 + 2 < 2 * (p - 1) ^ 2 + 1 := by
  nlinarith [sq_nonneg (p - 5)]

lemma differential_index_range (p a r : ℤ) (hp : 5 ≤ p)
    (hr₂ : 2 ≤ r) (hrm : r ≤ p ^ 2 + 2)
    (hr : r = 2 * (p - 1) * a + 1) : 1 ≤ a ∧ a < p - 1 := by
  have ht : 0 < p - 1 := by omega
  have ha : 1 ≤ a := by
    by_contra h
    have : a ≤ 0 := by omega
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht) this]
  refine ⟨ha, ?_⟩
  by_contra h
  have : 0 ≤ (p - 1) * (a - (p - 1)) :=
    mul_nonneg (le_of_lt ht) (by omega)
  nlinarith [exponent_page_bound_int p hp]

lemma outgoing_degree_equation (p a l : ℤ) (hp : 5 ≤ p)
    (ha : 1 ≤ a) (hat : a < p - 1)
    (heq : a - 1 = p * (p - 1) * (a + l)) : a = 1 := by
  have hdiv : p * (p - 1) ∣ a - 1 := ⟨a + l, heq⟩
  have hsmall : a - 1 < p * (p - 1) := by nlinarith
  have := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) hsmall hdiv
  omega

lemma incoming_degree_equation (p a l : ℤ) (hp : 5 ≤ p)
    (ha : 1 ≤ a) (hat : a < p - 1) :
    a - (p - 1) ≠ p * (p - 1) * (a - l) := by
  intro heq
  have hdiv : p * (p - 1) ∣ (p - 1) - a := by
    refine ⟨l - a, ?_⟩
    linear_combination -heq
  have hsmall : (p - 1) - a < p * (p - 1) := by nlinarith
  have := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) hsmall hdiv
  omega

end DegreeArithmetic

end DescentExponents

end

end OAI
