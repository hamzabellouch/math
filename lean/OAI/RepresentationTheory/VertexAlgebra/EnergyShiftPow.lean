import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.BlockGrowth
import OAI.RepresentationTheory.VertexAlgebra.VirasoroLinearEnergy

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U
theorem energyShift_pow_norm_mono {k l : ℕ} (hkl : k ≤ l) (b : V) :
    ‖(A.energyShift^k) b‖ ≤ ‖(A.energyShift^l) b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [U.energy_norm_sq_eq_sum_grades, U.energy_norm_sq_eq_sum_grades]
  apply Finset.sum_le_sum
  intro d _
  apply pow_le_pow_left₀ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg d)) hkl

theorem energyBound_add {a b : V} (ha : A.PolynomialEnergyBound a)
    (hb : A.PolynomialEnergyBound b) : A.PolynomialEnergyBound (a + b) := by
  obtain ⟨C, hC, p, k, hp⟩ := ha
  obtain ⟨D, hD, q, l, hq⟩ := hb
  refine ⟨C + D, add_pos hC hD, p + q, k + l, ?_⟩
  intro n c
  have hbase : 1 ≤ 1 + |(n : ℝ)| := le_add_of_nonneg_right (abs_nonneg _)
  have hpp : (1 + |(n : ℝ)|)^p ≤ (1 + |(n : ℝ)|)^(p + q) :=
    pow_le_pow_right₀ hbase (by omega)
  have hqq : (1 + |(n : ℝ)|)^q ≤ (1 + |(n : ℝ)|)^(p + q) :=
    pow_le_pow_right₀ hbase (by omega)
  have hkk := U.energyShift_pow_norm_mono (show k ≤ k + l by omega) c
  have hll := U.energyShift_pow_norm_mono (show l ≤ k + l by omega) c
  rw [mode_add, LinearMap.add_apply]
  calc
    _ ≤ ‖mode A.fields a n c‖ + ‖mode A.fields b n c‖ := norm_add_le _ _
    _ ≤ C * (1 + |(n : ℝ)|)^p * ‖(A.energyShift^k) c‖ +
          D * (1 + |(n : ℝ)|)^q * ‖(A.energyShift^l) c‖ := add_le_add (hp n c) (hq n c)
    _ ≤ C * (1 + |(n : ℝ)|)^(p + q) * ‖(A.energyShift^(k + l)) c‖ +
          D * (1 + |(n : ℝ)|)^(p + q) * ‖(A.energyShift^(k + l)) c‖ := by gcongr
    _ = _ := by ring

 

theorem polynomialEnergyBounds (hc : A.toVertexAlgebra.C2Cofinite) : A.PolynomialEnergyBounds := by
  obtain ⟨D, hD, S, _, hS, H⟩ := U.exists_generatorMajorant hc
  obtain ⟨C, hC, p, hp⟩ := U.generatorMajorant_polynomial D hD S hS H
  have hB := A.one_le_generatorMajorant D S
  have hhom (d : ℕ) (a : V) (ha : a ∈ A.grade d) : A.PolynomialEnergyBound a := by
    obtain ⟨K, hK, q, hq⟩ := H d a ha
    apply U.energyBound_of_polynomial_blocks ha
    refine ⟨K * C^d, by positivity, q + p * d, ?_⟩
    intro N
    apply A.blockControl_mono (hq N)
    have hBN : 0 ≤ A.generatorMajorant D S N := zero_le_one.trans (hB N)
    calc
      _ ≤ K * (1 + (N : ℝ))^q * (C * (1 + (N : ℝ))^p)^d := by gcongr; exact hp N
      _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring
  intro a
  exact A.homogeneous_induction (P := A.PolynomialEnergyBound)
    (hhom 0 0 (Submodule.zero_mem _)) hhom (fun _ _ => U.energyBound_add) a

 

theorem grade_le_generatorFiltration (D : ℕ) (S : ℕ → Set V)
    (hS : ∀ d, 1 ≤ d → d ≤ D → ∀ a ∈ A.grade d, A.IsQuasiPrimary a →
      a ∈ Submodule.span ℂ (S d))
    (hcut : ∀ d, D < d → A.grade d ≤ A.toVertexAlgebra.c2) :
    ∀ d, A.grade d ≤ A.generatorFiltration S d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro a ha
    have hc2 := A.homogeneousC2_le_generatorFiltration d ih
    by_cases hd0 : d = 0
    · subst d
      rw [A.grade_zero] at ha
      obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp ha
      exact Submodule.smul_mem _ z (A.vacuum_mem_generatorFiltration S 0)
    by_cases hdD : d ≤ D
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
      obtain ⟨q, hq, hqq, b, hb, hab⟩ := U.quasiPrimary_decomposition ha
      rw [hab]
      apply Submodule.add_mem
      · have hle : Submodule.span ℂ (S (e + 1)) ≤ A.generatorFiltration S (e + 1) := by
          apply Submodule.span_le.mpr
          intro x hx
          change x ∈ A.generatorFiltration S (e + 1)
          have h := A.generator_mode_mem hx (A.vacuum_mem_generatorFiltration S 0) (-1)
          simpa only [A.creation, Nat.add_zero] using h
        exact hle (hS (e + 1) (by omega) hdD q hq hqq)
      · exact A.generatorFiltration_mono S (by omega : e ≤ e + 1)
          (A.translation_mem_generatorFiltration (ih e (by omega) hb))
    · have hc : a ∈ A.homogeneousC2 d := by
        rw [A.homogeneousC2_eq]
        exact ⟨hcut d (by omega) ha, ha⟩
      exact A.generatorFiltration_mono S (Nat.sub_le d 1) (hc2 hc)

 

theorem c2_grade_le_generatorFiltration (D : ℕ) (S : ℕ → Set V)
    (hS : ∀ d, 1 ≤ d → d ≤ D → ∀ a ∈ A.grade d, A.IsQuasiPrimary a →
      a ∈ Submodule.span ℂ (S d))
    (hcut : ∀ d, D < d → A.grade d ≤ A.toVertexAlgebra.c2) (d : ℕ) :
    A.toVertexAlgebra.c2 ⊓ A.grade d ≤ A.generatorFiltration S (d - 1) := by
  rw [← A.homogeneousC2_eq]
  exact A.homogeneousC2_le_generatorFiltration d
    (fun e _ => U.grade_le_generatorFiltration D S hS hcut e)

 

theorem exists_energy_generating_filtration (hc : A.toVertexAlgebra.C2Cofinite) :
    ∃ D : ℕ, 2 ≤ D ∧ ∃ S : ℕ → Finset V,
      (∀ d, d = 0 ∨ D < d → S d = ∅) ∧
      (∀ d, ∀ a ∈ S d, 1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧
        A.IsQuasiPrimary a ∧ U.IsHermitian d a) ∧
      (∀ w, A.grade w ≤ A.homogeneousNegativeFiltration (fun d => (S d : Set V)) w w) ∧
      (∀ w, A.toVertexAlgebra.c2 ⊓ A.grade w ≤
        A.homogeneousNegativeFiltration (fun d => (S d : Set V)) (w - 1) w) := by
  classical
  obtain ⟨D, hD, hcut⟩ := A.exists_c2_weight_cutoff hc
  choose R hR hspan using U.exists_hermitian_quasiPrimary_spanning
  let S : ℕ → Finset V := fun d => if 1 ≤ d ∧ d ≤ D then R d else ∅
  let T : ℕ → Set V := fun d => (S d : Set V)
  have hS (d : ℕ) (a : V) (ha : a ∈ S d) :
      1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧ A.IsQuasiPrimary a ∧ U.IsHermitian d a := by
    dsimp only [S] at ha
    split_ifs at ha with hd
    · exact ⟨hd.1, hd.2, hR d a ha⟩
    · simp at ha
  have hGT : ∀ d, ∀ a ∈ T d, 1 ≤ d ∧ a ∈ A.grade d := by
    intro d a ha
    have h := hS d a ha
    exact ⟨h.1, h.2.2.1⟩
  have hT : ∀ d, ∀ a ∈ T d, a ∈ A.grade d := fun d a ha => (hGT d a ha).2
  have hQ : ∀ d, 1 ≤ d → d ≤ D → ∀ a ∈ A.grade d, A.IsQuasiPrimary a →
      a ∈ Submodule.span ℂ (T d) := by
    intro d hd hD a ha hq
    have he : T d = (R d : Set V) := by dsimp [T, S]; rw [ite_eq_left ⟨hd, hD⟩]
    rw [he]
    exact hspan d a ha hq
  have hgen := U.grade_le_generatorFiltration D T hQ hcut
  have hEq := A.generatorFiltration_eq_negativeFiltration hGT hgen
  refine ⟨D, hD, S, ?_, hS, ?_, ?_⟩
  · intro d hd
    dsimp [S]
    rw [ite_eq_right]
    omega
  · intro w a ha
    change a ∈ A.homogeneousNegativeFiltration T w w
    rw [A.homogeneousNegativeFiltration_eq hT, ← hEq]
    exact ⟨hgen w ha, ha⟩
  · intro w a ha
    change a ∈ A.homogeneousNegativeFiltration T (w - 1) w
    rw [A.homogeneousNegativeFiltration_eq hT, ← hEq]
    exact ⟨U.c2_grade_le_generatorFiltration D T hQ hcut w ha, ha.2⟩

 

theorem primary_decomposition {d : ℕ} {a : V} (ha : a ∈ A.grade d) :
    ∃ q ∈ A.grade d, A.IsPrimary q ∧ ∃ y ∈ A.lowerVirasoroSpace d, a = q + y := by
  let K := A.lowerVirasoroSpace d
  let := A.grade_finite d
  have : FiniteDimensional ℂ K :=
    Submodule.finiteDimensional_of_le (A.lowerVirasoroSpace_le_grade d)
  obtain ⟨y, hy, q, hq, hayq⟩ := K.exists_add_mem_mem_orthogonal a
  have hygrade := A.lowerVirasoroSpace_le_grade d hy
  have hqgrade : q ∈ A.grade d := by
    have he : q = a - y := by rw [hayq]; abel
    rw [he]
    exact (A.grade d).sub_mem ha hygrade
  have hp : A.IsPrimary q := by
    intro n hn
    by_cases hnd : n ≤ d
    · have hLq : A.virasoroMode n q ∈ A.grade (d - n) :=
        A.virasoro_mem_grade hqgrade n (by omega)
      have hmem : A.virasoroMode (-(n : ℤ)) (A.virasoroMode n q) ∈ K :=
        A.virasoro_mem_lowerVirasoroSpace hn hnd hLq
      apply (inner_self_eq_zero (𝕜 := ℂ)).mp
      have h := (K.mem_orthogonal q).mp hq _ hmem
      simpa only [U.virasoro_adjoint, neg_neg] using h
    · exact A.virasoro_eq_zero_of_lt hqgrade n (by omega)
  exact ⟨q, hqgrade, hp, y, hy, hayq.trans (add_comm _ _)⟩

 

theorem grade_le_primaryDescendantSpan (d : ℕ) : A.grade d ≤ A.primaryDescendantSpan := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro a ha
    obtain ⟨q, hq, hp, y, hy, rfl⟩ := U.primary_decomposition ha
    apply Submodule.add_mem _ (A.primary_mem_primaryDescendantSpan hq hp)
    have hK : A.lowerVirasoroSpace d ≤ A.primaryDescendantSpan := by
      apply iSup_le
      intro n x hx
      obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hx
      have hbn := ih (d - (n.val + 1)) (by have := n.isLt; omega) hb
      have h := A.virasoro_mem_primaryDescendantSpan hbn (Nat.zero_lt_succ n.val)
      simpa only [Nat.cast_succ] using h
    exact hK hy

 

theorem primaryDescendantSpan_eq_top : A.primaryDescendantSpan = ⊤ := by
  apply top_unique
  intro a _
  exact A.homogeneous_induction (P := fun x => x ∈ A.primaryDescendantSpan)
    (Submodule.zero_mem _) (fun d _ ha => U.grade_le_primaryDescendantSpan d ha)
    (fun _ _ ha hb => Submodule.add_mem _ ha hb) a

end UnitaryStructure

end CFTTypeVOA

open Filter in
 

theorem additive_cutoff_log_bound (b : ℕ → ℝ) (s : ℕ)
    (ρ c p K : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hc : 0 ≤ c) (hp : 0 ≤ p)
    (hstart : ∀ N : ℕ, b N ≤ K * ((N : ℝ) + 1))
    (hstep : ∀ N : ℕ, b N ≤ c + p * Real.log ((N : ℝ) + 1) + ρ * b (N + s)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      b N ≤ C + (p / (1 - ρ)) * Real.log ((N : ℝ) + 1) := by
  let α := p / (1 - ρ)
  let C := (c + ρ * α * s) / (1 - ρ)
  let F := fun N : ℕ => α * Real.log ((N : ℝ) + 1) + C
  have hden : 0 < 1 - ρ := sub_pos.mpr hρ1
  have hα0 : 0 ≤ α := div_nonneg hp hden.le
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hα : p + ρ * α = α := by
    dsimp [α]
    field_simp
    ring
  have hC : c + ρ * α * s + ρ * C = C := by
    dsimp [C]
    field_simp
    ring
  have hlog (N : ℕ) : Real.log ((N + s : ℕ) + 1 : ℝ) ≤
      Real.log ((N : ℝ) + 1) + s := by
    have hle : ((N + s : ℕ) : ℝ) + 1 ≤ ((N : ℝ) + 1) * ((s : ℝ) + 1) := by
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (Nat.cast_nonneg s)]
    calc
      _ ≤ Real.log (((N : ℝ) + 1) * ((s : ℝ) + 1)) := Real.log_le_log (by positivity) hle
      _ = Real.log ((N : ℝ) + 1) + Real.log ((s : ℝ) + 1) :=
        Real.log_mul (by positivity) (by positivity)
      _ ≤ _ := add_le_add le_rfl (by
        simpa using Real.log_le_sub_one_of_pos (show (0 : ℝ) < (s : ℝ) + 1 by positivity))
  have hF0 (N : ℕ) : 0 ≤ F N := by
    dsimp [F]
    exact add_nonneg (mul_nonneg hα0 (Real.log_nonneg (by have := Nat.cast_nonneg N (α := ℝ); linarith))) hC0
  have hsuper (N : ℕ) :
      c + p * Real.log ((N : ℝ) + 1) + ρ * F (N + s) ≤ F N := by
    dsimp only [F]
    calc
      _ ≤ c + p * Real.log ((N : ℝ) + 1) +
          ρ * (α * (Real.log ((N : ℝ) + 1) + s) + C) := by gcongr; exact hlog N
      _ = (p + ρ * α) * Real.log ((N : ℝ) + 1) + (c + ρ * α * s + ρ * C) := by ring
      _ = _ := by rw [hα, hC]
  have hres (N : ℕ) : b N - F N ≤ ρ * (b (N + s) - F (N + s)) := by
    have h₁ := hstep N
    have h₂ := hsuper N
    nlinarith
  have hit (r : ℕ) : ∀ N : ℕ, b N - F N ≤ ρ^r * b (N + r * s) := by
    induction r with
    | zero =>
      intro N
      simpa using sub_le_self (b N) (hF0 N)
    | succ r ih =>
      intro N
      calc
        _ ≤ ρ * (b (N + s) - F (N + s)) := hres N
        _ ≤ ρ * (ρ^r * b (N + s + r * s)) := mul_le_mul_of_nonneg_left (ih (N + s)) hρ0
        _ = _ := by
          rw [show N + s + r * s = N + (r + 1) * s by ring, pow_succ]
          ring
  refine ⟨C, hC0, fun N => ?_⟩
  have htail : Tendsto (fun r : ℕ => ρ^r * (K * ((N + r * s : ℕ) + 1 : ℝ)))
      atTop (nhds 0) := by
    have h₀ := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
    have h₁ := tendsto_pow_const_mul_const_pow_of_lt_one 1 hρ0 hρ1
    have h := (h₀.const_mul (K * ((N : ℝ) + 1))).add (h₁.const_mul (K * s))
    convert h using 1
    · ext r
      push_cast
      ring
    · simp
  have hbd (r : ℕ) : b N - F N ≤ ρ^r * (K * ((N + r * s : ℕ) + 1 : ℝ)) :=
    (hit r N).trans (mul_le_mul_of_nonneg_left (hstart _) (pow_nonneg hρ0 _))
  have hlast : b N - F N ≤ 0 := ge_of_tendsto' htail hbd
  dsimp [F] at hlast
  dsimp [α] at hlast
  linarith

namespace LocalSkewFlow
open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma inner_tsum_left (u : ℕ → E) (hu : Summable u) (w : E) :
    inner ℂ (∑' n, u n) w = ∑' n, inner ℂ (u n) w := by
  exact ((innerSL ℂ).flip w).map_tsum hu

lemma inner_tsum_right (v : ℕ → E) (hv : Summable v) (w : E) :
    inner ℂ w (∑' n, v n) = ∑' n, inner ℂ w (v n) := by
  exact (innerSL ℂ w).map_tsum hv

variable [CompleteSpace E]

lemma inner_tsum_prod (u v : ℕ → E) (hu : Summable (fun n => ‖u n‖))
    (hv : Summable (fun n => ‖v n‖)) :
    inner ℂ (∑' n, u n) (∑' n, v n) =
      ∑' p : ℕ × ℕ, inner ℂ (u p.1) (v p.2) := by
  have hs : Summable (fun p : ℕ × ℕ => inner ℂ (u p.1) (v p.2)) := by
    have hp : Summable (fun p : ℕ × ℕ => ‖u p.1‖ * ‖v p.2‖) :=
      hu.mul_of_nonneg hv (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    apply Summable.of_norm_bounded hp
    intro p
    exact norm_inner_le_norm _ _
  rw [hs.tsum_prod, inner_tsum_left _ hu.of_norm]
  apply tsum_congr
  intro n
  exact inner_tsum_right _ hv.of_norm _

lemma tsum_prod_antidiagonal (f : ℕ × ℕ → ℂ) (hf : Summable f) :
    (∑' p, f p) = ∑' n, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, f p := by
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq f]
  have hs := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff).mpr hf
  change (∑' p, (f ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) p) = _
  rw [hs.tsum_sigma]
  apply tsum_congr
  intro n
  exact (tsum_fintype _).trans (Finset.sum_finset_coe _ _)

lemma exp_antidiagonal (s t : ℂ) (k : ℕ) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
       (s^p.1 / (p.1.factorial : ℂ)) * (t^p.2 / (p.2.factorial : ℂ))) =
      (s + t)^k / (k.factorial : ℂ) := by
  rw [(Commute.all s t).add_pow', Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have he : p.1 + p.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [← he]
  simp only [nsmul_eq_mul]
  rw [Nat.cast_add_choose ℂ]
  have h1 : (p.1.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (p.2.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h3 : ((p.1 + p.2).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

section SkewFlow
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (K : Module.End ℂ V)

def skewExpTerm (t : ℝ) (n : ℕ) (v : V) : UniformSpace.Completion V :=
  ((t : ℂ)^n / (n.factorial : ℂ)) • (((K^n) v : V) : UniformSpace.Completion V)

def skewExp (t : ℝ) (v : V) : UniformSpace.Completion V :=
  ∑' n, skewExpTerm K t n v

lemma skewExpTerm_norm_bound {C : ℝ} (hC : 0 ≤ C) {N : ℕ} {v : V}
    (hb : ∀ n, ‖(K^n) v‖ ≤ C^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖)
    (t : ℝ) (n : ℕ) :
    ‖skewExpTerm K t n v‖ ≤ (2 : ℝ)^N * (2 * |t| * C)^n * ‖v‖ := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hc : ((N + n).choose n : ℝ) ≤ (2 : ℝ)^(N + n) := by
    exact_mod_cast Nat.choose_le_two_pow (N + n) n
  calc
    _ = (|t|^n / (n.factorial : ℝ)) * ‖(K^n) v‖ := by
      simp [skewExpTerm, norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (|t|^n / (n.factorial : ℝ)) *
        (C^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖) := by gcongr; exact hb n
    _ = (|t| * C)^n * ((N + n).choose n : ℝ) * ‖v‖ := by
      rw [Nat.ascFactorial_eq_factorial_mul_choose]
      push_cast
      rw [mul_pow]
      field_simp
    _ ≤ (|t| * C)^n * (2 : ℝ)^(N + n) * ‖v‖ := by gcongr
    _ = _ := by rw [pow_add]; simp only [mul_pow]; ring

lemma summable_norm_skewExpTerm {C : ℝ} (hC : 0 ≤ C) {N : ℕ} {v : V}
    (hb : ∀ n, ‖(K^n) v‖ ≤ C^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖)
    {t : ℝ} (ht : 2 * |t| * C < 1) :
    Summable (fun n => ‖skewExpTerm K t n v‖) := by
  have hg := (summable_geometric_of_lt_one (by positivity : 0 ≤ 2 * |t| * C) ht).mul_left ((2 : ℝ)^N)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (skewExpTerm_norm_bound K hC hb t)
    (hg.mul_right ‖v‖)

lemma skew_pow_inner
    (hs : ∀ v w, inner ℂ (K v) w = - inner ℂ v (K w))
    (n m : ℕ) (v w : V) :
    inner ℂ ((K^n) v) ((K^m) w) = (-1 : ℂ)^n * inner ℂ v ((K^(n + m)) w) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, hs]
    rw [← Module.End.mul_apply, ← pow_succ', ih (m + 1)]
    rw [show n + (m + 1) = n + 1 + m by omega, pow_succ]
    ring

lemma inner_skewExpTerm
    (hs : ∀ v w, inner ℂ (K v) w = - inner ℂ v (K w))
    (t : ℝ) (n m : ℕ) (v w : V) :
    inner ℂ (skewExpTerm K t n v) (skewExpTerm K t m w) =
      (((-t : ℝ) : ℂ)^n / (n.factorial : ℂ)) *
        ((t : ℂ)^m / (m.factorial : ℂ)) * inner ℂ v ((K^(n + m)) w) := by
  simp only [skewExpTerm, inner_smul_left, inner_smul_right,
    UniformSpace.Completion.inner_coe, skew_pow_inner K hs,
    map_div₀, map_pow, Complex.conj_ofReal, map_natCast]
  push_cast
  rw [neg_pow]
  ring

lemma inner_skewExp
    (hs : ∀ v w, inner ℂ (K v) w = - inner ℂ v (K w))
    (t : ℝ) (v w : V)
    (hv : Summable (fun n => ‖skewExpTerm K t n v‖))
    (hw : Summable (fun n => ‖skewExpTerm K t n w‖)) :
    inner ℂ (skewExp K t v) (skewExp K t w) = inner ℂ v w := by
  have hf : Summable (fun p : ℕ × ℕ =>
      inner ℂ (skewExpTerm K t p.1 v) (skewExpTerm K t p.2 w)) := by
    apply Summable.of_norm_bounded
      (hv.mul_of_nonneg hw (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
    intro p
    exact norm_inner_le_norm _ _
  rw [skewExp, skewExp, inner_tsum_prod _ _ hv hw, tsum_prod_antidiagonal _ hf]
  have he : ∀ k, (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      inner ℂ (skewExpTerm K t p.1 v) (skewExpTerm K t p.2 w)) =
      if k = 0 then inner ℂ v w else 0 := by
    intro k
    simp_rw [inner_skewExpTerm K hs]
    calc
      _ = (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
          (((-t : ℝ) : ℂ)^p.1 / (p.1.factorial : ℂ)) *
          ((t : ℂ)^p.2 / (p.2.factorial : ℂ))) * inner ℂ v ((K^k) w) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
      _ = _ := by rw [exp_antidiagonal]; push_cast; split_ifs with hk <;> simp [hk]
  simp_rw [he]
  simp
end SkewFlow

section SkewFlowNorm
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (K : Module.End ℂ V)

lemma norm_skewExp
    (hs : ∀ v w, inner ℂ (K v) w = - inner ℂ v (K w))
    (t : ℝ) (v : V) (hv : Summable (fun n => ‖skewExpTerm K t n v‖)) :
    ‖skewExp K t v‖ = ‖v‖ := by
  have h := inner_skewExp K hs t v v hv hv
  simp only [inner_self_eq_norm_sq_to_K] at h
  have he : ‖skewExp K t v‖^2 = ‖v‖^2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

lemma skewExp_add (t : ℝ) (v w : V)
    (hv : Summable (fun n => ‖skewExpTerm K t n v‖))
    (hw : Summable (fun n => ‖skewExpTerm K t n w‖)) :
    skewExp K t (v + w) = skewExp K t v + skewExp K t w := by
  simp only [skewExp, skewExpTerm, map_add, UniformSpace.Completion.coe_add, smul_add]
  exact hv.of_norm.tsum_add hw.of_norm

lemma skewExp_smul (t : ℝ) (z : ℂ) (v : V) :
    skewExp K t (z • v) = z • skewExp K t v := by
  simp only [skewExp, skewExpTerm, map_smul, UniformSpace.Completion.coe_smul,
    smul_comm (_ / _) z, tsum_const_smul'']

end SkewFlowNorm

lemma summable_shifted_pow_geometric (a : ℝ) (ha : 0 ≤ a) (r : ℕ)
    {q : ℝ} (hq : 0 ≤ q) (hql : q < 1) :
    Summable (fun n : ℕ => (a + n)^r * q^n) := by
  have he : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq] using hql
  have h1 := (summable_geometric_of_lt_one hq hql).mul_left (a^r)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one r he
  have hsum := (h1.add h2).mul_left ((2 : ℝ)^(r - 1))
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hsum
  intro n
  change (a + (n : ℝ))^r * q^n ≤ 2^(r - 1) * (a^r*q^n + (n : ℝ)^r*q^n)
  calc
    _ ≤ (2 : ℝ)^(r - 1) * (a^r + (n : ℝ)^r) * q^n := by
      gcongr
      exact add_pow_le ha (Nat.cast_nonneg n) r
    _ = _ := by ring

lemma shifted_pow_geometric_tail_uniform (r N n : ℕ) (hn : N ≤ n) {q : ℝ} (hq : 0 ≤ q) :
    (2 : ℝ)^N * (1 + (N : ℝ) + n)^r * q^n ≤
      (2 : ℝ)^r * (1 + (n : ℝ))^r * (2*q)^n := by
  have hN : (N : ℝ) ≤ n := by exact_mod_cast hn
  calc
    _ ≤ (2 : ℝ)^n * (2 * (1 + (n : ℝ)))^r * q^n := by
      gcongr
      · norm_num
      · linarith
    _ = _ := by simp only [mul_pow]; ring

section Algebra
variable {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
end Algebra
end LocalSkewFlow
end StronglyRationalVOA

end

end OAI
