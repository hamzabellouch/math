import OAI.RepresentationTheory.VertexAlgebra.ModuleGeneratorMajorant
import OAI.RepresentationTheory.VertexAlgebra.ModuleBlockSquareBound

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
theorem finite_band_weighted_poly_uniform {ι κ : Type*} {B : EnergyBand → ℕ → ℝ}
    (hB : ∀ t N, 1 ≤ B t N) (s : Finset ι) (f : ι → EnergyBand → ℕ → κ → ℝ)
    (w : ι → ℕ) (T : ℕ → κ → Prop)
    (H : ∀ i ∈ s, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ t N x, T N x →
      f i t N x ≤ C * (1 + (N : ℝ))^p * B t N ^ w i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ i ∈ s, ∀ t N x, T N x →
      f i t N x ≤ C * (1 + (N : ℝ))^p * B t N ^ w i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, 0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨C, hC, p, hp⟩ := H i (Finset.mem_insert_self _ _)
    obtain ⟨D, hD, q, hq⟩ := ih (fun j hj => H j (Finset.mem_insert_of_mem hj))
    refine ⟨C + D, add_nonneg hC hD, p + q, ?_⟩
    intro j hj t N x hx
    have hBN : 0 ≤ B t N := zero_le_one.trans (hB t N)
    have hN1 : 1 ≤ 1 + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg N)
    have hpq : (1 + (N : ℝ))^p ≤ (1 + (N : ℝ))^(p + q) :=
      pow_le_pow_right₀ hN1 (by omega)
    have hqp : (1 + (N : ℝ))^q ≤ (1 + (N : ℝ))^(p + q) :=
      pow_le_pow_right₀ hN1 (by omega)
    rcases Finset.mem_insert.mp hj with rfl | hj
    · apply (hp t N x hx).trans
      gcongr
      exact le_add_of_nonneg_right hD
    · apply (hq j hj t N x hx).trans
      gcongr
      exact le_add_of_nonneg_left hC

namespace UnitaryStructure
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {M : A.GradingRestrictedModule W} (Hunit : M.UnitaryStructure U)
include Hunit
theorem grade_blockGrowth {B : EnergyBand → ℕ → ℝ} (hB : ∀ t N, 1 ≤ B t N) (D : ℕ)
    (hsmall : ∀ d, 1 ≤ d → d ≤ D → ∀ a ∈ A.grade d, A.IsQuasiPrimary a →
      M.BlockGrowth B a d d)
    (hcut : ∀ d, D < d → A.grade d ≤ A.toVertexAlgebra.c2) :
    ∀ d, ∀ a ∈ A.grade d, M.BlockGrowth B a d d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro a ha
    by_cases hd0 : d = 0
    · subst d
      rw [A.grade_zero] at ha
      obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp ha
      exact M.blockGrowth_smul (M.vacuum_blockGrowth B) z
    by_cases hdD : d ≤ D
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
      obtain ⟨q, hq, hqq, b, hb, hab⟩ := U.quasiPrimary_decomposition ha
      rw [hab, A.virasoro_neg_one_eq_translation]
      exact M.blockGrowth_add hB (hsmall _ (by omega) hdD q hq hqq)
        (M.blockGrowth_mono_weight hB (M.translation_blockGrowth hB (ih e (by omega) b hb))
          (by omega))
    · have hc : a ∈ A.homogeneousC2 d := by
        rw [A.homogeneousC2_eq]
        exact ⟨hcut d (by omega) ha, ha⟩
      exact M.homogeneousC2_le_blockGrowth Hunit hB d ih hc

 

theorem exists_generatorMajorant (hc : A.toVertexAlgebra.C2Cofinite) :
    ∃ D : ℕ, 2 ≤ D ∧ ∃ S : ℕ → Finset V,
      (∀ d, d = 0 ∨ D < d → S d = ∅) ∧
      (∀ d, ∀ a ∈ S d, 1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧
        A.IsQuasiPrimary a ∧ U.IsHermitian d a) ∧
      ∀ w, ∀ a ∈ A.grade w, M.BlockGrowth (M.generatorMajorant D S) a w w := by
  classical
  obtain ⟨D, hD, hcut⟩ := A.exists_c2_weight_cutoff hc
  choose R hR hspan using U.exists_hermitian_quasiPrimary_spanning
  let S : ℕ → Finset V := fun d => if 1 ≤ d ∧ d ≤ D then R d else ∅
  have hS (d : ℕ) (a : V) (ha : a ∈ S d) :
      1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧ A.IsQuasiPrimary a ∧ U.IsHermitian d a := by
    dsimp only [S] at ha
    split_ifs at ha with hd
    · exact ⟨hd.1, hd.2, hR d a ha⟩
    · simp at ha
  refine ⟨D, hD, S, ?_, hS, ?_⟩
  · intro d hd
    dsimp [S]
    rw [ite_eq_right]
    omega
  · apply Hunit.grade_blockGrowth (M.one_le_generatorMajorant D S) D _ hcut
    intro d hd hdD a ha hq
    have he : S d = R d := by dsimp [S]; rw [ite_eq_left ⟨hd, hdD⟩]
    have hmem : a ∈ Submodule.span ℂ (S d : Set V) := by
      rw [he]
      exact hspan d a ha hq
    have hle : Submodule.span ℂ (S d : Set V) ≤
        M.blockGrowthSubmodule (M.generatorMajorant D S) (M.one_le_generatorMajorant D S) d d := by
      apply Submodule.span_le.mpr
      intro b hb
      exact M.generator_blockGrowth D S (by omega) hdD hb
    exact hle hmem

 

theorem generatorMajorant_polynomial (D : ℕ) (hD : 2 ≤ D) (S : ℕ → Finset V)
    (hS : ∀ d, ∀ a ∈ S d, 1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧
      A.IsQuasiPrimary a ∧ U.IsHermitian d a)
    (H : ∀ w, ∀ a ∈ A.grade w, M.BlockGrowth (M.generatorMajorant D S) a w w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ t N,
      M.generatorMajorant D S t N ≤ C * (1 + (N : ℝ))^p := by
  classical
  let B := M.generatorMajorant D S
  have hB := M.one_le_generatorMajorant D S
  let G := (Finset.range (D + 1)).sigma S
  have HG (i : Σ _ : ℕ, V) (hi : i ∈ G) :
      1 ≤ i.1 ∧ i.1 ≤ D ∧ i.2 ∈ A.grade i.1 ∧
        A.IsQuasiPrimary i.2 ∧ U.IsHermitian i.1 i.2 :=
    hS i.1 i.2 (Finset.mem_sigma.mp hi).2
  have Hsq (i : Σ _ : ℕ, V) (hi : i ∈ G) :
      ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ t N (hk : ℕ × ℕ), hk.1 ≤ N ∧ hk.2 ≤ N →
        ‖M.modeBlock t i.2 i.1 hk.1 hk.2‖^2 ≤
          C * (1 + (N : ℝ))^p * B t N^(2 * i.1 - 1) := by
    obtain ⟨hd, _, ha, hq, hh⟩ := HG i hi
    obtain ⟨C, hC, p, hp⟩ := Hunit.modeBlock_norm_sq_bound hB ha hd hq hh
      (fun j hj => H _ _ (A.mode_mem_grade ha ha j (by omega)))
    exact ⟨C, hC, p, fun t N hk hh => hp t N hk.1 hk.2 hh.1 hh.2⟩
  obtain ⟨C, hC, p, hp⟩ := finite_band_weighted_poly_uniform hB G
    (fun (i : Σ _ : ℕ, V) (t : EnergyBand) (_ : ℕ) (hk : ℕ × ℕ) => ‖M.modeBlock t i.2 i.1 hk.1 hk.2‖^2)
    (fun i => 2 * i.1 - 1) (fun N (hk : ℕ × ℕ) => hk.1 ≤ N ∧ hk.2 ≤ N) Hsq
  let J : ℝ := (G.card : ℝ) + 1
  have hJ : 1 ≤ J := by dsimp [J]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  refine ⟨J^(2 * D) * (C + 1), by positivity, 4 * D + p, ?_⟩
  intro t N
  have hBN : 0 ≤ B t N := zero_le_one.trans (hB t N)
  have hBN' : 0 ≤ M.generatorMajorant D S t N := hBN
  let s := G ×ˢ (Finset.range (N + 1) ×ˢ Finset.range (N + 1))
  let x : ((Σ _ : ℕ, V) × (ℕ × ℕ)) → ℝ :=
    fun i => ‖M.modeBlock t i.1.2 i.1.1 i.2.1 i.2.2‖ ^ (i.1.1 : ℝ)⁻¹
  have hx (i) : 0 ≤ x i := by
    dsimp [x]
    exact Real.rpow_nonneg (norm_nonneg (M.modeBlock t _ _ _ _)) _
  have hsum : 1 + ∑ i ∈ s, x i = B t N := by
    simp only [s, x, G, B, generatorMajorant, Finset.sum_product, Finset.sum_sigma]
  let R := (C + 1) * (1 + (N : ℝ))^p
  have hN1 : 1 ≤ 1 + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg N)
  have hR : 1 ≤ R := by
    dsimp [R]
    nlinarith [one_le_pow₀ hN1 (n := p)]
  have hstep (i) (hi : i ∈ s) : (x i)^(2 * D) ≤ R * (B t N)^(2 * D - 1) := by
    obtain ⟨hiG, hhk⟩ := Finset.mem_product.mp hi
    obtain ⟨hh, hk⟩ := Finset.mem_product.mp hhk
    have hhN : i.2.1 ≤ N := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hh
    have hkN : i.2.2 ≤ N := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    have hs := HG i.1 hiG
    have hroot : x i ≤ B t N := M.root_modeBlock_le_generatorMajorant D S t hs.2.1
      (Finset.mem_sigma.mp hiG).2 hhN hkN
    have hpow : (x i)^(2 * i.1.1) = ‖M.modeBlock t i.1.2 i.1.1 i.2.1 i.2.2‖^2 := by
      rw [mul_comm 2 i.1.1, pow_mul]
      dsimp [x]
      rw [Real.rpow_inv_natCast_pow (norm_nonneg (M.modeBlock t _ _ _ _)) (by omega)]
    have hsq := hp i.1 hiG t N i.2 ⟨hhN, hkN⟩
    have hsq' : (x i)^(2 * i.1.1) ≤ R * (B t N)^(2 * i.1.1 - 1) := by
      rw [hpow]
      apply hsq.trans
      dsimp [R]
      gcongr
      linarith
    have he : 2 * i.1.1 + (2 * D - 2 * i.1.1) = 2 * D := by omega
    have he' : (2 * i.1.1 - 1) + (2 * D - 2 * i.1.1) = 2 * D - 1 := by omega
    calc
      _ = (x i)^(2 * i.1.1) * (x i)^(2 * D - 2 * i.1.1) := by rw [← pow_add, he]
      _ ≤ (R * (B t N)^(2 * i.1.1 - 1)) * (B t N)^(2 * D - 2 * i.1.1) := by
        apply mul_le_mul hsq' (pow_le_pow_left₀ (hx i) hroot _) (pow_nonneg (hx i) _) (by positivity)
      _ = _ := by rw [mul_assoc, ← pow_add, he']
  have hcontract := finite_sum_power_contraction s x (2 * D) (by omega) R hR
    (fun i _ => hx i) (fun i hi => by rw [hsum]; exact hstep i hi)
  rw [hsum] at hcontract
  have hcard : (s.card : ℝ) + 1 ≤ J * (1 + (N : ℝ))^2 := by
    simp only [s, Finset.card_product, Finset.card_range, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, J]
    nlinarith [Nat.cast_nonneg N (α := ℝ)]
  calc
    _ ≤ ((s.card : ℝ) + 1)^(2 * D) * R := hcontract
    _ ≤ (J * (1 + (N : ℝ))^2)^(2 * D) * R := by
      gcongr
    _ = _ := by
      dsimp [R]
      rw [mul_pow, ← pow_mul, ← mul_assoc, mul_right_comm _ _ (C + 1), mul_assoc,
        ← pow_add]
      congr 2
      omega

end UnitaryStructure
end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
