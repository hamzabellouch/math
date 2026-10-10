import OAI.RepresentationTheory.VertexAlgebra.ModuleSharpBounds
import OAI.RepresentationTheory.VertexAlgebra.ModulePositiveColumn

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)
def zeroGrowthSubmodule (X : EnergyBand → ℕ → ℝ) (d p q : ℕ) : Submodule ℂ V where
  carrier := {a | M.ZeroGrowth X a d p q}
  zero_mem' := M.zeroGrowth_zero X d p q
  add_mem' := M.zeroGrowth_add
  smul_mem' z _ H := M.zeroGrowth_smul H z

theorem zeroGrowth_changeControl {X Y : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 0 ≤ X τ N)
    (hXY : ∀ τ N, X τ N ≤ Y τ N) {a : V} {d p q : ℕ} (H : M.ZeroGrowth X a d p q) :
    M.ZeroGrowth Y a d p q := by
  obtain ⟨C, hC, HC⟩ := H
  refine ⟨C, hC, ?_⟩
  intro τ N v hv
  apply (HC τ N v hv).trans
  gcongr
  · exact hX τ N
  · exact hXY τ N

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q
theorem zeroMode_sharpGrowth {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N) (hmono : ∀ τ, Monotone (X τ))
    {a : V} {d : ℕ} (hp : M.PolynomialEnergyBound a) (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (hd : 2 ≤ d)
    (H : ∀ e ≤ 2*d-2, ∀ b ∈ A.grade e, M.SharpGrowth X b e) :
    M.ZeroGrowth (fun τ N => X τ (2*N)) a d (2*(d-1)) (2*(d-1)) := by
  obtain ⟨C, hC, HC⟩ := Q.nonzeroModes_sharp_bound hX ha hq hh hd H
  let F : EnergyBand → ℕ → ℝ := fun τ N => (C+1)*2^(2*d)*(N+1 : ℝ)^(d-1)*X τ N^(d-1)
  have hF (τ : EnergyBand) (N : ℕ) : 1 ≤ F τ N := by
    dsimp [F]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by norm_num)))
      (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]))) (one_le_pow₀ (hX τ N))
  have HF (τ : EnergyBand) (N : ℕ) (v : W) (hv : v ∈ M.energyCutoff τ N) :
      ‖M.physicalMode a d 1 v‖ ≤ F τ N * ‖v‖ := by
    have H' := (HC τ N 1 (by decide) v hv).1
    apply H'.trans
    dsimp [F]
    have hXN := zero_le_one.trans (hX τ N)
    norm_num only [Nat.cast_one, show (1 : ℝ)+1 = 2 by norm_num]
    gcongr
    linarith
  obtain ⟨B, hB, HB⟩ := Q.zeroMode_transfer hp ha hq hd
  let K := B*(C+1)*2^(2*d)*2^(d-1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have HR (τ : EnergyBand) (N h : ℕ) (hhN : h ≤ N) :
      B * F τ (2*h) ≤ K * (N+1 : ℝ)^(d-1)*X τ (2*N)^(d-1) := by
    have hx := zero_le_one.trans (hX τ (2*h))
    have hx' := zero_le_one.trans (hX τ (2*N))
    have hnR : (2*h+1 : ℝ) ≤ 2*(N+1 : ℝ) := by
      have hn : (h : ℝ) ≤ N := by exact_mod_cast hhN
      linarith
    have hXm : X τ (2*h) ≤ X τ (2*N) := hmono τ (by omega)
    calc
      _ ≤ B * ((C+1)*2^(2*d)*(2*(N+1 : ℝ))^(d-1)*X τ (2*N)^(d-1)) := by
        dsimp [F]
        push_cast
        gcongr
      _ = _ := by dsimp [K]; rw [mul_pow]; ring
  refine ⟨K^2, sq_nonneg _, ?_⟩
  intro τ N v hv
  have hXN := zero_le_one.trans (hX τ (2*N))
  have HK : ‖M.physicalMode a d 0 v‖^2 ≤
      (K*(N+1 : ℝ)^(d-1)*X τ (2*N)^(d-1))^2 * ‖v‖^2 := by
    apply Q.physicalMode_cutoff_sq_of_grades τ ha 0 _ _ hv
    intro h hhN w hw
    have Hnorm : ‖M.physicalMode a d 0 w‖ ≤
        (K*(N+1 : ℝ)^(d-1)*X τ (2*N)^(d-1))*‖w‖ :=
      (HB τ (F τ) (hF τ) (HF τ) h w hw).trans (mul_le_mul_of_nonneg_right (HR τ N h hhN) (norm_nonneg _))
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) Hnorm 2
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm (d-1) 2] using HK

theorem grade_improved_zeroGrowth {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N)
    (hmono : ∀ τ, Monotone (X τ)) (hp : M.PolynomialEnergyBounds)
    (H : ∀ e, ∀ b ∈ A.grade e, M.SharpGrowth X b e)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hd : 2 ≤ d) :
    M.ZeroGrowth (fun τ N => X τ (2*N)) a d (2*(d-1)) (2*(d-1)) := by
  classical
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  obtain ⟨q, hq, hqq, b, hb, hab⟩ := U.quasiPrimary_decomposition ha
  obtain ⟨S, hS, hspan⟩ := U.exists_hermitian_quasiPrimary_spanning (e+1)
  have Hq : M.ZeroGrowth (fun τ N => X τ (2*N)) q (e+1) (2*e) (2*e) := by
    have hle : Submodule.span ℂ (S : Set V) ≤
        M.zeroGrowthSubmodule (fun τ N => X τ (2*N)) (e+1) (2*e) (2*e) := by
      apply Submodule.span_le.mpr
      intro c hc
      obtain ⟨hcg, hcq, hch⟩ := hS c hc
      change M.ZeroGrowth (fun τ N => X τ (2*N)) c (e+1) (2*e) (2*e)
      simpa only [Nat.add_sub_cancel] using
        Q.zeroMode_sharpGrowth hX hmono (hp c) hcg hcq hch hd
          (fun f _ c hcf => H f c hcf)
    exact hle (hspan q hq hqq)
  have Hb := M.translation_zeroGrowth (H e b hb).2
  have Hb' := M.zeroGrowth_changeControl (fun τ N => zero_le_one.trans (hX τ N))
    (fun τ N => hmono τ (by omega : N ≤ 2*N)) Hb
  have Hb'' := M.zeroGrowth_mono (fun τ N => hX τ (2*N)) Hb' (p' := 2*e) (q' := 2*e)
    (by omega) le_rfl
  rw [hab, A.virasoro_neg_one_eq_translation]
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using M.zeroGrowth_add Hq Hb''

omit Q in
theorem positiveColumnNorm_sq_le (τ : EnergyBand) {a : V} {d N : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (H : ∀ v ∈ M.energyCutoff τ N,
      (∑ m ∈ Finset.range (N+1), ‖M.physicalMode a d m v‖^2) ≤ K*‖v‖^2) :
    M.positiveColumnNorm τ a d N^2 ≤ K := by
  have HB : M.positiveColumnNorm τ a d N ≤ Real.sqrt K := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hK, M.positiveColumn_norm_sq τ]
    exact H v v.property
  exact (pow_le_pow_left₀ (M.positiveColumnNorm_nonneg τ a d N) HB 2).trans_eq (Real.sq_sqrt hK)

theorem generator_column_contraction {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N)
    (hmono : ∀ τ, Monotone (X τ)) (hp : M.PolynomialEnergyBounds)
    (H : ∀ e, ∀ b ∈ A.grade e, M.SharpGrowth X b e)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hd : 1 ≤ d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ N,
      M.positiveColumnNorm τ a d N^2 ≤ C*(N+1 : ℝ)^(2*d-1)*X τ (2*N)^(2*d-1) := by
  have hs : mode A.fields a (-1) a ∈ A.grade (2*d) := A.normalProduct_mem_grade ha
  obtain ⟨C, hC, HC⟩ := Q.grade_improved_zeroGrowth hX hmono hp H hs (by omega)
  refine ⟨C+1, by linarith, ?_⟩
  intro τ N
  have hXN := zero_le_one.trans (hX τ (2*N))
  apply positiveColumnNorm_sq_le τ (by positivity)
  intro v hv
  have Hs := norm_of_sharp_square hXN hC N (2*d-1) (2*d-1) v _ (HC τ N v hv)
  have Hpos := Q.positive_column hd ha hq hh v
  have Hfin : (∑ m ∈ Finset.range (N+1), ‖M.physicalMode a d m v‖^2) ≤
      ∑ᶠ m : ℕ, ‖M.physicalMode a d m v‖^2 :=
    (Q.finsum_positive_modes_sq_eq τ ha hv).symm.le
  have HE : M.physicalMode (mode A.fields a (-1) a) (2*d) 0 v =
      mode M.fields (mode A.fields a (-1) a) (2*(d : ℤ)-1) v := by
    simp only [physicalMode, zero_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [HE] at Hs
  calc
    _ ≤ _ := Hfin.trans Hpos
    _ ≤ ‖mode M.fields (mode A.fields a (-1) a) (2*(d : ℤ)-1) v‖*‖v‖ := re_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ((C+1)*(N+1 : ℝ)^(2*d-1)*X τ (2*N)^(2*d-1)*‖v‖)*‖v‖ :=
      mul_le_mul_of_nonneg_right Hs (norm_nonneg _)
    _ = _ := by ring

end UnitaryStructure

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
