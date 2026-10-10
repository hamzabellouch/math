import OAI.RepresentationTheory.VertexAlgebra.ModuleSl2Bound

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {M : A.GradingRestrictedModule W} (Hunit : M.UnitaryStructure U)
include Hunit
theorem zeroMode_norm_sq_of_commutator (t : EnergyBand) {a : V} {d N : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (hd : 1 ≤ d) {R : ℝ} (hR : 0 ≤ R)
    (H : ∀ h ≤ N, ∀ c ∈ M.bandGrade t h, ‖M.selfCommutator a d (1 : ℕ) c‖ ≤ R * ‖c‖)
    {h : ℕ} (hN : h ≤ N) {c : W} (hc : c ∈ M.bandGrade t h) :
    ‖M.physicalMode a d 0 c‖ ^ 2 ≤
      256 * (1 + A.centralCharge.re)^2 * (1 + (N : ℝ))^3 * R * ‖c‖^2 := by
  let G : ℝ := Real.sqrt ((1 + (N : ℝ)) * R)
  let K : ℝ := 8 * (1 + A.centralCharge.re) * (1 + (N : ℝ))
  have hccharge := U.centralCharge_nonneg.2
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hG : 0 ≤ G := Real.sqrt_nonneg _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hraising {e : ℕ} (he : e ≤ N) {b : W} (hb : b ∈ M.bandGrade t e) :
      ‖M.physicalMode a d (-1) b‖ ≤ G * ‖b‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hG (norm_nonneg _))).mp
    have h := Hunit.raising_norm_sq_of_commutator t ha hq hh (by omega : 0 < 1) hR H he hb
    norm_num only [Nat.cast_one, neg_inj] at h
    rw [mul_pow, show G ^ 2 = (1 + (N : ℝ)) * R from Real.sq_sqrt (by positivity)]
    calc
      _ ≤ ((e : ℝ) + 1) * R * ‖b‖ ^ 2 := h
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : e + 1 ≤ 1 + N)) hR)
        (sq_nonneg _)
  have hLbound {e : ℕ} (he : e ≤ N + 1) {b : W} (hb : b ∈ M.bandGrade t e) :
      ‖M.virasoroMode 1 b‖ ≤ K * ‖b‖ := by
    have h := Hunit.virasoro_one_norm_on_band t hb
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have her : (e : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast he
    dsimp [K]
    nlinarith [mul_nonneg (show 0 ≤ 1 + A.centralCharge.re by linarith) (by linarith : 0 ≤ 2 * (1 + (N : ℝ)) - (1 + e))]
  have hraisegrade : M.physicalMode a d (-1) c ∈ M.bandGrade t (h + 1) :=
    M.mode_mem_band t ha hc (-1 + (d : ℤ) - 1) (by omega)
  have hLgrade : M.virasoroMode 1 c ∈ M.bandGrade t (h - 1) := by
    by_cases hz : h = 0
    · have he := Hunit.physicalMode_eq_zero_above_band t A.conformal_mem hc 1 (by omega)
      simp only [M.physicalMode_conformal] at he
      rw [he]
      exact (M.bandGrade t (h - 1)).zero_mem
    · exact M.virasoro_mem_band t hc 1 (by omega)
  have hfirst : ‖M.virasoroMode 1 (M.physicalMode a d (-1) c)‖ ≤ K * G * ‖c‖ := by
    calc
      _ ≤ K * ‖M.physicalMode a d (-1) c‖ := hLbound (by omega) hraisegrade
      _ ≤ K * (G * ‖c‖) := mul_le_mul_of_nonneg_left (hraising hN hc) hK
      _ = _ := by ring
  have hsecond : ‖M.physicalMode a d (-1) (M.virasoroMode 1 c)‖ ≤ K * G * ‖c‖ := by
    calc
      _ ≤ G * ‖M.virasoroMode 1 c‖ := hraising (by omega) hLgrade
      _ ≤ G * (K * ‖c‖) := mul_le_mul_of_nonneg_left (hLbound (by omega) hc) hG
      _ = _ := by ring
  have he := congrArg norm (M.zeroMode_commutator ha hq c)
  rw [norm_smul, Complex.norm_natCast] at he
  have hlo : ‖M.physicalMode a d 0 c‖ ≤ 2 * K * G * ‖c‖ := by
    calc
      _ ≤ (d : ℝ) * ‖M.physicalMode a d 0 c‖ := by
        have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
        nlinarith [norm_nonneg (M.physicalMode a d 0 c)]
      _ = _ := he.symm
      _ ≤ ‖M.virasoroMode 1 (M.physicalMode a d (-1) c)‖ +
          ‖M.physicalMode a d (-1) (M.virasoroMode 1 c)‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  calc
    _ ≤ (2 * K * G * ‖c‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hlo 2
    _ = 4 * K^2 * G^2 * ‖c‖^2 := by ring
    _ = _ := by
      rw [show G^2 = (1 + (N : ℝ)) * R from Real.sq_sqrt (by positivity)]
      dsimp [K]
      ring

 

theorem modeBlock_norm_sq_bound {B : EnergyBand → ℕ → ℝ} (hB : ∀ t N, 1 ≤ B t N)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hd : 1 ≤ d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (H : ∀ j < 2 * d, M.BlockGrowth B (mode A.fields a j a)
      (2 * d - j - 1) (2 * d - j - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ t, ∀ N h k : ℕ, h ≤ N → k ≤ N →
      ‖M.modeBlock t a d h k‖ ^ 2 ≤ C * (1 + (N : ℝ)) ^ p * B t N ^ (2 * d - 1) := by
  obtain ⟨C, hC, p, hp⟩ := M.selfCommutator_bound hB ha hd H
  let F : ℝ := 256 * (1 + A.centralCharge.re)^2
  have hccharge := U.centralCharge_nonneg.2
  have hF : 1 ≤ F := by dsimp [F]; nlinarith [sq_nonneg A.centralCharge.re]
  refine ⟨F * C, by positivity, p + 3, ?_⟩
  intro t N h k hN kN
  let R : ℝ := C * (1 + (N : ℝ)) ^ p * B t N ^ (2 * d - 1)
  let Q : ℝ := F * (1 + (N : ℝ)) ^ 3 * R
  have hBN : 0 ≤ B t N := zero_le_one.trans (hB t N)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hN1 : 1 ≤ 1 + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg N)
  have hQle : (1 + (N : ℝ)) * R ≤ Q := by
    dsimp [Q]
    have hpow : 1 + (N : ℝ) ≤ (1 + (N : ℝ)) ^ 3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hN1 (by norm_num : 1 ≤ 3)
    have hmul : (1 + (N : ℝ)) ^ 3 ≤ F * (1 + (N : ℝ)) ^ 3 := by
      nlinarith [pow_nonneg (show 0 ≤ 1 + (N : ℝ) by positivity) 3]
    exact mul_le_mul_of_nonneg_right (hpow.trans hmul) hR
  have H' (m : ℕ) (hm : m ≤ N + 1) :
      ∀ e ≤ N, ∀ c ∈ M.bandGrade t e, ‖M.selfCommutator a d m c‖ ≤ R * ‖c‖ := hp t N m hm
  have hsquare (c : M.bandGrade t h) : ‖M.modeBlock t a d h k c‖^2 ≤ Q * ‖c‖^2 := by
    rw [modeBlock_apply]
    by_cases heq : h = k
    · subst k
      simpa only [sub_self, Q, F, Submodule.norm_coe] using
        Hunit.zeroMode_norm_sq_of_commutator t ha hq hh hd hR (H' 1 (by omega)) hN c.property
    · by_cases hhk : k < h
      · let m := h - k
        have hm : 0 < m := by dsimp [m]; omega
        have hmN : m ≤ N + 1 := by dsimp [m]; omega
        have he : (m : ℤ) = (h : ℤ) - k := by dsimp [m]; omega
        have hb := Hunit.lowering_norm_sq_of_commutator t ha hq hh hm hR (H' m hmN) h hN c c.property
        rw [he] at hb
        apply hb.trans
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : h ≤ 1 + N)) hR).trans hQle
      · let m := k - h
        have hm : 0 < m := by dsimp [m]; omega
        have hmN : m ≤ N + 1 := by dsimp [m]; omega
        have he : -(m : ℤ) = (h : ℤ) - k := by dsimp [m]; omega
        have hb := Hunit.raising_norm_sq_of_commutator t ha hq hh hm hR (H' m hmN) hN c.property
        rw [he] at hb
        apply hb.trans
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        apply le_trans _ hQle
        apply mul_le_mul_of_nonneg_right _ hR
        exact_mod_cast (by omega : h + 1 ≤ 1 + N)
  have hop : ‖M.modeBlock t a d h k‖ ≤ Real.sqrt Q := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro c
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hQ]
    exact hsquare c
  calc
    _ ≤ (Real.sqrt Q)^2 := pow_le_pow_left₀ (norm_nonneg (M.modeBlock t a d h k)) hop 2
    _ = Q := Real.sq_sqrt hQ
    _ = _ := by dsimp [Q, R]; rw [pow_add]; ring

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure

end

end OAI
