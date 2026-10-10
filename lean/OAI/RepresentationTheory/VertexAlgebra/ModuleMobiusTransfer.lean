import OAI.RepresentationTheory.VertexAlgebra.ModuleMobiusEstimates
import OAI.RepresentationTheory.VertexAlgebra.ModuleRoughEnergy

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)
theorem mobius_physical_commutator {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (m : ℤ) :
    M.mobiusGenerator * M.physicalMode a d m - M.physicalMode a d m * M.mobiusGenerator =
      (((d : ℂ) - 1 - m) / 2) • M.physicalMode a d (m + 1) +
      (((d : ℂ) - 1 + m) / 2) • M.physicalMode a d (m - 1) := by
  calc
    _ = (2 : ℂ)⁻¹ •
        ((M.virasoroMode 1 * M.physicalMode a d m - M.physicalMode a d m * M.virasoroMode 1) -
         (M.virasoroMode (-1) * M.physicalMode a d m - M.physicalMode a d m * M.virasoroMode (-1))) := by
      simp only [mobiusGenerator, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_sub]
      abel
    _ = _ := by
      rw [M.virasoro_one_physical_commutator ha hq, M.virasoro_neg_one_physical_commutator]
      module

theorem mobius_commutator_power {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (n : ℕ) :
    ((LocalSkewFlow.commutatorOperator (R := ℂ) M.mobiusGenerator)^n)
      (M.physicalMode a d 1) =
        MobiusCoefficients.representation (M.physicalMode a d) (MobiusCoefficients.coeff d n) := by
  let L := (LocalSkewFlow.commutatorOperator (R := ℂ) M.mobiusGenerator).restrictScalars ℝ
  have hL (m : ℤ) : L (M.physicalMode a d m) =
      (((d : ℝ) - 1 - m) / 2) • M.physicalMode a d (m + 1) +
      (((d : ℝ) - 1 + m) / 2) • M.physicalMode a d (m - 1) := by
    have he := M.mobius_physical_commutator ha hq m
    change LocalSkewFlow.commutatorOperator (R := ℂ) M.mobiusGenerator (M.physicalMode a d m) = _
    rw [LocalSkewFlow.commutatorOperator_apply, he]
    simp only [← Complex.coe_smul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_intCast, Complex.ofReal_ofNat]
  have h := MobiusCoefficients.representation_coeff (M.physicalMode a d) L d hL n
  convert h using 1
  clear h
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply]
      exact congrArg (LocalSkewFlow.commutatorOperator (R := ℂ) M.mobiusGenerator) ih

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q

 

theorem physicalMode_polynomial_cutoff {a : V} (hp : M.PolynomialEnergyBound a)
    (d : ℕ) (m : ℤ) : ∃ D : ℝ, 0 < D ∧ ∃ r : ℕ, ∀ (τ : EnergyBand) {N : ℕ} {x : W},
    x ∈ M.energyCutoff τ N → ‖M.physicalMode a d m x‖ ≤ D*(1+(N:ℝ))^r*‖x‖ := by
  obtain ⟨C,hC,p,r,he⟩ := hp
  refine ⟨C*(1+|((m+(d:ℤ)-1:ℤ):ℝ)|)^p*2^r, by positivity, r, ?_⟩
  intro τ N x hx
  have he' := he (m+d-1) x
  simp only [Int.cast_abs] at he'
  apply he'.trans
  have hg := Q.energyShift_pow_norm_on_cutoff τ hx r
  calc
    _ ≤ C*(1+|((m+(d:ℤ)-1:ℤ):ℝ)|)^p*((2*(1+(N:ℝ)))^r*‖x‖) := by gcongr
    _ = _ := by rw [mul_pow]; ring

theorem physicalMode_diagonal_zero (τ : EnergyBand) {a : V} {x y : W} {d h : ℕ}
    (ha : a ∈ A.grade d) (hx : x ∈ M.bandGrade τ h) (hy : y ∈ M.bandGrade τ h)
    (m : ℤ) (hm : m ≠ 0) : inner ℂ x (M.physicalMode a d m y)=0 := by
  apply Q.grades_orthogonal _ hx (M.mode_mem_grade ha hy (m+d-1))
  intro he
  apply hm
  have hz : (m:ℂ)=0 := by push_cast at he; linear_combination he
  exact_mod_cast hz

theorem mobius_commutator_diagonal (τ : EnergyBand) {a : V} {v w : W} {d h : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a)
    (hv : v ∈ M.bandGrade τ h) (hw : w ∈ M.bandGrade τ h) (n : ℕ) :
    inner ℂ v ((((LocalSkewFlow.commutatorOperator (R := ℂ) M.mobiusGenerator)^n)
      (M.physicalMode a d 1)) w) =
       (MobiusCoefficients.coeff d n 0 : ℂ) * inner ℂ v (M.physicalMode a d 0 w) := by
  rw [M.mobius_commutator_power ha hq]
  let l : Module.End ℂ W →ₗ[ℝ] ℂ :=
    ((innerSL ℂ v).toLinearMap.comp (LinearMap.applyₗ w)).restrictScalars ℝ
  have hl (m : ℤ) (hm : m ≠ 0) : l (M.physicalMode a d m) = 0 :=
    Q.physicalMode_diagonal_zero τ ha hv hw m hm
  have he := MobiusCoefficients.diagonal_representation (M.physicalMode a d) l hl
    (MobiusCoefficients.coeff d n)
  change inner ℂ v (((MobiusCoefficients.representation (M.physicalMode a d))
    (MobiusCoefficients.coeff d n)) w) =
      (MobiusCoefficients.coeff d n 0) • inner ℂ v (M.physicalMode a d 0 w) at he
  simpa only [Complex.real_smul] using he

theorem summable_norm_mobiusEvolutionTerm (τ : EnergyBand) {N : ℕ} {x : W}
    (hx : x ∈ M.energyCutoff τ N) {t : ℝ} (ht : 2 * |t| * 8 < 1) :
    Summable (fun n => ‖LocalSkewFlow.skewExpTerm M.mobiusGenerator t n x‖) :=
  LocalSkewFlow.summable_norm_skewExpTerm _ (by norm_num : (0:ℝ) ≤ 8)
    (Q.mobiusGenerator_pow_norm τ hx) ht

theorem summable_norm_mobiusInserted {a : V} (hp : M.PolynomialEnergyBound a)
    (d : ℕ) (m : ℤ) {t : ℝ}
    (ht : 2 * |t| * (8 : ℝ) < 1) (τ : EnergyBand) {N : ℕ} {v : W}
    (hN : v ∈ M.energyCutoff τ N) :
    Summable (fun n => ‖LocalSkewFlow.insertedExpTerm M.mobiusGenerator
      (M.physicalMode a d m) t n v‖) := by
  obtain ⟨D, hD, r, hT⟩ := Q.physicalMode_polynomial_cutoff hp d m
  apply LocalSkewFlow.summable_norm_insertedExpTerm _ _
    (by norm_num : (0:ℝ) ≤ 8) hD.le
    (Q.mobiusGenerator_pow_norm τ hN) (N := N) (r := r) _ ht
  intro n
  simpa only [Nat.cast_add, add_assoc] using
    hT τ (Q.mobiusGenerator_pow_mem_energyCutoff τ hN n)

 

theorem mobius_diagonal_compression (τ : EnergyBand) {a : V} {v w : W} {d h : ℕ}
    (hp : M.PolynomialEnergyBound a) (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a)
    (hv : v ∈ M.bandGrade τ h) (hw : w ∈ M.bandGrade τ h) {t : ℝ}
    (ht : 2 * |t| * (8 : ℝ) < 1) :
    inner ℂ (LocalSkewFlow.skewExp M.mobiusGenerator (-t) v)
      (LocalSkewFlow.insertedExp M.mobiusGenerator (M.physicalMode a d 1) (-t) w) =
        (MobiusCoefficients.mean d t : ℂ) * inner ℂ v (M.physicalMode a d 0 w) := by
  have ht' : 2 * |-t| * (8 : ℝ) < 1 := by simpa using ht
  rw [LocalSkewFlow.inner_skewExp_inserted _ _ Q.mobiusGenerator_skew t v w
    (Q.summable_norm_mobiusEvolutionTerm τ (M.grade_le_energyCutoff τ le_rfl hv) ht')
    (Q.summable_norm_mobiusInserted hp d 1 ht' τ (M.grade_le_energyCutoff τ le_rfl hw))]
  simp_rw [Q.mobius_commutator_diagonal τ ha hq hv hw]
  calc
    _ = ∑' n, ((t^n / (n.factorial : ℝ) * MobiusCoefficients.coeff d n 0 : ℝ) : ℂ) *
        inner ℂ v (M.physicalMode a d 0 w) := by
      apply tsum_congr
      intro n
      push_cast
      ring
    _ = _ := by rw [tsum_mul_right, ← Complex.ofReal_tsum]; rfl

 

theorem mobiusInserted_bound {a : V} (hp : M.PolynomialEnergyBound a) (d : ℕ) (m : ℤ)
    {t : ℝ} (ht : 4 * |t| * (8 : ℝ) < 1) :
    ∃ B E : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ ∀ (τ : EnergyBand) (F : ℕ → ℝ),
      (∀ N, 0 ≤ F N) →
      (∀ N, ∀ v ∈ M.energyCutoff τ N, ‖M.physicalMode a d m v‖ ≤ F N * ‖v‖) →
      ∀ N, ∀ v ∈ M.energyCutoff τ N,
        ‖LocalSkewFlow.insertedExp M.mobiusGenerator (M.physicalMode a d m) t v‖ ≤
          (F (2 * N) * B + E) * ‖v‖ := by
  let C : ℝ := 8
  have hC : 0 ≤ C := by norm_num [C]
  obtain ⟨D, hD, r, hT⟩ := Q.physicalMode_polynomial_cutoff hp d m
  let B := 1 + (1 - 4 * |t| * C)⁻¹
  let E := D * (2 : ℝ)^r * ∑' n : ℕ, (1 + (n : ℝ))^r * (4 * |t| * C)^n
  have hB : 0 ≤ B := by
    dsimp [B]
    have hh : 0 < 1 - 4 * |t| * C := by linarith
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg (mul_nonneg hD.le (by positivity)) (tsum_nonneg (fun _ => by positivity))
  refine ⟨B, E, hB, hE, ?_⟩
  intro τ F hFnonneg hF N v hv
  have hF0 : 0 ≤ F (2*N) := hFnonneg _
  have hq : 2 * |t| * C < 1 := by nlinarith [mul_nonneg (abs_nonneg t) hC]
  have hiter := Q.mobiusGenerator_pow_norm τ hv
  have hTv (n : ℕ) : ‖M.physicalMode a d m ((M.mobiusGenerator^n) v)‖ ≤
      D * (1 + (N : ℝ) + n)^r * ‖(M.mobiusGenerator^n) v‖ := by
    simpa only [Nat.cast_add, add_assoc] using hT τ (Q.mobiusGenerator_pow_mem_energyCutoff τ hv n)
  have hs := Q.summable_norm_mobiusInserted hp d m hq τ hv
  have he := LocalSkewFlow.apply_skewTaylor_add_tail M.mobiusGenerator (M.physicalMode a d m)
    (N := N) hs
  have hbnd := LocalSkewFlow.skewTaylor_norm_bound M.mobiusGenerator Q.mobiusGenerator_skew hC hiter ht
  have htail := LocalSkewFlow.insertedExp_tail_norm_bound M.mobiusGenerator (M.physicalMode a d m)
    hC hD.le hiter hTv ht
  rw [← he]
  calc
    _ ≤ ‖(M.physicalMode a d m (LocalSkewFlow.skewTaylor M.mobiusGenerator t N v) : W)‖ +
        ‖∑' n, LocalSkewFlow.insertedExpTerm M.mobiusGenerator (M.physicalMode a d m) t (n + N) v‖ := by
      simpa only [UniformSpace.Completion.norm_coe] using norm_add_le
        ((M.physicalMode a d m (LocalSkewFlow.skewTaylor M.mobiusGenerator t N v) : W) : UniformSpace.Completion W)
        (∑' n, LocalSkewFlow.insertedExpTerm M.mobiusGenerator (M.physicalMode a d m) t (n + N) v)
    _ ≤ F (2 * N) * (B * ‖v‖) + E * ‖v‖ := by
      apply add_le_add _ htail
      apply (hF (2 * N) _ ?_).trans
      · exact mul_le_mul_of_nonneg_left hbnd hF0
      · simpa only [two_mul] using Q.mobiusTaylor_mem_energyCutoff τ hv t N
    _ = _ := by ring

 

theorem zeroMode_transfer {a : V} {d : ℕ}
    (hp : M.PolynomialEnergyBound a) (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : EnergyBand) (F : ℕ → ℝ), (∀ N, 1 ≤ F N) →
      (∀ N, ∀ v ∈ M.energyCutoff τ N, ‖M.physicalMode a d 1 v‖ ≤ F N * ‖v‖) →
      ∀ h, ∀ w ∈ M.bandGrade τ h, ‖M.physicalMode a d 0 w‖ ≤ C * F (2 * h) * ‖w‖ := by
  let L : ℝ := 8
  have hL : 0 < L := by norm_num [L]
  let t : ℝ := (16 * L)⁻¹
  have ht : 0 < t := by dsimp [t]; positivity
  have h4 : 4 * |t| * L < 1 := by
    rw [abs_of_pos ht]
    dsimp [t]
    field_simp
    nlinarith
  have h4' : 4 * |-t| * L < 1 := by simpa using h4
  have h2 : 2 * |t| * L < 1 := by nlinarith [mul_nonneg (abs_nonneg t) hL.le]
  obtain ⟨B, E, hB, hE, hBE⟩ := Q.mobiusInserted_bound hp d 1 h4'
  let c := MobiusCoefficients.mean d t
  have hc : 0 < c := MobiusCoefficients.mean_pos hd ht
  refine ⟨(1 + B + E) / c, div_pos (by positivity) hc, ?_⟩
  intro τ F hF hbound h w hw
  let v := M.physicalMode a d 0 w
  have hv : v ∈ M.bandGrade τ h := M.physicalMode_mem_band τ ha hw 0 (by omega)
  have hn := hBE τ F (fun N => zero_le_one.trans (hF N)) hbound h w (M.grade_le_energyCutoff τ le_rfl hw)
  have hi := Q.mobius_diagonal_compression τ hp ha hq hv hw h2
  have he : ‖LocalSkewFlow.skewExp M.mobiusGenerator (-t) v‖ = ‖v‖ :=
    LocalSkewFlow.norm_skewExp _ Q.mobiusGenerator_skew (-t) v
      (Q.summable_norm_mobiusEvolutionTerm τ (M.grade_le_energyCutoff τ le_rfl hv) (by simpa using h2))
  have hh : c * ‖v‖^2 ≤ ‖v‖ * ((F (2 * h) * B + E) * ‖w‖) := by
    calc
      _ = ‖(c : ℂ) * inner ℂ v v‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
          inner_self_eq_norm_sq_to_K]
        simp
      _ = ‖inner ℂ (LocalSkewFlow.skewExp M.mobiusGenerator (-t) v)
        (LocalSkewFlow.insertedExp M.mobiusGenerator (M.physicalMode a d 1) (-t) w)‖ :=
          congrArg norm hi.symm
      _ ≤ ‖LocalSkewFlow.skewExp M.mobiusGenerator (-t) v‖ *
          ‖LocalSkewFlow.insertedExp M.mobiusGenerator (M.physicalMode a d 1) (-t) w‖ :=
            norm_inner_le_norm _ _
      _ ≤ _ := by rw [he]; exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)
  by_cases hv0 : ‖v‖ = 0
  · change ‖v‖ ≤ _
    rw [hv0]
    have hFpos := (hF (2 * h)).trans_lt' (by norm_num : (0 : ℝ) < 1)
    positivity
  have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv0)
  have hvb : c * ‖v‖ ≤ (F (2 * h) * B + E) * ‖w‖ := by
    apply (mul_le_mul_iff_of_pos_left hvpos).mp
    nlinarith [hh]
  change ‖v‖ ≤ _
  apply (mul_le_mul_iff_of_pos_right hc).mp
  calc
    ‖v‖ * c ≤ (F (2 * h) * B + E) * ‖w‖ := by nlinarith [hvb]
    _ ≤ ((1 + B + E) * F (2 * h)) * ‖w‖ := by
      gcongr
      nlinarith [hF (2 * h)]
    _ = (((1 + B + E) / c * F (2 * h) * ‖w‖) * c) := by field_simp

end UnitaryStructure

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
