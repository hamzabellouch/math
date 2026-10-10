import OAI.RepresentationTheory.VertexAlgebra.ModuleSharpContraction

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)
def PolynomialCutoffControl (f : EnergyBand → ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ τ N, f τ N ≤ C*(N+1 : ℝ)^p

theorem polynomialCutoffControl_add {f g : EnergyBand → ℕ → ℝ}
    (Hf : PolynomialCutoffControl f) (Hg : PolynomialCutoffControl g) :
    PolynomialCutoffControl (fun τ N => f τ N+g τ N) := by
  obtain ⟨C, hC, p, HC⟩ := Hf
  obtain ⟨D, hD, q, HD⟩ := Hg
  refine ⟨C+D, add_nonneg hC hD, p+q, ?_⟩
  intro τ N
  have hN : 1 ≤ (N+1 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have Hp := pow_le_pow_right₀ hN (show p ≤ p+q by omega)
  have Hq := pow_le_pow_right₀ hN (show q ≤ p+q by omega)
  calc
    _ ≤ C*(N+1 : ℝ)^p+D*(N+1 : ℝ)^q := add_le_add (HC τ N) (HD τ N)
    _ ≤ C*(N+1 : ℝ)^(p+q)+D*(N+1 : ℝ)^(p+q) := by gcongr
    _ = _ := by ring

theorem polynomialCutoffControl_sum {ι : Type*} (s : Finset ι) (f : ι → EnergyBand → ℕ → ℝ)
    (H : ∀ i ∈ s, PolynomialCutoffControl (f i)) :
    PolynomialCutoffControl (fun τ N => ∑ i ∈ s, f i τ N) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, 0, by simp⟩
  | @insert i s hi ih =>
    have h := polynomialCutoffControl_add (H i (Finset.mem_insert_self _ _))
      (ih (fun j hj => H j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using h

theorem polynomialCutoffControl_one : PolynomialCutoffControl (fun _ _ => 1) :=
  ⟨1, zero_le_one, 0, by simp⟩

theorem polynomialCutoffControl_root {f : EnergyBand → ℕ → ℝ} (hf : ∀ τ N, 0 ≤ f τ N)
    (H : PolynomialCutoffControl f) {p : ℕ} (hp : 1 ≤ p) :
    PolynomialCutoffControl (fun τ N => f τ N^((p : ℝ)⁻¹)) := by
  obtain ⟨C, hC, k, HC⟩ := polynomialCutoffControl_add polynomialCutoffControl_one H
  exact ⟨C, hC, k, fun τ N => (rpow_inv_nat_le_one_add (hf τ N) hp).trans (HC τ N)⟩

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q
theorem positiveColumnNorm_sq_polynomial {a : V} (hp : M.PolynomialEnergyBound a)
    (d : ℕ) (hd : 1 ≤ d) : PolynomialCutoffControl (fun τ N => M.positiveColumnNorm τ a d N^2) := by
  obtain ⟨C, hC, p, k, HC⟩ := hp
  let B := C*(d+2 : ℝ)^p*2^k
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have Hmode (τ : EnergyBand) (N m : ℕ) (hm : m ≤ N) (v : W) (hv : v ∈ M.energyCutoff τ N) :
      ‖M.physicalMode a d m v‖ ≤ B*(N+1 : ℝ)^(p+k)*‖v‖ := by
    have hmR : (m : ℝ) ≤ N := by exact_mod_cast hm
    have hdR : 1 ≤ (d : ℝ) := by exact_mod_cast hd
    have hcoef : 1+|(((m : ℤ)+d-1 : ℤ) : ℝ)| ≤ (d+2 : ℝ)*(N+1 : ℝ) := by
      push_cast
      rw [abs_of_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m])]
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    have HK := Q.energyShift_pow_norm_on_cutoff τ hv k
    change ‖mode M.fields a ((m : ℤ)+d-1) v‖ ≤ _
    calc
      _ ≤ C*(1+|(((m : ℤ)+d-1 : ℤ) : ℝ)|)^p*‖(M.energyShift^k) v‖ := by simpa only [Int.cast_abs] using HC _ _
      _ ≤ C*((d+2 : ℝ)*(N+1 : ℝ))^p*((2*(N+1 : ℝ))^k*‖v‖) := by
        have HK' : ‖(M.energyShift^k) v‖ ≤ (2*(N+1 : ℝ))^k*‖v‖ := by simpa only [add_comm] using HK
        gcongr
      _ = _ := by dsimp [B]; simp only [mul_pow, pow_add]; ring
  refine ⟨B^2, sq_nonneg _, 2*(p+k)+1, ?_⟩
  intro τ N
  apply positiveColumnNorm_sq_le τ (by positivity)
  intro v hv
  calc
    _ ≤ ∑ m ∈ Finset.range (N+1), (B*(N+1 : ℝ)^(p+k)*‖v‖)^2 := by
      apply Finset.sum_le_sum
      intro m hm
      exact pow_le_pow_left₀ (norm_nonneg _) (Hmode τ N m (by have := Finset.mem_range.mp hm; omega) v hv) 2
    _ = (N+1 : ℝ)*(B*(N+1 : ℝ)^(p+k)*‖v‖)^2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    _ = (B^2*(N+1 : ℝ)^(2*(p+k)+1))*‖v‖^2 := by rw [pow_succ]; ring

theorem sharpQuantities_polynomial {a : V} (hp : M.PolynomialEnergyBound a)
    (d : ℕ) (hd : 1 ≤ d) :
    PolynomialCutoffControl (fun τ => M.sharpColumnQuantity τ a d) ∧
      PolynomialCutoffControl (fun τ => M.sharpZeroQuantity τ a d) := by
  obtain ⟨C, hC, p, HC⟩ := Q.positiveColumnNorm_sq_polynomial hp d hd
  constructor
  · refine ⟨C, hC, p, ?_⟩
    intro τ N
    apply le_trans _ (HC τ N)
    exact div_le_self (sq_nonneg _) (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]))
  · refine ⟨C, hC, p, ?_⟩
    intro τ N
    apply le_trans _ (HC τ N)
    apply le_trans (div_le_self (sq_nonneg _) (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) N])))
    exact pow_le_pow_left₀ (norm_nonneg (M.zeroModeOnCutoff τ a d N))
      (M.zeroModeCutoffNorm_le_column τ a d N) 2

 

theorem sharpMajorant_polynomial (D : ℕ) (S : ℕ → Finset V)
    (hS : ∀ d, ∀ a ∈ S d, 1 ≤ d) (hp : M.PolynomialEnergyBounds) :
    PolynomialCutoffControl (fun τ => M.sharpMajorant τ D S) := by
  classical
  have Hraw : PolynomialCutoffControl (fun τ => M.rawSharpMajorant τ D S) := by
    apply polynomialCutoffControl_add polynomialCutoffControl_one
    apply polynomialCutoffControl_sum
    intro d hd
    apply polynomialCutoffControl_sum
    intro a ha
    have HQ := Q.sharpQuantities_polynomial (hp a) d (hS d a ha)
    exact polynomialCutoffControl_add
      (polynomialCutoffControl_root (fun τ => M.sharpColumnQuantity_nonneg τ a d) HQ.1 (by have := hS d a ha; omega))
      (polynomialCutoffControl_root (fun τ => M.sharpZeroQuantity_nonneg τ a d) HQ.2 (by have := hS d a ha; omega))
  obtain ⟨C, hC, p, HC⟩ := Hraw
  refine ⟨C, hC, p, ?_⟩
  intro τ N
  apply Finset.sup'_le
  intro n hn
  apply (HC τ n).trans
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (show n ≤ N by have := Finset.mem_range.mp hn; omega)
  gcongr

end UnitaryStructure

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
