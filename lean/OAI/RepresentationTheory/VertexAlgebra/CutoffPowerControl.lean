import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.GeneratorSharpGrowth

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
def CutoffPowerControl (Y : ℕ → ℝ) (P : ℕ) (f : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N, f N^P ≤ C*Y N

theorem cutoffPowerControl_add {Y f g : ℕ → ℝ} {P : ℕ}
    (hf : ∀ N, 0 ≤ f N) (hg : ∀ N, 0 ≤ g N)
    (Hf : CutoffPowerControl Y P f) (Hg : CutoffPowerControl Y P g) :
    CutoffPowerControl Y P (fun N => f N+g N) := by
  obtain ⟨C, hC, HC⟩ := Hf
  obtain ⟨D, hD, HD⟩ := Hg
  refine ⟨2^(P-1)*(C+D), by positivity, ?_⟩
  intro N
  calc
    _ ≤ 2^(P-1)*(f N^P+g N^P) := add_pow_le (hf N) (hg N) P
    _ ≤ 2^(P-1)*(C*Y N+D*Y N) := by gcongr; exacts [HC N, HD N]
    _ = _ := by ring

theorem cutoffPowerControl_sum {Y : ℕ → ℝ} {P : ℕ}
    (hP : 1 ≤ P) {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ s, ∀ N, 0 ≤ f i N)
    (H : ∀ i ∈ s, CutoffPowerControl Y P (f i)) :
    CutoffPowerControl Y P (fun N => ∑ i ∈ s, f i N) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, by simp [show P ≠ 0 by omega]⟩
  | @insert i s hi ih =>
    have hsum := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => H j (Finset.mem_insert_of_mem hj))
    have h := cutoffPowerControl_add (hf i (Finset.mem_insert_self _ _))
      (fun N => Finset.sum_nonneg (fun j hj => hf j (Finset.mem_insert_of_mem hj) N))
      (H i (Finset.mem_insert_self _ _)) hsum
    simpa only [Finset.sum_insert hi] using h

theorem cutoffPowerControl_one {Y : ℕ → ℝ} (hY : ∀ N, 1 ≤ Y N) (P : ℕ) :
    CutoffPowerControl Y P (fun _ => 1) :=
  ⟨1, zero_le_one, by simpa using hY⟩

 

theorem root_lift_power_bound {q X C : ℝ} {p P : ℕ} (hq : 0 ≤ q) (hX : 0 ≤ X)
    (hC : 0 ≤ C) (hp : 1 ≤ p) (hpP : p ≤ P)
    (hroot : q^((p : ℝ)⁻¹) ≤ X) (H : q ≤ C*X^(p-1)) :
    (q^((p : ℝ)⁻¹))^P ≤ C*X^(P-1) := by
  have hqroot := Real.rpow_nonneg hq ((p : ℝ)⁻¹)
  calc
    _ = (q^((p : ℝ)⁻¹))^p * (q^((p : ℝ)⁻¹))^(P-p) := by
      rw [← pow_add, Nat.add_sub_of_le hpP]
    _ = q*(q^((p : ℝ)⁻¹))^(P-p) := by
      rw [Real.rpow_inv_natCast_pow hq (by omega)]
    _ ≤ (C*X^(p-1))*X^(P-p) := by gcongr
    _ = _ := by rw [mul_assoc, ← pow_add, show p-1+(P-p) = P-1 by omega]

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 

theorem sharpMajorant_power_contraction (D : ℕ) (hD : 2 ≤ D) (S : ℕ → Finset V)
    (hS : ∀ d, ∀ a ∈ S d, 1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧
      A.IsQuasiPrimary a ∧ U.IsHermitian d a)
    (hp : A.PolynomialEnergyBounds)
    (H : ∀ e, ∀ b ∈ A.grade e, A.SharpGrowth (A.sharpMajorant D S) b e) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N,
      A.sharpMajorant D S N^(2*D) ≤ C*A.sharpMajorant D S (2*N)^(2*D-1) := by
  classical
  let X := A.sharpMajorant D S
  let Y : ℕ → ℝ := fun N => X (2*N)^(2*D-1)
  have hX := A.one_le_sharpMajorant D S
  have hm := A.sharpMajorant_mono D S
  have hpositive (d : ℕ) (a : V) (N : ℕ) :
      0 ≤ (A.sharpColumnQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹ +
        (A.sharpZeroQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹ :=
    add_nonneg (Real.rpow_nonneg (A.sharpColumnQuantity_nonneg a d N) _)
      (Real.rpow_nonneg (A.sharpZeroQuantity_nonneg a d N) _)
  have Hsum : CutoffPowerControl Y (2*D) (fun N =>
      ∑ d ∈ Finset.range (D+1), ∑ a ∈ S d,
        ((A.sharpColumnQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹ +
         (A.sharpZeroQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹)) := by
    apply cutoffPowerControl_sum (by omega)
      (hf := fun d _ N => Finset.sum_nonneg (fun a _ => hpositive d a N))
    intro d hd
    apply cutoffPowerControl_sum (by omega) (hf := fun a _ N => hpositive d a N)
    intro a haS
    obtain ⟨hdpos, hdD, ha, hq, hh⟩ := hS d a haS
    obtain ⟨C, hC, HC⟩ := U.generator_quantities_contraction hX hm hp H ha hdpos hq hh
    apply cutoffPowerControl_add
      (fun N => Real.rpow_nonneg (A.sharpColumnQuantity_nonneg a d N) _)
      (fun N => Real.rpow_nonneg (A.sharpZeroQuantity_nonneg a d N) _)
    · refine ⟨C, hC, ?_⟩
      intro N
      exact root_lift_power_bound (A.sharpColumnQuantity_nonneg a d N)
        (zero_le_one.trans (hX (2*N))) hC (by omega) (by omega)
        (((A.root_sharpQuantity_le D S hdD haS).1).trans (hm (by omega : N ≤ 2*N))) (HC N).1
    · refine ⟨C, hC, ?_⟩
      intro N
      exact root_lift_power_bound (A.sharpZeroQuantity_nonneg a d N)
        (zero_le_one.trans (hX (2*N))) hC (by omega) (by omega)
        (((A.root_sharpQuantity_le D S hdD haS).2).trans (hm (by omega : N ≤ 2*N))) (HC N).2
  have Hraw : CutoffPowerControl Y (2*D) (A.rawSharpMajorant D S) :=
    cutoffPowerControl_add (fun _ => zero_le_one)
      (fun N => Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun a _ => hpositive d a N)))
      (cutoffPowerControl_one (fun N => one_le_pow₀ (hX (2*N))) (2*D)) Hsum
  obtain ⟨C, hC, HC⟩ := Hraw
  refine ⟨C+1, by linarith, ?_⟩
  intro N
  obtain ⟨n, hn, he⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (N+1))
    (by simp) (A.rawSharpMajorant D S)
  change ((Finset.range (N+1)).sup' (by simp) (A.rawSharpMajorant D S))^(2*D) ≤ _
  rw [he]
  apply (HC n).trans
  have hXn := zero_le_one.trans (hX (2*n))
  have hnN : n ≤ N := by have := Finset.mem_range.mp hn; omega
  change C*X (2*n)^(2*D-1) ≤ (C+1)*X (2*N)^(2*D-1)
  gcongr
  · exact le_add_of_nonneg_right zero_le_one
  · exact hm (by omega)

end UnitaryStructure
end CFTTypeVOA

def PolynomialCutoffControl (f : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ N, f N ≤ C*(N+1 : ℝ)^p

theorem polynomialCutoffControl_add {f g : ℕ → ℝ}
    (Hf : PolynomialCutoffControl f) (Hg : PolynomialCutoffControl g) :
    PolynomialCutoffControl (fun N => f N+g N) := by
  obtain ⟨C, hC, p, HC⟩ := Hf
  obtain ⟨D, hD, q, HD⟩ := Hg
  refine ⟨C+D, add_nonneg hC hD, p+q, ?_⟩
  intro N
  have hN : 1 ≤ (N+1 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have Hp := pow_le_pow_right₀ hN (show p ≤ p+q by omega)
  have Hq := pow_le_pow_right₀ hN (show q ≤ p+q by omega)
  calc
    _ ≤ C*(N+1 : ℝ)^p+D*(N+1 : ℝ)^q := add_le_add (HC N) (HD N)
    _ ≤ C*(N+1 : ℝ)^(p+q)+D*(N+1 : ℝ)^(p+q) := by gcongr
    _ = _ := by ring

theorem polynomialCutoffControl_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (H : ∀ i ∈ s, PolynomialCutoffControl (f i)) :
    PolynomialCutoffControl (fun N => ∑ i ∈ s, f i N) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, 0, by simp⟩
  | @insert i s hi ih =>
    have h := polynomialCutoffControl_add (H i (Finset.mem_insert_self _ _))
      (ih (fun j hj => H j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using h

theorem polynomialCutoffControl_one : PolynomialCutoffControl (fun _ => 1) :=
  ⟨1, zero_le_one, 0, by simp⟩

theorem rpow_inv_nat_le_one_add {q : ℝ} (hq : 0 ≤ q) {p : ℕ} (hp : 1 ≤ p) :
    q^((p : ℝ)⁻¹) ≤ 1+q := by
  have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  rcases le_total q 1 with hq1 | hq1
  · exact (Real.rpow_le_one hq hq1 (by positivity)).trans (le_add_of_nonneg_right hq)
  · apply (Real.rpow_le_self_of_one_le hq1 ((inv_le_one₀ hp0).mpr hpR)).trans
    linarith

theorem polynomialCutoffControl_root {f : ℕ → ℝ} (hf : ∀ N, 0 ≤ f N)
    (H : PolynomialCutoffControl f) {p : ℕ} (hp : 1 ≤ p) :
    PolynomialCutoffControl (fun N => f N^((p : ℝ)⁻¹)) := by
  obtain ⟨C, hC, k, HC⟩ := polynomialCutoffControl_add polynomialCutoffControl_one H
  exact ⟨C, hC, k, fun N => (rpow_inv_nat_le_one_add (hf N) hp).trans (HC N)⟩

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 

theorem positiveColumnNorm_sq_polynomial {a : V} (hp : A.PolynomialEnergyBound a)
    (d : ℕ) (hd : 1 ≤ d) : PolynomialCutoffControl (fun N => A.positiveColumnNorm a d N^2) := by
  obtain ⟨C, hC, p, k, HC⟩ := hp
  let B := C*(d+2 : ℝ)^p
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have Hmode (N m : ℕ) (hm : m ≤ N) (v : V) (hv : v ∈ A.energyCutoff N) :
      ‖A.physicalMode a d m v‖ ≤ B*(N+1 : ℝ)^(p+k)*‖v‖ := by
    have hmR : (m : ℝ) ≤ N := by exact_mod_cast hm
    have hdR : 1 ≤ (d : ℝ) := by exact_mod_cast hd
    have hcoef : 1+|(((m : ℤ)+d-1 : ℤ) : ℝ)| ≤ (d+2 : ℝ)*(N+1 : ℝ) := by
      push_cast
      rw [abs_of_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m])]
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    have HK := U.energyShift_pow_norm_on_cutoff hv k
    change ‖mode A.fields a ((m : ℤ)+d-1) v‖ ≤ _
    calc
      _ ≤ C*(1+|(((m : ℤ)+d-1 : ℤ) : ℝ)|)^p*‖(A.energyShift^k) v‖ := HC _ _
      _ ≤ C*((d+2 : ℝ)*(N+1 : ℝ))^p*((N+1 : ℝ)^k*‖v‖) := by
        have HK' : ‖(A.energyShift^k) v‖ ≤ (N+1 : ℝ)^k*‖v‖ := by simpa only [add_comm] using HK
        gcongr
      _ = _ := by dsimp [B]; rw [mul_pow, pow_add]; ring
  refine ⟨B^2, sq_nonneg _, 2*(p+k)+1, ?_⟩
  intro N
  apply positiveColumnNorm_sq_le (by positivity)
  intro v hv
  calc
    _ ≤ ∑ m ∈ Finset.range (N+1), (B*(N+1 : ℝ)^(p+k)*‖v‖)^2 := by
      apply Finset.sum_le_sum
      intro m hm
      exact pow_le_pow_left₀ (norm_nonneg _) (Hmode N m (by have := Finset.mem_range.mp hm; omega) v hv) 2
    _ = (N+1 : ℝ)*(B*(N+1 : ℝ)^(p+k)*‖v‖)^2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    _ = (B^2*(N+1 : ℝ)^(2*(p+k)+1))*‖v‖^2 := by rw [pow_succ]; ring

theorem sharpQuantities_polynomial {a : V} (hp : A.PolynomialEnergyBound a)
    (d : ℕ) (hd : 1 ≤ d) :
    PolynomialCutoffControl (A.sharpColumnQuantity a d) ∧
      PolynomialCutoffControl (A.sharpZeroQuantity a d) := by
  obtain ⟨C, hC, p, HC⟩ := U.positiveColumnNorm_sq_polynomial hp d hd
  constructor
  · refine ⟨C, hC, p, ?_⟩
    intro N
    apply le_trans _ (HC N)
    exact div_le_self (sq_nonneg _) (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]))
  · refine ⟨C, hC, p, ?_⟩
    intro N
    apply le_trans _ (HC N)
    apply le_trans (div_le_self (sq_nonneg _) (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) N])))
    exact pow_le_pow_left₀ (norm_nonneg (A.zeroModeOnCutoff a d N))
      (A.zeroModeCutoffNorm_le_column a d N) 2

 

theorem sharpMajorant_polynomial (D : ℕ) (S : ℕ → Finset V)
    (hS : ∀ d, ∀ a ∈ S d, 1 ≤ d) (hp : A.PolynomialEnergyBounds) :
    PolynomialCutoffControl (A.sharpMajorant D S) := by
  classical
  have Hraw : PolynomialCutoffControl (A.rawSharpMajorant D S) := by
    apply polynomialCutoffControl_add polynomialCutoffControl_one
    apply polynomialCutoffControl_sum
    intro d hd
    apply polynomialCutoffControl_sum
    intro a ha
    have HQ := U.sharpQuantities_polynomial (hp a) d (hS d a ha)
    exact polynomialCutoffControl_add
      (polynomialCutoffControl_root (A.sharpColumnQuantity_nonneg a d) HQ.1 (by have := hS d a ha; omega))
      (polynomialCutoffControl_root (A.sharpZeroQuantity_nonneg a d) HQ.2 (by have := hS d a ha; omega))
  obtain ⟨C, hC, p, HC⟩ := Hraw
  refine ⟨C, hC, p, ?_⟩
  intro N
  apply Finset.sup'_le
  intro n hn
  apply (HC n).trans
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (show n ≤ N by have := Finset.mem_range.mp hn; omega)
  gcongr

end UnitaryStructure
end CFTTypeVOA

open Filter
 

theorem multiplicative_cutoff_log_bound (b : ℕ → ℝ) (K : ℕ) (hK : 1 ≤ K)
    (ρ c C s : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hc : 0 ≤ c)
    (hstart : ∀ N, 1 ≤ N → b N ≤ C + s * Real.log N)
    (hstep : ∀ N, 1 ≤ N → b N ≤ c + ρ * b (K * N)) :
    ∀ N, 1 ≤ N → b N ≤ c / (1 - ρ) := by
  let B := c / (1 - ρ)
  have hden : 0 < 1 - ρ := sub_pos.mpr hρ1
  have hB0 : 0 ≤ B := div_nonneg hc hden.le
  have hB : c + ρ * B = B := by dsimp [B]; field_simp; ring
  have hit (j : ℕ) : ∀ N, 1 ≤ N → b N - B ≤ ρ ^ j * b (K ^ j * N) := by
    induction j with
    | zero => intro N hN; simpa using sub_le_self (b N) hB0
    | succ j ih =>
      intro N hN
      have hKN : 1 ≤ K * N := by nlinarith
      calc
        _ ≤ ρ * (b (K * N) - B) := by nlinarith [hstep N hN]
        _ ≤ ρ * (ρ^j * b (K^j * (K * N))) :=
          mul_le_mul_of_nonneg_left (ih _ hKN) hρ0
        _ = _ := by
          rw [show K^j * (K * N) = K^(j+1) * N by rw [pow_succ]; ring, pow_succ]
          ring
  intro N hN
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hb (j : ℕ) : b N - B ≤
      ρ ^ j * (C + s * Real.log N + s * (j : ℝ) * Real.log K) := by
    apply (hit j N hN).trans
    have hp : 1 ≤ K^j * N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (pow_ne_zero _ (by omega)) (by omega))
    have he : Real.log ((K^j * N : ℕ) : ℝ) = (j : ℝ) * Real.log K + Real.log N := by
      push_cast
      rw [Real.log_mul (pow_ne_zero _ hKpos.ne') hNpos.ne', Real.log_pow]
    have h := mul_le_mul_of_nonneg_left (hstart _ hp) (pow_nonneg hρ0 j)
    rw [he] at h
    convert h using 1
    ring
  have ht : Tendsto (fun j : ℕ =>
      ρ ^ j * (C + s * Real.log N + s * (j : ℝ) * Real.log K)) atTop (nhds 0) := by
    have h₀ := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
    have h₁ := tendsto_pow_const_mul_const_pow_of_lt_one 1 hρ0 hρ1
    have h := (h₀.const_mul (C + s * Real.log N)).add (h₁.const_mul (s * Real.log K))
    convert h using 1
    · ext j; ring
    · simp
  have hlast : b N - B ≤ 0 := ge_of_tendsto' ht hb
  exact sub_nonpos.mp hlast

 

theorem polynomial_power_contraction_bounded (X : ℕ → ℝ) (hX : ∀ N, 1 ≤ X N)
    (hm : Monotone X) (hp : PolynomialCutoffControl X)
    (K P : ℕ) (hK : 1 ≤ K) (hP : 1 ≤ P) (C : ℝ) (hC : 1 ≤ C)
    (H : ∀ N, X N^P ≤ C*X (K*N)^(P-1)) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ N, X N ≤ B := by
  obtain ⟨D, hD, p, HD⟩ := hp
  let A := (D+1)*2^p
  have hA : 0 < A := by dsimp [A]; positivity
  have hPR : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hPR1 : 1 ≤ (P : ℝ) := by exact_mod_cast hP
  let ρ : ℝ := 1-(P : ℝ)⁻¹
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; linarith [(inv_le_one₀ hPR).mpr hPR1]
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith [inv_pos.mpr hPR]
  let c := Real.log C/(P : ℝ)
  have hc : 0 ≤ c := div_nonneg (Real.log_nonneg hC) hPR.le
  have hstart (N : ℕ) (hN : 1 ≤ N) : Real.log (X N) ≤ Real.log A + (p : ℝ)*Real.log N := by
    have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNR : (0 : ℝ) < N := by linarith
    have HX : X N ≤ A*(N : ℝ)^p := by
      apply (HD N).trans
      calc
        _ ≤ (D+1)*(2*(N : ℝ))^p := by gcongr <;> linarith
        _ = _ := by dsimp [A]; rw [mul_pow]; ring
    have HH := Real.log_le_log (by linarith [hX N] : 0 < X N) HX
    rwa [Real.log_mul hA.ne' (pow_pos hNR p).ne', Real.log_pow] at HH
  have hstep (N : ℕ) (_hN : 1 ≤ N) : Real.log (X N) ≤ c+ρ*Real.log (X (K*N)) := by
    have hx : 0 < X N := by linarith [hX N]
    have hy : 0 < X (K*N) := by linarith [hX (K*N)]
    have HL := Real.log_le_log (pow_pos hx P) (H N)
    rw [Real.log_mul (by linarith : C ≠ 0) (pow_ne_zero _ hy.ne'), Real.log_pow,
      Real.log_pow, Nat.cast_sub hP, Nat.cast_one] at HL
    have he : c+ρ*Real.log (X (K*N)) =
        (Real.log C+((P : ℝ)-1)*Real.log (X (K*N)))/(P : ℝ) := by
      dsimp [c, ρ]
      field_simp
    rw [he]
    exact (le_div_iff₀ hPR).mpr (by simpa only [mul_comm] using HL)
  have HB := multiplicative_cutoff_log_bound (fun N => Real.log (X N)) K hK
    ρ c (Real.log A) p hρ0 hρ1 hc hstart hstep
  let B := Real.exp (c/(1-ρ))
  have HB1 : 1 ≤ B := Real.one_le_exp_iff.mpr (div_nonneg hc (by linarith))
  have HBN (N : ℕ) (hN : 1 ≤ N) : X N ≤ B := by
    have hx : 0 < X N := by linarith [hX N]
    simpa [B, Real.exp_log hx] using Real.exp_le_exp.mpr (HB N hN)
  exact ⟨B, HB1, fun N => if hN : 1 ≤ N then HBN N hN else
    (hm (show N ≤ 1 by omega)).trans (HBN 1 le_rfl)⟩

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 

theorem exists_bounded_sharpGrowth (hc : A.toVertexAlgebra.C2Cofinite) :
    ∃ X : ℕ → ℝ, (∀ N, 1 ≤ X N) ∧ Monotone X ∧
      (∃ B : ℝ, 1 ≤ B ∧ ∀ N, X N ≤ B) ∧
      (∀ e, ∀ b ∈ A.grade e, A.SharpGrowth X b e) := by
  obtain ⟨D, hD, S, _hSzero, hS, _hspan, _hcut, H⟩ := U.exists_sharpMajorant hc
  have hp := U.polynomialEnergyBounds hc
  obtain ⟨C, hC, HC⟩ := U.sharpMajorant_power_contraction D hD S hS hp H
  have HB := polynomial_power_contraction_bounded (A.sharpMajorant D S)
    (A.one_le_sharpMajorant D S) (A.sharpMajorant_mono D S)
    (U.sharpMajorant_polynomial D S (fun d a ha => (hS d a ha).1) hp)
    2 (2*D) (by decide) (by omega) C hC HC
  exact ⟨A.sharpMajorant D S, A.one_le_sharpMajorant D S, A.sharpMajorant_mono D S, HB, H⟩

 

theorem optimal_quasiPrimary_cutoff (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a)
    (hh : U.IsHermitian d a) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ N (m : ℤ) v, v ∈ A.energyCutoff N →
      ‖A.physicalMode a d m v‖ ≤ C*(1+|(m : ℝ)|)^(2*d)*(N+1 : ℝ)^(d-1)*‖v‖ := by
  obtain ⟨X, hX, hm, ⟨B, hB, HB⟩, H⟩ := U.exists_bounded_sharpGrowth hc
  obtain ⟨C, hC, HC⟩ := U.nonzeroModes_sharp_bound hX ha hq hh hd (fun e _ b hb => H e b hb)
  obtain ⟨D, hD, HD⟩ := U.zeroMode_sharpGrowth hX hm (U.polynomialEnergyBounds hc a)
    ha hq hh hd (fun e _ b hb => H e b hb)
  let K := (C+D+2)*B^(d-1)
  have hK : 0 < K := by dsimp [K]; positivity
  have Hzero (N : ℕ) (v : V) (hv : v ∈ A.energyCutoff N) :
      ‖A.physicalMode a d 0 v‖ ≤ K*(N+1 : ℝ)^(d-1)*‖v‖ := by
    have Hn := norm_of_sharp_square (zero_le_one.trans (hX (2*N))) hD N (d-1) (d-1) v _ (HD N v hv)
    apply Hn.trans
    calc
      _ ≤ (C+D+2)*(N+1 : ℝ)^(d-1)*B^(d-1)*‖v‖ := by
        have hhX := zero_le_one.trans (hX (2*N))
        gcongr <;> linarith [HB (2*N)]
      _ = _ := by dsimp [K]; ring
  have Hpos (N m : ℕ) (hm : 0 < m) (v : V) (hv : v ∈ A.energyCutoff N) :
      ‖A.physicalMode a d m v‖ ≤ K*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*‖v‖ ∧
      ‖A.physicalMode a d (-(m : ℤ)) v‖ ≤ K*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*‖v‖ := by
    have Hn := HC N m hm v hv
    have hbound : C*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*X N^(d-1)*‖v‖ ≤
        K*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*‖v‖ := by
      have hhX := zero_le_one.trans (hX N)
      calc
        _ ≤ (C+D+2)*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*B^(d-1)*‖v‖ := by
          gcongr
          · linarith
          · exact HB N
        _ = _ := by dsimp [K]; ring
    exact ⟨Hn.1.trans hbound, Hn.2.trans hbound⟩
  refine ⟨K, hK, ?_⟩
  intro N m v hv
  rcases m with m | m
  · by_cases hm0 : m = 0
    · subst m
      simpa using Hzero N v hv
    · simpa only [Int.ofNat_eq_natCast, Int.cast_natCast,
        abs_of_nonneg (show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m), add_comm 1 (m : ℝ)] using
        (Hpos N m (by omega) v hv).1
  · have he : Int.negSucc m = -((m+1 : ℕ) : ℤ) := by omega
    rw [he]
    simpa only [Int.cast_neg, abs_neg, Int.cast_natCast,
      abs_of_nonneg (show (0 : ℝ) ≤ ((m+1 : ℕ) : ℝ) from Nat.cast_nonneg (m+1)),
      add_comm 1 ((m+1 : ℕ) : ℝ)] using (Hpos N (m+1) (by omega) v hv).2

 

theorem physical_energyBound_of_cutoffs {a : V} {d p k : ℕ} {C : ℝ}
    (ha : a ∈ A.grade d) (hC : 0 ≤ C)
    (H : ∀ N (m : ℤ) v, v ∈ A.energyCutoff N →
      ‖A.physicalMode a d m v‖ ≤ C*(1+|(m : ℝ)|)^p*(N+1 : ℝ)^k*‖v‖) :
    ∀ (m : ℤ) v, ‖A.physicalMode a d m v‖ ≤
      C*(1+|(m : ℝ)|)^p*‖(A.energyShift^k) v‖ := by
  classical
  intro m v
  let L := C*(1+|(m : ℝ)|)^p
  have hL : 0 ≤ L := by dsimp [L]; positivity
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  change ‖A.physicalMode a d m v‖^2 ≤ (L*‖(A.energyShift^k) v‖)^2
  rw [physicalMode, U.mode_norm_sq_eq_sum_grades ha]
  calc
    _ ≤ ∑ h ∈ A.gradeSupport v, (L*(1+(h : ℝ))^k*‖A.gradeComponent h v‖)^2 := by
      apply Finset.sum_le_sum
      intro h _
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      simpa only [L, physicalMode, add_comm (h : ℝ) 1] using H h m (A.gradeComponent h v)
        (A.grade_le_energyCutoff le_rfl (A.gradeComponent_mem h v))
    _ = L^2 * ∑ h ∈ A.gradeSupport v, ((1+(h : ℝ))^k*‖A.gradeComponent h v‖)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = _ := by rw [← U.energy_norm_sq_eq_sum_grades]; ring

 

theorem optimal_quasiPrimary_energyBound (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a)
    (hh : U.IsHermitian d a) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℤ) v, ‖A.physicalMode a d m v‖ ≤
      C*(1+|(m : ℝ)|)^(2*d)*‖(A.energyShift^(d-1)) v‖ := by
  obtain ⟨C, hC, H⟩ := U.optimal_quasiPrimary_cutoff hc ha hq hh hd
  exact ⟨C, hC, U.physical_energyBound_of_cutoffs ha hC.le H⟩

 

theorem current_linear_energyBound (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} (ha : a ∈ A.grade 1) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian 1 a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℤ) v, ‖A.physicalMode a 1 m v‖ ≤
      C*(1+|(m : ℝ)|)*‖A.energyShift v‖ := by
  obtain ⟨X, hX, _hm, ⟨B, hB, HB⟩, H⟩ := U.exists_bounded_sharpGrowth hc
  obtain ⟨C, hC, HC⟩ := (H 1 a ha).1
  have HR (N : ℕ) : A.positiveColumnNorm a 1 N ≤ (C+1)*B*(N+1 : ℝ) := by
    have Hsq := positiveColumnNorm_sq_le (by positivity : 0 ≤ C*(N+1 : ℝ)*X N^2)
      (by simpa only [ColumnControl, show 2*1-1=1 by decide, show 2*1=2 by decide, pow_one] using HC N)
    have hXN := zero_le_one.trans (hX N)
    have hCX : C*(N+1 : ℝ)*X N^2 ≤ C*(N+1 : ℝ)*B^2 := by gcongr; exact HB N
    apply (sq_le_sq₀ (A.positiveColumnNorm_nonneg a 1 N) (by positivity)).mp
    apply Hsq.trans (hCX.trans _)
    have hN : 1 ≤ (N+1 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) N]
    have hcc : C ≤ (C+1)^2 := by nlinarith
    calc
      _ ≤ (C+1)^2*(N+1 : ℝ)^2*B^2 := by gcongr; nlinarith
      _ = _ := by ring
  let K := (C+1)*B
  have hK : 0 < K := by dsimp [K]; positivity
  have Hcut (N : ℕ) (m : ℤ) v (hv : v ∈ A.energyCutoff N) :
      ‖A.physicalMode a 1 m v‖ ≤ K*(1+|(m : ℝ)|)^1*(N+1 : ℝ)^1*‖v‖ := by
    have HR' (n : ℕ) : A.positiveColumnNorm a 1 n ≤ K*(n+1 : ℝ) := HR n
    rcases m with m | m
    · apply (A.positive_mode_norm_le_column ha hv m).trans
      simp only [Int.ofNat_eq_natCast, Int.cast_natCast,
        abs_of_nonneg (show (0 : ℝ) ≤ m from Nat.cast_nonneg m), pow_one]
      calc
        _ ≤ K*(N+1 : ℝ)*‖v‖ := mul_le_mul_of_nonneg_right (HR' N) (norm_nonneg _)
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hK.le (by positivity : 0 ≤ (N+1 : ℝ))) (norm_nonneg v),
          mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (mul_nonneg (mul_nonneg hK.le (by positivity : 0 ≤ (N+1 : ℝ))) (norm_nonneg v))]
    · have he : Int.negSucc m = -((m+1 : ℕ) : ℤ) := by omega
      rw [he]
      apply (U.negative_mode_norm_le_column ha hq hh hv (m+1)).trans
      simp only [Int.cast_neg, abs_neg, Int.cast_natCast,
        abs_of_nonneg (show (0 : ℝ) ≤ ((m+1 : ℕ) : ℝ) from Nat.cast_nonneg (m+1)), pow_one]
      calc
        _ ≤ K*((N+(m+1) : ℕ)+1 : ℝ)*‖v‖ := mul_le_mul_of_nonneg_right (HR' (N+(m+1))) (norm_nonneg _)
        _ ≤ _ := by
          have hbase : (((N+(m+1) : ℕ) : ℝ)+1) ≤ (1+((m+1 : ℕ) : ℝ))*(N+1 : ℝ) := by
            push_cast
            have hh := mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (Nat.cast_nonneg (α := ℝ) N)
            nlinarith [Nat.cast_nonneg (α := ℝ) N]
          calc
            _ ≤ K*((1+((m+1 : ℕ) : ℝ))*(N+1 : ℝ))*‖v‖ := by gcongr
            _ = _ := by ring
  refine ⟨K, hK, ?_⟩
  simpa only [pow_one] using U.physical_energyBound_of_cutoffs ha hK.le Hcut

end UnitaryStructure
end CFTTypeVOA

namespace HilbertCore
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
end HilbertCore
end StronglyRationalVOA

end

end OAI
