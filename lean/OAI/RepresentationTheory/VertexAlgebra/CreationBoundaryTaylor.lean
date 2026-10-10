import Mathlib

namespace OAI

noncomputable section
namespace CreationBoundary
open Filter Topology

theorem pow_remainder_le {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖z^n - w^n - (n:ℂ)*w^(n-1)*(z-w)‖ ≤ (n:ℝ)^2 * ‖z-w‖^2 := by
  have H : ∀ n : ℕ, ‖z^(n+1)-w^(n+1)-((n:ℂ)+1)*w^n*(z-w)‖ ≤
      ((n:ℝ)+1)^2*‖z-w‖^2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have he : z^((n+1)+1)-w^((n+1)+1)-(((n+1:ℕ):ℂ)+1)*w^(n+1)*(z-w) =
          z*(z^(n+1)-w^(n+1)-((n:ℂ)+1)*w^n*(z-w)) +
            ((n:ℂ)+1)*w^n*(z-w)^2 := by
        push_cast
        simp only [pow_succ]
        ring
      rw [he]
      have hn : ‖(n:ℂ)+1‖ = (n:ℝ)+1 := by
        rw [← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add_one]
      have hnw : ‖w‖^n ≤ 1 := pow_le_one₀ (norm_nonneg w) hw
      calc
        _ ≤ ‖z*(z^(n+1)-w^(n+1)-((n:ℂ)+1)*w^n*(z-w))‖ +
            ‖((n:ℂ)+1)*w^n*(z-w)^2‖ := norm_add_le _ _
        _ ≤ 1*(((n:ℝ)+1)^2*‖z-w‖^2) + ((n:ℝ)+1)*1*‖z-w‖^2 := by
          simp only [norm_mul, norm_pow, hn]
          gcongr
        _ ≤ _ := by push_cast; nlinarith [sq_nonneg ‖z-w‖]
  cases n with
  | zero => simp
  | succ n => simpa only [Nat.add_sub_cancel, Nat.cast_add_one] using H n

def powerSum (c : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n, c n*z^n

def powerDeriv (c : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n, c n*(n:ℂ)*z^(n-1)

def weightTwo (c : ℕ → ℂ) (n : ℕ) : ℝ := ‖c n‖*(1+(n:ℝ))^2

theorem summable_power {c : ℕ → ℂ} (hc : Summable (weightTwo c))
    {z : ℂ} (hz : ‖z‖ ≤ 1) : Summable (fun n => ‖c n*z^n‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hc
  intro n
  simp only [weightTwo, norm_mul, norm_pow]
  gcongr
  calc
    ‖z‖^n ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
    _ ≤ (1+(n:ℝ))^2 := by nlinarith [Nat.cast_nonneg (α:=ℝ) n]

theorem summable_deriv {c : ℕ → ℂ} (hc : Summable (weightTwo c))
    {z : ℂ} (hz : ‖z‖ ≤ 1) : Summable (fun n => ‖c n*(n:ℂ)*z^(n-1)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hc
  intro n
  simp only [weightTwo, norm_mul, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ ‖c n‖*(n:ℝ)*1 := by gcongr; exact pow_le_one₀ (norm_nonneg _) hz
    _ ≤ _ := by
      rw [mul_one]
      gcongr
      nlinarith [Nat.cast_nonneg (α:=ℝ) n]

theorem powerSum_remainder_norm {c : ℕ → ℂ} (hc : Summable (weightTwo c))
    {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖powerSum c z - powerSum c w - (z-w)*powerDeriv c w‖ ≤
      (∑' n, weightTwo c n)*‖z-w‖^2 := by
  have hs1 := summable_power hc hz
  have hs2 := summable_power hc hw
  have hsd := summable_deriv hc hw
  have he : powerSum c z - powerSum c w - (z-w)*powerDeriv c w =
      ∑' n, c n*(z^n-w^n-(n:ℂ)*w^(n-1)*(z-w)) := by
    simp only [powerSum, powerDeriv]
    rw [← hs1.of_norm.tsum_sub hs2.of_norm, ← tsum_mul_left,
      ← (hs1.of_norm.sub hs2.of_norm).tsum_sub (hsd.of_norm.mul_left (z-w))]
    congr 1
    funext n
    ring
  rw [he]
  have hr : Summable (fun n => ‖c n*(z^n-w^n-(n:ℂ)*w^(n-1)*(z-w))‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
      ((hs1.add hs2).add (hsd.mul_left ‖z-w‖))
    intro n
    calc
      _ = ‖(c n*z^n-c n*w^n)-(z-w)*(c n*(n:ℂ)*w^(n-1))‖ := by congr 1; ring
      _ ≤ ‖c n*z^n-c n*w^n‖ + ‖(z-w)*(c n*(n:ℂ)*w^(n-1))‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_mul]; gcongr; exact norm_sub_le _ _
  calc
    _ ≤ ∑' n, ‖c n*(z^n-w^n-(n:ℂ)*w^(n-1)*(z-w))‖ := norm_tsum_le_tsum_norm hr
    _ ≤ ∑' n, weightTwo c n*‖z-w‖^2 := by
      apply Summable.tsum_le_tsum _ hr (hc.mul_right _)
      intro n
      rw [norm_mul]
      calc
        _ ≤ ‖c n‖*((n:ℝ)^2*‖z-w‖^2) := by
          gcongr
          exact pow_remainder_le hz hw n
        _ ≤ weightTwo c n*‖z-w‖^2 := by
          dsimp [weightTwo]
          rw [← mul_assoc]
          gcongr
          linarith
    _ = _ := tsum_mul_right

end CreationBoundary

end

end OAI
