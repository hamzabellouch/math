import Mathlib

namespace OAI

/-! The finite positivity interval for the Jones--Wenzl scalar recurrence. -/
namespace HarmonicArtin.ParabolicIntersections

/-- Quantum integers as a real recurrence, with no trigonometric choices. -/
noncomputable def meshQuantum (δ : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | n+2 => δ*meshQuantum δ (n+1)-meshQuantum δ n

@[simp] lemma meshQuantum_zero (δ : ℝ) : meshQuantum δ 0=0 := rfl
@[simp] lemma meshQuantum_one (δ : ℝ) : meshQuantum δ 1=1 := rfl
lemma meshQuantum_step (δ : ℝ) (n : ℕ) :
    meshQuantum δ (n+2)=δ*meshQuantum δ (n+1)-meshQuantum δ n := rfl

/-- For `δ<2`, the recurrence starting at `0,1` cannot remain strictly
positive. This discrete concavity proof avoids choosing an angle. -/
theorem mesh_quantum_eventually_nonpositive (δ : ℝ) (hδ : δ<2)
    (q : ℕ → ℝ) (hzero : q 0=0) (hone : q 1=1)
    (hrec : ∀ n, q (n+2)=δ*q (n+1)-q n) :
    ∃ n, 0<n ∧ q n≤0 := by
  by_contra hex
  have hpos : ∀ n, 0<n → 0<q n := by
    intro n hn
    by_contra hq
    exact hex ⟨n,hn,le_of_not_gt hq⟩
  have hnonneg : ∀ n, 0≤q n := by
    intro n
    cases n with
    | zero => rw [hzero]
    | succ n => exact (hpos _ (Nat.succ_pos n)).le
  let d : ℕ → ℝ := fun n => q (n+1)-q n
  have hd0 : d 0=1 := by simp only [d,hzero,hone]; norm_num
  have hstep : ∀ n, d (n+1)=d n-(2-δ)*q (n+1) := by
    intro n
    dsimp [d]
    rw [show n+1+1=n+2 by omega,hrec]
    ring
  have hanti : Antitone d := antitone_nat_of_succ_le (fun n => by
    rw [hstep]
    have := hnonneg (n+1)
    nlinarith)
  have hnegative : ∃ n, d n<0 := by
    by_contra hneg
    have hdpos : ∀ n, 0≤d n := by
      intro n
      by_contra hn
      exact hneg ⟨n,lt_of_not_ge hn⟩
    have hmono : Monotone q := monotone_nat_of_le_succ (fun n => by
      have := hdpos n
      dsimp [d] at this
      linarith)
    have hqone : ∀ n, 1≤q (n+1) := by
      intro n
      simpa only [hone] using hmono (Nat.le_add_left 1 n)
    have hbound : ∀ n, d n≤1-(n:ℝ)*(2-δ) := by
      intro n
      induction n with
      | zero => simp only [Nat.cast_zero,zero_mul,sub_zero,hd0,le_refl]
      | succ n ih =>
        rw [hstep,Nat.cast_succ]
        have := hqone n
        nlinarith
    obtain ⟨n,hn⟩ := exists_nat_gt (1/(2-δ))
    have hden : 0<2-δ := by linarith
    have hn' : 1<(n:ℝ)*(2-δ) := (div_lt_iff₀ hden).mp hn
    have := hbound n
    have := hdpos n
    linarith
  obtain ⟨n,hn⟩ := hnegative
  have hlinear : ∀ k, q (n+k)≤q n+(k:ℝ)*d n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := hanti (Nat.le_add_right n k)
      have he : q (n+(k+1))=q (n+k)+d (n+k) := by dsimp [d]; simp only [Nat.add_assoc]; ring
      rw [he,Nat.cast_succ]
      linarith
  obtain ⟨k,hk⟩ := exists_nat_gt (q n/(-d n))
  have hdneg : 0 < -d n := by linarith
  have hk' : q n<(k:ℝ)*(-d n) := (div_lt_iff₀ hdneg).mp hk
  have := hlinear k
  have := hnonneg (n+k)
  nlinarith

/-- The first nonpositive scalar gives a finite cutoff, and all earlier
nonzero-index scalars are positive, as required by the projection recursion. -/
theorem mesh_quantum_cutoff (δ : ℝ) (hδ0 : 0<δ) (hδ2 : δ<2)
    (q : ℕ → ℝ) (hzero : q 0=0) (hone : q 1=1)
    (hrec : ∀ n, q (n+2)=δ*q (n+1)-q n) :
    ∃ h, 3≤h ∧ q h≤0 ∧ ∀ n, 0<n → n<h → 0<q n := by
  classical
  have hex := mesh_quantum_eventually_nonpositive δ hδ2 q hzero hone hrec
  let h := Nat.find hex
  have hh : 0<h ∧ q h≤0 := Nat.find_spec hex
  have hp : ∀ n, 0<n → n<h → 0<q n := by
    intro n hn hnh
    have hnot := Nat.find_min hex hnh
    exact lt_of_not_ge (fun hqn => hnot ⟨hn,hqn⟩)
  have htwo : q 2=δ := by simpa only [zero_add,hzero,hone,mul_one,sub_zero] using hrec 0
  have hge : 3≤h := by
    by_contra hlt
    have he : h=1 ∨ h=2 := by omega
    rcases he with he|he
    · have := hh.2; rw [he,hone] at this; linarith
    · have := hh.2; rw [he,htwo] at this; linarith
  exact ⟨h,hge,hh.2,hp⟩

theorem meshQuantum_cutoff (δ : ℝ) (hδ0 : 0<δ) (hδ2 : δ<2) :
    ∃ h, 3≤h ∧ meshQuantum δ h≤0 ∧
      ∀ n, 0 < n → n < h → 0 < meshQuantum δ n :=
  mesh_quantum_cutoff δ hδ0 hδ2 (meshQuantum δ)
    (meshQuantum_zero δ) (meshQuantum_one δ) (meshQuantum_step δ)

lemma meshQuantum_ratio_step (δ : ℝ) (n : ℕ) (h : meshQuantum δ (n+2)≠0) :
    δ-(meshQuantum δ (n+2)/meshQuantum δ (n+1))⁻¹=
      meshQuantum δ (n+3)/meshQuantum δ (n+2) := by
  have hrec : meshQuantum δ (n+3)=δ*meshQuantum δ (n+2)-meshQuantum δ (n+1) :=
    meshQuantum_step δ (n+1)
  rw [inv_div,hrec]
  field_simp [h]

end HarmonicArtin.ParabolicIntersections

end OAI
