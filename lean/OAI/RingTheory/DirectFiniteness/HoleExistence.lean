import OAI.RingTheory.DirectFiniteness.HoleNumerics

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry

lemma trimmed_card_interval {A : Type u_1} [DecidableEq A] (O : Finset A) {N D : ℕ}
    (hD : 0 < D) (hDN : D^2 ≤ N) (hO : 3*(N:ℝ)/(D:ℝ)^2 ≤ O.card) :
    ∃ P ⊆ O, 2*N ≤ P.card*D^2 ∧ P.card*D^2 ≤ 3*N := by
  let m := 2*N/D^2+1
  have hds : 0 < D^2 := pow_pos hD _
  have hm : 2*N ≤ m*D^2 := by
    have hmod := Nat.mod_lt (2*N) hds
    have he := Nat.mod_add_div (2*N) (D^2)
    dsimp [m]
    nlinarith
  have hm' : m*D^2 ≤ 3*N := by
    have hh := Nat.div_mul_le_self (2*N) (D^2)
    dsimp [m]
    nlinarith
  have hmO : m ≤ O.card := by
    have hcast : (3*N:ℕ) ≤ O.card*D^2 := by
      have hdreal : 0 < (D:ℝ)^2 := by positivity
      have hh := (div_le_iff₀ hdreal).mp hO
      exact_mod_cast hh
    nlinarith
  obtain ⟨P,hP,hcard⟩ := Finset.exists_subset_card_eq hmO
  exact ⟨P,hP,by simpa [hcard] using hm,by simpa [hcard] using hm'⟩

namespace DirectionFrame
variable {Q : Type u_2} {A : Type u_3} {R : Type u_4} {E : Type u_5} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype R] [Fintype E]

lemma exists_sized_goodHoles (F : DirectionFrame Q A R E) (S : Finset A)
    {q D : ℕ} (hqcard : Fintype.card Q=q) (hE : Fintype.card E=q^119)
    (hq : 12 ≤ q) (hD : q^100 ≤ D) (hR : Fintype.card R*q ≤ D)
    (hdensity : Fintype.card A ≤ q^72*S.card) (hDN : D^2 ≤ Fintype.card A) :
    ∃ O : Finset A, HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O ∧
      2*Fintype.card A ≤ O.card*D^2 ∧ O.card*D^2 ≤ 3*Fintype.card A := by
  have hqpos : 0 < q := by omega
  have hdpos : 0 < D := (pow_pos hqpos _).trans_le hD
  have hr : Fintype.card R ≤ D := by
    exact (Nat.le_mul_of_pos_right _ hqpos).trans hR
  have hw (r : R) : Fintype.card (F.W r) ≤ q^2 := by rw [F.card_W,hqcard]
  have hu (j : R × Q) (r : R) : Fintype.card ↥(F.U j ⊔ F.W r) ≤ q^122 := by
    calc
      _ ≤ Fintype.card (F.U j)*Fintype.card (F.W r) := card_sup_le_mul _ _
      _ = (q*q^119)*q^2 := by rw [F.card_U,F.card_W,hqcard,hE]
      _ = q^122 := by ring
  have hC : (Fintype.card (HoleEvents.PairIndex S F.W) : ℝ) ≤ D*(S.card:ℝ)*(q:ℝ)^2 := by
    exact_mod_cast (HoleEvents.pairIndex_card S F.W (q^2) hw).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hr))
  have hB : (Fintype.card (HoleEvents.RectangleIndex S F.W (fun r t => F.exc r t)) : ℝ)
      ≤ (D:ℝ)^2*Fintype.card A*(q:ℝ)^10 := by
    have hh := (HoleEvents.rectangleIndex_card S F.W (fun r t => F.exc r t) (q^2) hw).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hr 2))))
    have he : D^2*Fintype.card A*q^2*(q^2)^4 = D^2*Fintype.card A*q^10 := by ring
    rw [hqcard,he] at hh
    exact_mod_cast hh
  have hH : (Fintype.card (HoleEvents.OccupancyIndex S F.W F.U 101) : ℝ)
      ≤ (D:ℝ)^2*Fintype.card A*((q:ℝ)^122)^101 := by
    have hh := HoleEvents.occupancyIndex_card S F.W F.U 101 (q^122) hu
    rw [hqcard] at hh
    have hh' : Fintype.card (HoleEvents.OccupancyIndex S F.W F.U 101)
        ≤ D^2*Fintype.card A*(q^122)^101 := hh.trans (by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by simpa [pow_two] using Nat.mul_le_mul hR hr)))
    exact_mod_cast hh'
  let p : Set.Icc (0:ℝ) 1 := ⟨(q:ℝ)^73/(D:ℝ)^2,hole_probability_mem (by exact_mod_cast hq) (by exact_mod_cast hD)⟩
  obtain ⟨O,hO,hsize⟩ := HoleEvents.exists_goodHoles S F.W F.U (fun r t => F.exc r t) p
  have hnumeric := hole_alteration_numeric (by exact_mod_cast hq : (12:ℝ) ≤ q)
    (by exact_mod_cast hD : (q:ℝ)^100 ≤ D)
    (by positivity : (0:ℝ) ≤ Fintype.card A) (by positivity : (0:ℝ) ≤ S.card)
    (by exact_mod_cast hdensity : (Fintype.card A:ℝ) ≤ (q:ℝ)^72*S.card) hC hB hH
  obtain ⟨P,hP,hlo,hhi⟩ := trimmed_card_interval O hdpos hDN (hnumeric.trans hsize)
  exact ⟨P,hO.mono S F.W F.U hP,hlo,hhi⟩

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
