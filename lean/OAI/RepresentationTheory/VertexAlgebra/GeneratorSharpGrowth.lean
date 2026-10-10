import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.AdjointMass

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
theorem generator_sharpGrowth (D : ℕ) (S : ℕ → Finset V) {d : ℕ} {a : V}
    (hd : 0 < d) (hD : d ≤ D) (ha : a ∈ S d) :
    A.SharpGrowth (A.sharpMajorant D S) a d := by
  have hquant (N : ℕ) : A.sharpColumnQuantity a d N ≤ A.sharpMajorant D S N^(2*d) ∧
      A.sharpZeroQuantity a d N ≤ A.sharpMajorant D S N^(2*d) := by
    obtain ⟨H, K⟩ := A.root_sharpQuantity_le D S hD ha (N := N)
    have H' := pow_le_pow_left₀ (Real.rpow_nonneg (A.sharpColumnQuantity_nonneg a d N) _) H (2*d)
    have K' := pow_le_pow_left₀ (Real.rpow_nonneg (A.sharpZeroQuantity_nonneg a d N) _) K (2*d)
    rw [Real.rpow_inv_natCast_pow (A.sharpColumnQuantity_nonneg a d N) (by omega)] at H'
    rw [Real.rpow_inv_natCast_pow (A.sharpZeroQuantity_nonneg a d N) (by omega)] at K'
    exact ⟨H', K'⟩
  constructor
  · refine ⟨1, zero_le_one, ?_⟩
    intro N v hv
    have H := (div_le_iff₀ (by positivity : 0 < (N+1 : ℝ)^(2*d-1))).mp (hquant N).1
    apply (A.sum_positive_modes_sq_le a d hv).trans
    simpa only [one_mul, mul_comm (A.sharpMajorant D S N^(2*d))] using
      mul_le_mul_of_nonneg_right H (sq_nonneg ‖v‖)
  · refine ⟨1, zero_le_one, ?_⟩
    intro N v hv
    have H := (div_le_iff₀ (by positivity : 0 < (N+1 : ℝ)^(max 1 (2*d-2)))).mp (hquant N).2
    have Z := pow_le_pow_left₀ (norm_nonneg _) (A.zeroMode_norm_le a d hv) 2
    rw [mul_pow] at Z
    apply Z.trans
    simpa only [one_mul, mul_comm (A.sharpMajorant D S N^(2*d))] using
      mul_le_mul_of_nonneg_right H (sq_nonneg ‖v‖)

end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 

theorem exists_sharpMajorant (hc : A.toVertexAlgebra.C2Cofinite) :
    ∃ D : ℕ, 2 ≤ D ∧ ∃ S : ℕ → Finset V,
      (∀ d, d = 0 ∨ D < d → S d = ∅) ∧
      (∀ d, ∀ a ∈ S d, 1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧
        A.IsQuasiPrimary a ∧ U.IsHermitian d a) ∧
      (∀ d, 1 ≤ d → d ≤ D → ∀ a ∈ A.grade d, A.IsQuasiPrimary a →
        a ∈ Submodule.span ℂ (S d : Set V)) ∧
      (∀ d, D < d → A.grade d ≤ A.toVertexAlgebra.c2) ∧
      (∀ w, ∀ a ∈ A.grade w, A.SharpGrowth (A.sharpMajorant D S) a w) := by
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
  have hspanS (d : ℕ) (hd : 1 ≤ d) (hdD : d ≤ D) (a : V) (ha : a ∈ A.grade d)
      (hq : A.IsQuasiPrimary a) : a ∈ Submodule.span ℂ (S d : Set V) := by
    have he : S d = R d := by dsimp [S]; rw [ite_eq_left ⟨hd, hdD⟩]
    rw [he]
    exact hspan d a ha hq
  refine ⟨D, hD, S, ?_, hS, hspanS, hcut, ?_⟩
  · intro d hd
    dsimp [S]
    rw [ite_eq_right]
    omega
  · apply U.grade_sharpGrowth (A.one_le_sharpMajorant D S) D _ hcut
    intro d hd hdD a ha hq
    have hle : Submodule.span ℂ (S d : Set V) ≤
        A.sharpGrowthSubmodule (A.sharpMajorant D S) d := by
      apply Submodule.span_le.mpr
      intro b hb
      exact A.generator_sharpGrowth D S (by omega) hdD hb
    exact hle (hspanS d hd hdD a ha hq)

 

theorem physicalMode_cutoff_sq_of_grades {a : V} {d N : ℕ} (ha : a ∈ A.grade d)
    (m : ℤ) (K : ℝ)
    (H : ∀ h ≤ N, ∀ v ∈ A.grade h, ‖A.physicalMode a d m v‖^2 ≤ K*‖v‖^2)
    {v : V} (hv : v ∈ A.energyCutoff N) : ‖A.physicalMode a d m v‖^2 ≤ K*‖v‖^2 := by
  classical
  rw [physicalMode, U.mode_norm_sq_eq_sum_grades ha, U.norm_sq_eq_sum_grades v, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hh
  have hhN : h ≤ N := by
    by_contra hnot
    have hz := hv h (by omega)
    have hne : A.gradingEquiv v h ≠ 0 := DFinsupp.mem_support_iff.mp hh
    exact hne (Subtype.ext hz)
  exact H h hhN _ (A.gradeComponent_mem h v)

end UnitaryStructure
end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

theorem finite_zeroGrowth_uniform {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {ι : Type*}
    (s : Finset ι) (a : ι → V) (d : ι → ℕ) (p q : ℕ)
    (H : ∀ i ∈ s, A.ZeroGrowth X (a i) (d i) p q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ∈ s, ∀ N v, v ∈ A.energyCutoff N →
      ‖A.physicalMode (a i) (d i) 0 v‖^2 ≤ C*(N+1 : ℝ)^p*X N^q*‖v‖^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨C, hC, HC⟩ := H i (Finset.mem_insert_self _ _)
    obtain ⟨D, hD, HD⟩ := ih (fun j hj => H j (Finset.mem_insert_of_mem hj))
    refine ⟨C + D, add_nonneg hC hD, ?_⟩
    intro j hj N v hv
    have hXN := zero_le_one.trans (hX N)
    rcases Finset.mem_insert.mp hj with rfl | hj
    · apply (HC N v hv).trans
      gcongr
      exact le_add_of_nonneg_right hD
    · apply (HD j hj N v hv).trans
      gcongr
      exact le_add_of_nonneg_left hC

omit [InnerProductSpace ℂ V] in
 

theorem norm_of_sharp_square {X : ℝ} (hX : 0 ≤ X) {C : ℝ} (hC : 0 ≤ C)
    (N r s : ℕ) (v w : V)
    (H : ‖w‖^2 ≤ C * (N+1 : ℝ)^(2*r) * X^(2*s) * ‖v‖^2) :
    ‖w‖ ≤ (C+1) * (N+1 : ℝ)^r * X^s * ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ C * (N+1 : ℝ)^(2*r) * X^(2*s) * ‖v‖^2 := H
    _ ≤ (C+1)^2 * (N+1 : ℝ)^(2*r) * X^(2*s) * ‖v‖^2 := by
      gcongr
      nlinarith [sq_nonneg C]
    _ = _ := by simp only [mul_pow, pow_mul, mul_comm 2 r, mul_comm 2 s]

theorem reduced_commutator_coefficient_bound {d : ℕ} (hd : 1 ≤ d) (m j : ℕ)
    (hj : j < 2*d-1) :
    ‖((m+d-1).choose (j+1) : ℂ) - ((d-1).choose (j+1) : ℂ)‖ ≤
      (2 : ℝ)*(d+1 : ℝ)^(2*d)*(m+1 : ℝ)^(2*d) := by
  have hchoose (n : ℕ) (hn : n ≤ (d+1)*(m+1)) :
      (n.choose (j+1) : ℝ) ≤ (d+1 : ℝ)^(2*d)*(m+1 : ℝ)^(2*d) := by
    have H : n.choose (j+1) ≤ ((d+1)*(m+1))^(2*d) :=
      (Nat.choose_le_pow n (j+1)).trans
        ((Nat.pow_le_pow_left hn (j+1)).trans (Nat.pow_le_pow_right (by positivity) (by omega)))
    simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_pow] using
      (show (n.choose (j+1) : ℝ) ≤ (((d+1)*(m+1) : ℕ) : ℝ)^(2*d) from by exact_mod_cast H)
  have H := hchoose (m+d-1) (by nlinarith [Nat.sub_le (m+d) 1])
  have K := hchoose (d-1) (by nlinarith [Nat.sub_le d 1])
  calc
    _ ≤ ‖((m+d-1).choose (j+1) : ℂ)‖ + ‖((d-1).choose (j+1) : ℂ)‖ := norm_sub_le _ _
    _ ≤ _ := by simp only [Complex.norm_natCast]; linarith

 

theorem selfCommutator_sharp_bound {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hd : 2 ≤ d)
    (H : ∀ e ≤ 2*d-2, ∀ b ∈ A.grade e, A.SharpGrowth X b e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N m : ℕ) (v : V), v ∈ A.energyCutoff N →
      ‖A.selfCommutator a d m v‖ ≤
        C*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(2*d-3)*X N^(2*d-2)*‖v‖ := by
  have HS (j : ℕ) (hj : j ∈ Finset.range (2*d-1)) :
      A.ZeroGrowth X (mode A.fields a (j+1) a) (2*d-j-2) (2*(2*d-3)) (2*(2*d-2)) := by
    have hgrade := A.mode_mem_grade ha ha ((j+1 : ℕ) : ℤ)
      (k := 2*d-j-2) (by have := Finset.mem_range.mp hj; omega)
    have h := (H (2*d-j-2) (by omega) _ hgrade).2
    apply A.zeroGrowth_mono hX h <;> omega
  obtain ⟨C, hC, HC⟩ := A.finite_zeroGrowth_uniform hX (Finset.range (2*d-1))
    (fun j => mode A.fields a (j+1) a) (fun j => 2*d-j-2) (2*(2*d-3)) (2*(2*d-2)) HS
  refine ⟨(2*d-1 : ℕ)* (2*(d+1 : ℝ)^(2*d))*(C+1), by positivity, ?_⟩
  intro N m v hv
  have hXN := zero_le_one.trans (hX N)
  rw [A.selfCommutator_eq_sum_reduced ha (by omega)]
  calc
    _ ≤ ∑ j ∈ Finset.range (2*d-1),
      ‖((m+d-1).choose (j+1) : ℂ) - ((d-1).choose (j+1) : ℂ)‖ *
        ‖A.physicalMode (mode A.fields a (j+1) a) (2*d-j-2) 0 v‖ := by
      simpa only [norm_smul] using norm_sum_le (Finset.range (2*d-1))
        (fun j => (((m+d-1).choose (j+1) : ℂ) - ((d-1).choose (j+1) : ℂ)) •
          A.physicalMode (mode A.fields a (j+1) a) (2*d-j-2) 0 v)
    _ ≤ ∑ _j ∈ Finset.range (2*d-1),
      (2*(d+1 : ℝ)^(2*d)*(m+1 : ℝ)^(2*d)) *
        ((C+1)*(N+1 : ℝ)^(2*d-3)*X N^(2*d-2)*‖v‖) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul (reduced_commutator_coefficient_bound (by omega) m j (Finset.mem_range.mp hj))
        (norm_of_sharp_square hXN hC N (2*d-3) (2*d-2) v _ (HC j hj N v hv))
        (norm_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 

theorem nonzeroModes_sharp_bound {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a)
    (hh : U.IsHermitian d a) (hd : 2 ≤ d)
    (H : ∀ e ≤ 2*d-2, ∀ b ∈ A.grade e, A.SharpGrowth X b e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N m : ℕ), 0 < m → ∀ v ∈ A.energyCutoff N,
      ‖A.physicalMode a d m v‖ ≤ C*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*X N^(d-1)*‖v‖ ∧
      ‖A.physicalMode a d (-(m : ℤ)) v‖ ≤ C*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*X N^(d-1)*‖v‖ := by
  obtain ⟨C, hC, HC⟩ := A.selfCommutator_sharp_bound hX ha hd H
  refine ⟨C+1, by positivity, ?_⟩
  intro N m hm v hv
  have hXN := zero_le_one.trans (hX N)
  let R := C*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(2*d-3)*X N^(2*d-2)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have HR (h : ℕ) (hhN : h ≤ N) (w : V) (hw : w ∈ A.grade h) :
      ‖A.selfCommutator a d m w‖ ≤ R*‖w‖ := HC N m w (A.grade_le_energyCutoff hhN hw)
  have HE : (N+1 : ℝ)*R = C*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(2*(d-1))*X N^(2*(d-1)) := by
    have hp : 2*(d-1) = (2*d-3)+1 := by omega
    have hq : 2*(d-1) = 2*d-2 := by omega
    dsimp [R]
    conv_rhs => arg 1; arg 2; rw [hp, pow_succ]
    rw [hq]
    ring
  have step (n : ℤ)
      (HN : ∀ h ≤ N, ∀ w ∈ A.grade h, ‖A.physicalMode a d n w‖^2 ≤ (h+1 : ℝ)*R*‖w‖^2) :
      ‖A.physicalMode a d n v‖ ≤ (C+1)*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*X N^(d-1)*‖v‖ := by
    have Hsq : ‖A.physicalMode a d n v‖^2 ≤ ((N+1 : ℝ)*R)*‖v‖^2 := by
      apply U.physicalMode_cutoff_sq_of_grades ha n _ _ hv
      intro h hhN w hw
      apply (HN h hhN w hw).trans
      have hhR : (h : ℝ) ≤ N := by exact_mod_cast hhN
      gcongr
    rw [HE] at Hsq
    have Hnorm := norm_of_sharp_square hXN (show 0 ≤ C*(m+1 : ℝ)^(2*d) by positivity)
      N (d-1) (d-1) v _ Hsq
    apply Hnorm.trans
    have hM : 1 ≤ (m+1 : ℝ)^(2*d) := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) m])
    have hcoef : C*(m+1 : ℝ)^(2*d)+1 ≤ (C+1)*(m+1 : ℝ)^(2*d) := by nlinarith
    gcongr
  constructor
  · apply step m
    intro h hhN w hw
    have Hlower := U.lowering_norm_sq_of_commutator ha hq hh hm hR HR h hhN w hw
    apply Hlower.trans
    gcongr
    linarith
  · apply step (-(m : ℤ))
    intro h hhN w hw
    exact U.raising_norm_sq_of_commutator ha hq hh hm hR HR hhN hw

end UnitaryStructure
end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 

theorem zeroMode_sharpGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) (hmono : Monotone X)
    {a : V} {d : ℕ} (hp : A.PolynomialEnergyBound a) (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (hd : 2 ≤ d)
    (H : ∀ e ≤ 2*d-2, ∀ b ∈ A.grade e, A.SharpGrowth X b e) :
    A.ZeroGrowth (fun N => X (2*N)) a d (2*(d-1)) (2*(d-1)) := by
  obtain ⟨C, hC, HC⟩ := U.nonzeroModes_sharp_bound hX ha hq hh hd H
  let F : ℕ → ℝ := fun N => (C+1)*2^(2*d)*(N+1 : ℝ)^(d-1)*X N^(d-1)
  have hF (N : ℕ) : 1 ≤ F N := by
    dsimp [F]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by norm_num)))
      (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]))) (one_le_pow₀ (hX N))
  have HF (N : ℕ) (v : V) (hv : v ∈ A.energyCutoff N) :
      ‖A.physicalMode a d 1 v‖ ≤ F N * ‖v‖ := by
    have H' := (HC N 1 (by decide) v hv).1
    apply H'.trans
    dsimp [F]
    have hXN := zero_le_one.trans (hX N)
    norm_num only [Nat.cast_one, show (1 : ℝ)+1 = 2 by norm_num]
    gcongr
    linarith
  obtain ⟨B, hB, HB⟩ := U.zeroMode_transfer hp ha hq hd
  let K := B*(C+1)*2^(2*d)*2^(d-1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have HR (N h : ℕ) (hhN : h ≤ N) :
      B * F (2*h) ≤ K * (N+1 : ℝ)^(d-1)*X (2*N)^(d-1) := by
    have hx := zero_le_one.trans (hX (2*h))
    have hx' := zero_le_one.trans (hX (2*N))
    have hnR : (2*h+1 : ℝ) ≤ 2*(N+1 : ℝ) := by
      have hn : (h : ℝ) ≤ N := by exact_mod_cast hhN
      linarith
    have hXm : X (2*h) ≤ X (2*N) := hmono (by omega)
    calc
      _ ≤ B * ((C+1)*2^(2*d)*(2*(N+1 : ℝ))^(d-1)*X (2*N)^(d-1)) := by
        dsimp [F]
        push_cast
        gcongr
      _ = _ := by dsimp [K]; rw [mul_pow]; ring
  refine ⟨K^2, sq_nonneg _, ?_⟩
  intro N v hv
  have hXN := zero_le_one.trans (hX (2*N))
  have HK : ‖A.physicalMode a d 0 v‖^2 ≤
      (K*(N+1 : ℝ)^(d-1)*X (2*N)^(d-1))^2 * ‖v‖^2 := by
    apply U.physicalMode_cutoff_sq_of_grades ha 0 _ _ hv
    intro h hhN w hw
    have Hnorm : ‖A.physicalMode a d 0 w‖ ≤
        (K*(N+1 : ℝ)^(d-1)*X (2*N)^(d-1))*‖w‖ :=
      (HB F hF HF h w hw).trans (mul_le_mul_of_nonneg_right (HR N h hhN) (norm_nonneg _))
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) Hnorm 2
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm (d-1) 2] using HK

end UnitaryStructure
end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

def zeroGrowthSubmodule (X : ℕ → ℝ) (d p q : ℕ) : Submodule ℂ V where
  carrier := {a | A.ZeroGrowth X a d p q}
  zero_mem' := A.zeroGrowth_zero X d p q
  add_mem' := A.zeroGrowth_add
  smul_mem' z _ H := A.zeroGrowth_smul H z

theorem zeroGrowth_changeControl {X Y : ℕ → ℝ} (hX : ∀ N, 0 ≤ X N)
    (hXY : ∀ N, X N ≤ Y N) {a : V} {d p q : ℕ} (H : A.ZeroGrowth X a d p q) :
    A.ZeroGrowth Y a d p q := by
  obtain ⟨C, hC, HC⟩ := H
  refine ⟨C, hC, ?_⟩
  intro N v hv
  apply (HC N v hv).trans
  gcongr
  · exact hX N
  · exact hXY N

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 

theorem grade_improved_zeroGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N)
    (hmono : Monotone X) (hp : A.PolynomialEnergyBounds)
    (H : ∀ e, ∀ b ∈ A.grade e, A.SharpGrowth X b e)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hd : 2 ≤ d) :
    A.ZeroGrowth (fun N => X (2*N)) a d (2*(d-1)) (2*(d-1)) := by
  classical
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  obtain ⟨q, hq, hqq, b, hb, hab⟩ := U.quasiPrimary_decomposition ha
  obtain ⟨S, hS, hspan⟩ := U.exists_hermitian_quasiPrimary_spanning (e+1)
  have Hq : A.ZeroGrowth (fun N => X (2*N)) q (e+1) (2*e) (2*e) := by
    have hle : Submodule.span ℂ (S : Set V) ≤
        A.zeroGrowthSubmodule (fun N => X (2*N)) (e+1) (2*e) (2*e) := by
      apply Submodule.span_le.mpr
      intro c hc
      obtain ⟨hcg, hcq, hch⟩ := hS c hc
      change A.ZeroGrowth (fun N => X (2*N)) c (e+1) (2*e) (2*e)
      simpa only [Nat.add_sub_cancel] using
        U.zeroMode_sharpGrowth hX hmono (hp c) hcg hcq hch hd
          (fun f _ c hcf => H f c hcf)
    exact hle (hspan q hq hqq)
  have Hb := A.translation_zeroGrowth (H e b hb).2
  have Hb' := A.zeroGrowth_changeControl (fun N => zero_le_one.trans (hX N))
    (fun N => hmono (by omega : N ≤ 2*N)) Hb
  have Hb'' := A.zeroGrowth_mono (fun N => hX (2*N)) Hb' (p' := 2*e) (q' := 2*e)
    (by omega) le_rfl
  rw [hab, A.virasoro_neg_one_eq_translation]
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using A.zeroGrowth_add Hq Hb''

omit U in
 

theorem positiveColumnNorm_sq_le {a : V} {d N : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (H : ∀ v ∈ A.energyCutoff N,
      (∑ m ∈ Finset.range (N+1), ‖A.physicalMode a d m v‖^2) ≤ K*‖v‖^2) :
    A.positiveColumnNorm a d N^2 ≤ K := by
  have HB : A.positiveColumnNorm a d N ≤ Real.sqrt K := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hK, A.positiveColumn_norm_sq]
    exact H v v.property
  exact (pow_le_pow_left₀ (A.positiveColumnNorm_nonneg a d N) HB 2).trans_eq (Real.sq_sqrt hK)

 

theorem generator_column_contraction {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N)
    (hmono : Monotone X) (hp : A.PolynomialEnergyBounds)
    (H : ∀ e, ∀ b ∈ A.grade e, A.SharpGrowth X b e)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hd : 1 ≤ d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      A.positiveColumnNorm a d N^2 ≤ C*(N+1 : ℝ)^(2*d-1)*X (2*N)^(2*d-1) := by
  have hs : mode A.fields a (-1) a ∈ A.grade (2*d) := A.normalProduct_mem_grade ha
  obtain ⟨C, hC, HC⟩ := U.grade_improved_zeroGrowth hX hmono hp H hs (by omega)
  refine ⟨C+1, by linarith, ?_⟩
  intro N
  have hXN := zero_le_one.trans (hX (2*N))
  apply positiveColumnNorm_sq_le (by positivity)
  intro v hv
  have Hs := norm_of_sharp_square hXN hC N (2*d-1) (2*d-1) v _ (HC N v hv)
  have Hpos := U.positive_column hd ha hq hh v
  have Hfin : (∑ m ∈ Finset.range (N+1), ‖A.physicalMode a d m v‖^2) ≤
      ∑ᶠ m : ℕ, ‖A.physicalMode a d m v‖^2 :=
    (A.finsum_positive_modes_sq_eq ha hv).symm.le
  have HE : A.physicalMode (mode A.fields a (-1) a) (2*d) 0 v =
      mode A.fields (mode A.fields a (-1) a) (2*(d : ℤ)-1) v := by
    simp only [physicalMode, zero_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [HE] at Hs
  calc
    _ ≤ _ := Hfin.trans Hpos
    _ ≤ ‖mode A.fields (mode A.fields a (-1) a) (2*(d : ℤ)-1) v‖*‖v‖ := re_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ((C+1)*(N+1 : ℝ)^(2*d-1)*X (2*N)^(2*d-1)*‖v‖)*‖v‖ :=
      mul_le_mul_of_nonneg_right Hs (norm_nonneg _)
    _ = _ := by ring

end UnitaryStructure
end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

theorem zeroModeCutoffNorm_le_column (a : V) (d N : ℕ) :
    A.zeroModeCutoffNorm a d N ≤ A.positiveColumnNorm a d N := by
  have hR := A.positiveColumnNorm_nonneg a d N
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro v
  change ‖A.physicalMode a d 0 v‖ ≤ A.positiveColumnNorm a d N * ‖v‖
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow]
  apply le_trans _ (A.sum_positive_modes_sq_le a d v.property)
  exact Finset.single_le_sum (s := Finset.range (N+1)) (a := 0)
    (f := fun m : ℕ => ‖A.physicalMode a d m v‖^2) (fun m _ => sq_nonneg _)
    (Finset.mem_range.mpr (show 0 < N+1 by omega))

theorem zeroModeCutoffNorm_sq_le {a : V} {d N : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (H : ∀ v ∈ A.energyCutoff N, ‖A.physicalMode a d 0 v‖^2 ≤ K*‖v‖^2) :
    A.zeroModeCutoffNorm a d N^2 ≤ K := by
  have HB : A.zeroModeCutoffNorm a d N ≤ Real.sqrt K := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hK]
    exact H v v.property
  exact (pow_le_pow_left₀ (norm_nonneg (A.zeroModeOnCutoff a d N)) HB 2).trans_eq (Real.sq_sqrt hK)

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

theorem generator_quantities_contraction {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N)
    (hmono : Monotone X) (hp : A.PolynomialEnergyBounds)
    (H : ∀ e, ∀ b ∈ A.grade e, A.SharpGrowth X b e)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hd : 1 ≤ d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      A.sharpColumnQuantity a d N ≤ C*X (2*N)^(2*d-1) ∧
      A.sharpZeroQuantity a d N ≤ C*X (2*N)^(2*d-1) := by
  obtain ⟨C, hC, HC⟩ := U.generator_column_contraction hX hmono hp H ha hd hq hh
  have HC' (N : ℕ) : A.sharpColumnQuantity a d N ≤ C*X (2*N)^(2*d-1) := by
    apply (div_le_iff₀ (by positivity : 0 < (N+1 : ℝ)^(2*d-1))).mpr
    simpa only [mul_assoc, mul_comm ((N+1 : ℝ)^(2*d-1)), mul_left_comm] using HC N
  by_cases hd1 : d = 1
  · subst d
    refine ⟨C, hC, fun N => ⟨HC' N, ?_⟩⟩
    apply le_trans _ (HC' N)
    unfold sharpZeroQuantity sharpColumnQuantity
    norm_num only
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg (A.zeroModeOnCutoff a 1 N))
      (A.zeroModeCutoffNorm_le_column a 1 N) 2
  · obtain ⟨B, hB, HB⟩ := U.zeroMode_sharpGrowth hX hmono (hp a) ha hq hh
      (by omega) (fun e _ b hb => H e b hb)
    have HB' (N : ℕ) : A.sharpZeroQuantity a d N ≤ B*X (2*N)^(2*d-1) := by
      have hXN := zero_le_one.trans (hX (2*N))
      have HB'' := A.zeroModeCutoffNorm_sq_le (a := a) (d := d) (N := N)
        (K := B*(N+1 : ℝ)^(2*(d-1))*X (2*N)^(2*(d-1))) (by positivity) (HB N)
      have he : max 1 (2*d-2) = 2*(d-1) := by omega
      unfold sharpZeroQuantity
      rw [he]
      apply (div_le_iff₀ (by positivity : 0 < (N+1 : ℝ)^(2*(d-1)))).mpr
      apply HB''.trans
      calc
        _ ≤ B*(N+1 : ℝ)^(2*(d-1))*X (2*N)^(2*d-1) := by
          gcongr
          · exact hX (2*N)
          · omega
        _ = _ := by ring
    refine ⟨C+B, add_nonneg hC hB, fun N => ⟨?_, ?_⟩⟩
    · apply (HC' N).trans
      gcongr
      · exact pow_nonneg (zero_le_one.trans (hX (2*N))) _
      · exact le_add_of_nonneg_right hB
    · apply (HB' N).trans
      gcongr
      · exact pow_nonneg (zero_le_one.trans (hX (2*N))) _
      · exact le_add_of_nonneg_left hC

end UnitaryStructure
end CFTTypeVOA
end StronglyRationalVOA

end

end OAI
