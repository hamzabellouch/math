import OAI.RepresentationTheory.VertexAlgebra.ModuleSharpMajorant
import OAI.RepresentationTheory.VertexAlgebra.ModuleMobiusTransfer

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)
theorem finite_zeroGrowth_uniform {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N) {ι : Type*}
    (s : Finset ι) (a : ι → V) (d : ι → ℕ) (p q : ℕ)
    (H : ∀ i ∈ s, M.ZeroGrowth X (a i) (d i) p q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ∈ s, ∀ τ N v, v ∈ M.energyCutoff τ N →
      ‖M.physicalMode (a i) (d i) 0 v‖^2 ≤ C*(N+1 : ℝ)^p*X τ N^q*‖v‖^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨C, hC, HC⟩ := H i (Finset.mem_insert_self _ _)
    obtain ⟨D, hD, HD⟩ := ih (fun j hj => H j (Finset.mem_insert_of_mem hj))
    refine ⟨C + D, add_nonneg hC hD, ?_⟩
    intro j hj τ N v hv
    have hXN := zero_le_one.trans (hX τ N)
    rcases Finset.mem_insert.mp hj with rfl | hj
    · apply (HC τ N v hv).trans
      gcongr
      exact le_add_of_nonneg_right hD
    · apply (HD j hj τ N v hv).trans
      gcongr
      exact le_add_of_nonneg_left hC

theorem selfCommutator_sharp_bound {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hd : 2 ≤ d)
    (H : ∀ e ≤ 2*d-2, ∀ b ∈ A.grade e, M.SharpGrowth X b e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : EnergyBand) (N m : ℕ) (v : W), v ∈ M.energyCutoff τ N →
      ‖M.selfCommutator a d m v‖ ≤
        C*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(2*d-3)*X τ N^(2*d-2)*‖v‖ := by
  have HS (j : ℕ) (hj : j ∈ Finset.range (2*d-1)) :
      M.ZeroGrowth X (mode A.fields a (j+1) a) (2*d-j-2) (2*(2*d-3)) (2*(2*d-2)) := by
    have hgrade := A.mode_mem_grade ha ha ((j+1 : ℕ) : ℤ)
      (k := 2*d-j-2) (by have := Finset.mem_range.mp hj; omega)
    have h := (H (2*d-j-2) (by omega) _ hgrade).2
    apply M.zeroGrowth_mono hX h <;> omega
  obtain ⟨C, hC, HC⟩ := M.finite_zeroGrowth_uniform hX (Finset.range (2*d-1))
    (fun j => mode A.fields a (j+1) a) (fun j => 2*d-j-2) (2*(2*d-3)) (2*(2*d-2)) HS
  refine ⟨(2*d-1 : ℕ)* (2*(d+1 : ℝ)^(2*d))*(C+1), by positivity, ?_⟩
  intro τ N m v hv
  have hXN := zero_le_one.trans (hX τ N)
  rw [M.selfCommutator_eq_sum_reduced ha (by omega)]
  calc
    _ ≤ ∑ j ∈ Finset.range (2*d-1),
      ‖((m+d-1).choose (j+1) : ℂ) - ((d-1).choose (j+1) : ℂ)‖ *
        ‖M.physicalMode (mode A.fields a (j+1) a) (2*d-j-2) 0 v‖ := by
      simpa only [norm_smul] using norm_sum_le (Finset.range (2*d-1))
        (fun j => (((m+d-1).choose (j+1) : ℂ) - ((d-1).choose (j+1) : ℂ)) •
          M.physicalMode (mode A.fields a (j+1) a) (2*d-j-2) 0 v)
    _ ≤ ∑ _j ∈ Finset.range (2*d-1),
      (2*(d+1 : ℝ)^(2*d)*(m+1 : ℝ)^(2*d)) *
        ((C+1)*(N+1 : ℝ)^(2*d-3)*X τ N^(2*d-2)*‖v‖) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul (reduced_commutator_coefficient_bound (by omega) m j (Finset.mem_range.mp hj))
        (norm_of_sharp_square hXN hC N (2*d-3) (2*d-2) v _ (HC j hj τ N v hv))
        (norm_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q
theorem physicalMode_cutoff_sq_of_grades (τ : EnergyBand) {a : V} {d N : ℕ}
    (ha : a ∈ A.grade d) (m : ℤ) (K : ℝ)
    (H : ∀ h ≤ N, ∀ v ∈ M.bandGrade τ h, ‖M.physicalMode a d m v‖^2 ≤ K*‖v‖^2)
    {v : W} (hv : v ∈ M.energyCutoff τ N) : ‖M.physicalMode a d m v‖^2 ≤ K*‖v‖^2 := by
  rw [physicalMode, Q.mode_norm_sq_eq_sum_cutoff τ ha _ hv,
    Q.norm_sq_eq_sum_cutoff τ hv, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hh
  exact H h (by have := Finset.mem_range.mp hh; omega) _ (M.bandComponent_mem τ h v)
theorem nonzeroModes_sharp_bound {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a)
    (hh : U.IsHermitian d a) (hd : 2 ≤ d)
    (H : ∀ e ≤ 2*d-2, ∀ b ∈ A.grade e, M.SharpGrowth X b e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : EnergyBand) (N m : ℕ), 0 < m → ∀ v ∈ M.energyCutoff τ N,
      ‖M.physicalMode a d m v‖ ≤ C*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*X τ N^(d-1)*‖v‖ ∧
      ‖M.physicalMode a d (-(m : ℤ)) v‖ ≤ C*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*X τ N^(d-1)*‖v‖ := by
  obtain ⟨C, hC, HC⟩ := M.selfCommutator_sharp_bound hX ha hd H
  refine ⟨C+1, by positivity, ?_⟩
  intro τ N m hm v hv
  have hXN := zero_le_one.trans (hX τ N)
  let R := C*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(2*d-3)*X τ N^(2*d-2)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have HR (h : ℕ) (hhN : h ≤ N) (w : W) (hw : w ∈ M.bandGrade τ h) :
      ‖M.selfCommutator a d m w‖ ≤ R*‖w‖ := HC τ N m w (M.grade_le_energyCutoff τ hhN hw)
  have HE : (N+1 : ℝ)*R = C*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(2*(d-1))*X τ N^(2*(d-1)) := by
    have hp : 2*(d-1) = (2*d-3)+1 := by omega
    have hq : 2*(d-1) = 2*d-2 := by omega
    dsimp [R]
    conv_rhs => arg 1; arg 2; rw [hp, pow_succ]
    rw [hq]
    ring
  have step (n : ℤ)
      (HN : ∀ h ≤ N, ∀ w ∈ M.bandGrade τ h, ‖M.physicalMode a d n w‖^2 ≤ (h+1 : ℝ)*R*‖w‖^2) :
      ‖M.physicalMode a d n v‖ ≤ (C+1)*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*X τ N^(d-1)*‖v‖ := by
    have Hsq : ‖M.physicalMode a d n v‖^2 ≤ ((N+1 : ℝ)*R)*‖v‖^2 := by
      apply Q.physicalMode_cutoff_sq_of_grades τ ha n _ _ hv
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
    have Hlower := Q.lowering_norm_sq_of_commutator τ ha hq hh hm hR HR h hhN w hw
    apply Hlower.trans
    gcongr
    linarith
  · apply step (-(m : ℤ))
    intro h hhN w hw
    exact Q.raising_norm_sq_of_commutator τ ha hq hh hm hR HR hhN hw

end UnitaryStructure

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
