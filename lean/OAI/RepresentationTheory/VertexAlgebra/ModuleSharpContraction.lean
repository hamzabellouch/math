import OAI.RepresentationTheory.VertexAlgebra.ModuleZeroSharp

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)
variable (τ : EnergyBand)
theorem zeroModeCutoffNorm_le_column (a : V) (d N : ℕ) :
    M.zeroModeCutoffNorm τ a d N ≤ M.positiveColumnNorm τ a d N := by
  have hR := M.positiveColumnNorm_nonneg τ a d N
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro v
  change ‖M.physicalMode a d 0 v‖ ≤ M.positiveColumnNorm τ a d N * ‖v‖
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow]
  apply le_trans _ (M.sum_positive_modes_sq_le τ a d v.property)
  exact Finset.single_le_sum (s := Finset.range (N+1)) (a := 0)
    (f := fun m : ℕ => ‖M.physicalMode a d m v‖^2) (fun m _ => sq_nonneg _)
    (Finset.mem_range.mpr (show 0 < N+1 by omega))

theorem zeroModeCutoffNorm_sq_le {a : V} {d N : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (H : ∀ v ∈ M.energyCutoff τ N, ‖M.physicalMode a d 0 v‖^2 ≤ K*‖v‖^2) :
    M.zeroModeCutoffNorm τ a d N^2 ≤ K := by
  have HB : M.zeroModeCutoffNorm τ a d N ≤ Real.sqrt K := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hK]
    exact H v v.property
  exact (pow_le_pow_left₀ (norm_nonneg (M.zeroModeOnCutoff τ a d N)) HB 2).trans_eq (Real.sq_sqrt hK)

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q
theorem generator_quantities_contraction {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N)
    (hmono : ∀ τ, Monotone (X τ)) (hp : M.PolynomialEnergyBounds)
    (H : ∀ e, ∀ b ∈ A.grade e, M.SharpGrowth X b e)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hd : 1 ≤ d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ N,
      M.sharpColumnQuantity τ a d N ≤ C*X τ (2*N)^(2*d-1) ∧
      M.sharpZeroQuantity τ a d N ≤ C*X τ (2*N)^(2*d-1) := by
  obtain ⟨C, hC, HC⟩ := Q.generator_column_contraction hX hmono hp H ha hd hq hh
  have HC' (τ : EnergyBand) (N : ℕ) : M.sharpColumnQuantity τ a d N ≤ C*X τ (2*N)^(2*d-1) := by
    apply (div_le_iff₀ (by positivity : 0 < (N+1 : ℝ)^(2*d-1))).mpr
    simpa only [mul_assoc, mul_comm ((N+1 : ℝ)^(2*d-1)), mul_left_comm] using HC τ N
  by_cases hd1 : d = 1
  · subst d
    refine ⟨C, hC, fun τ N => ⟨HC' τ N, ?_⟩⟩
    apply le_trans _ (HC' τ N)
    unfold sharpZeroQuantity sharpColumnQuantity
    norm_num only
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg (M.zeroModeOnCutoff τ a 1 N))
      (M.zeroModeCutoffNorm_le_column τ a 1 N) 2
  · obtain ⟨B, hB, HB⟩ := Q.zeroMode_sharpGrowth hX hmono (hp a) ha hq hh
      (by omega) (fun e _ b hb => H e b hb)
    have HB' (τ : EnergyBand) (N : ℕ) : M.sharpZeroQuantity τ a d N ≤ B*X τ (2*N)^(2*d-1) := by
      have hXN := zero_le_one.trans (hX τ (2*N))
      have HB'' := M.zeroModeCutoffNorm_sq_le τ (a := a) (d := d) (N := N)
        (K := B*(N+1 : ℝ)^(2*(d-1))*X τ (2*N)^(2*(d-1))) (by positivity) (HB τ N)
      have he : max 1 (2*d-2) = 2*(d-1) := by omega
      unfold sharpZeroQuantity
      rw [he]
      apply (div_le_iff₀ (by positivity : 0 < (N+1 : ℝ)^(2*(d-1)))).mpr
      apply HB''.trans
      calc
        _ ≤ B*(N+1 : ℝ)^(2*(d-1))*X τ (2*N)^(2*d-1) := by
          gcongr
          · exact hX τ (2*N)
          · omega
        _ = _ := by ring
    refine ⟨C+B, add_nonneg hC hB, fun τ N => ⟨?_, ?_⟩⟩
    · apply (HC' τ N).trans
      gcongr
      · exact pow_nonneg (zero_le_one.trans (hX τ (2*N))) _
      · exact le_add_of_nonneg_right hB
    · apply (HB' τ N).trans
      gcongr
      · exact pow_nonneg (zero_le_one.trans (hX τ (2*N))) _
      · exact le_add_of_nonneg_left hC

end UnitaryStructure
def CutoffPowerControl (Y : EnergyBand → ℕ → ℝ) (P : ℕ) (f : EnergyBand → ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ τ N, f τ N^P ≤ C*Y τ N

theorem cutoffPowerControl_add {Y f g : EnergyBand → ℕ → ℝ} {P : ℕ}
    (hf : ∀ τ N, 0 ≤ f τ N) (hg : ∀ τ N, 0 ≤ g τ N)
    (Hf : CutoffPowerControl Y P f) (Hg : CutoffPowerControl Y P g) :
    CutoffPowerControl Y P (fun τ N => f τ N+g τ N) := by
  obtain ⟨C, hC, HC⟩ := Hf
  obtain ⟨D, hD, HD⟩ := Hg
  refine ⟨2^(P-1)*(C+D), by positivity, ?_⟩
  intro τ N
  calc
    _ ≤ 2^(P-1)*(f τ N^P+g τ N^P) := add_pow_le (hf τ N) (hg τ N) P
    _ ≤ 2^(P-1)*(C*Y τ N+D*Y τ N) := by gcongr; exacts [HC τ N, HD τ N]
    _ = _ := by ring

theorem cutoffPowerControl_sum {Y : EnergyBand → ℕ → ℝ} {P : ℕ}
    (hP : 1 ≤ P) {ι : Type*} (s : Finset ι) (f : ι → EnergyBand → ℕ → ℝ)
    (hf : ∀ i ∈ s, ∀ τ N, 0 ≤ f i τ N)
    (H : ∀ i ∈ s, CutoffPowerControl Y P (f i)) :
    CutoffPowerControl Y P (fun τ N => ∑ i ∈ s, f i τ N) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, by simp [show P ≠ 0 by omega]⟩
  | @insert i s hi ih =>
    have hsum := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => H j (Finset.mem_insert_of_mem hj))
    have h := cutoffPowerControl_add (hf i (Finset.mem_insert_self _ _))
      (fun τ N => Finset.sum_nonneg (fun j hj => hf j (Finset.mem_insert_of_mem hj) τ N))
      (H i (Finset.mem_insert_self _ _)) hsum
    simpa only [Finset.sum_insert hi] using h

theorem cutoffPowerControl_one {Y : EnergyBand → ℕ → ℝ} (hY : ∀ τ N, 1 ≤ Y τ N) (P : ℕ) :
    CutoffPowerControl Y P (fun _ _ => 1) :=
  ⟨1, zero_le_one, by simpa using hY⟩

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q
theorem sharpMajorant_power_contraction (D : ℕ) (hD : 2 ≤ D) (S : ℕ → Finset V)
    (hS : ∀ d, ∀ a ∈ S d, 1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧
      A.IsQuasiPrimary a ∧ U.IsHermitian d a)
    (hp : M.PolynomialEnergyBounds)
    (H : ∀ e, ∀ b ∈ A.grade e, M.SharpGrowth (fun τ => M.sharpMajorant τ D S) b e) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ τ N,
      M.sharpMajorant τ D S N^(2*D) ≤ C*M.sharpMajorant τ D S (2*N)^(2*D-1) := by
  classical
  let X := fun τ => M.sharpMajorant τ D S
  let Y : EnergyBand → ℕ → ℝ := fun τ N => X τ (2*N)^(2*D-1)
  have hX := fun τ => M.one_le_sharpMajorant τ D S
  have hm := fun τ => M.sharpMajorant_mono τ D S
  have hpositive (τ : EnergyBand) (d : ℕ) (a : V) (N : ℕ) :
      0 ≤ (M.sharpColumnQuantity τ a d N)^((2*d : ℕ) : ℝ)⁻¹ +
        (M.sharpZeroQuantity τ a d N)^((2*d : ℕ) : ℝ)⁻¹ :=
    add_nonneg (Real.rpow_nonneg (M.sharpColumnQuantity_nonneg τ a d N) _)
      (Real.rpow_nonneg (M.sharpZeroQuantity_nonneg τ a d N) _)
  have Hsum : CutoffPowerControl Y (2*D) (fun τ N =>
      ∑ d ∈ Finset.range (D+1), ∑ a ∈ S d,
        ((M.sharpColumnQuantity τ a d N)^((2*d : ℕ) : ℝ)⁻¹ +
         (M.sharpZeroQuantity τ a d N)^((2*d : ℕ) : ℝ)⁻¹)) := by
    apply cutoffPowerControl_sum (by omega)
      (hf := fun d _ τ N => Finset.sum_nonneg (fun a _ => hpositive τ d a N))
    intro d hd
    apply cutoffPowerControl_sum (by omega) (hf := fun a _ τ N => hpositive τ d a N)
    intro a haS
    obtain ⟨hdpos, hdD, ha, hq, hh⟩ := hS d a haS
    obtain ⟨C, hC, HC⟩ := Q.generator_quantities_contraction hX hm hp H ha hdpos hq hh
    apply cutoffPowerControl_add
      (fun τ N => Real.rpow_nonneg (M.sharpColumnQuantity_nonneg τ a d N) _)
      (fun τ N => Real.rpow_nonneg (M.sharpZeroQuantity_nonneg τ a d N) _)
    · refine ⟨C, hC, ?_⟩
      intro τ N
      exact root_lift_power_bound (M.sharpColumnQuantity_nonneg τ a d N)
        (zero_le_one.trans (hX τ (2*N))) hC (by omega) (by omega)
        (((M.root_sharpQuantity_le τ D S hdD haS).1).trans (hm τ (by omega : N ≤ 2*N))) (HC τ N).1
    · refine ⟨C, hC, ?_⟩
      intro τ N
      exact root_lift_power_bound (M.sharpZeroQuantity_nonneg τ a d N)
        (zero_le_one.trans (hX τ (2*N))) hC (by omega) (by omega)
        (((M.root_sharpQuantity_le τ D S hdD haS).2).trans (hm τ (by omega : N ≤ 2*N))) (HC τ N).2
  have Hraw : CutoffPowerControl Y (2*D) (fun τ => M.rawSharpMajorant τ D S) :=
    cutoffPowerControl_add (fun _ _ => zero_le_one)
      (fun τ N => Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun a _ => hpositive τ d a N)))
      (cutoffPowerControl_one (fun τ N => one_le_pow₀ (hX τ (2*N))) (2*D)) Hsum
  obtain ⟨C, hC, HC⟩ := Hraw
  refine ⟨C+1, by linarith, ?_⟩
  intro τ N
  obtain ⟨n, hn, he⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (N+1))
    (by simp) (M.rawSharpMajorant τ D S)
  change ((Finset.range (N+1)).sup' (by simp) (M.rawSharpMajorant τ D S))^(2*D) ≤ _
  rw [he]
  apply (HC τ n).trans
  have hXn := zero_le_one.trans (hX τ (2*n))
  have hnN : n ≤ N := by have := Finset.mem_range.mp hn; omega
  change C*X τ (2*n)^(2*D-1) ≤ (C+1)*X τ (2*N)^(2*D-1)
  gcongr
  · exact le_add_of_nonneg_right zero_le_one
  · exact hm τ (by omega)

end UnitaryStructure

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
