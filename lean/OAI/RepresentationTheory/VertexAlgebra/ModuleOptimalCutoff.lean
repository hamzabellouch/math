import OAI.RepresentationTheory.VertexAlgebra.ModuleSharpBounded

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q
theorem optimal_quasiPrimary_cutoff (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a)
    (hh : U.IsHermitian d a) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ N (m : ℤ) v, v ∈ M.energyCutoff τ N →
      ‖M.physicalMode a d m v‖ ≤ C*(1+|(m : ℝ)|)^(2*d)*(N+1 : ℝ)^(d-1)*‖v‖ := by
  obtain ⟨X, hX, hm, ⟨B, hB, HB⟩, H⟩ := Q.exists_bounded_sharpGrowth hc
  obtain ⟨C, hC, HC⟩ := Q.nonzeroModes_sharp_bound hX ha hq hh hd (fun e _ b hb => H e b hb)
  obtain ⟨D, hD, HD⟩ := Q.zeroMode_sharpGrowth hX hm (Q.polynomialEnergyBounds hc a)
    ha hq hh hd (fun e _ b hb => H e b hb)
  let K := (C+D+2)*B^(d-1)
  have hK : 0 < K := by dsimp [K]; positivity
  have Hzero (τ : EnergyBand) (N : ℕ) (v : W) (hv : v ∈ M.energyCutoff τ N) :
      ‖M.physicalMode a d 0 v‖ ≤ K*(N+1 : ℝ)^(d-1)*‖v‖ := by
    have Hn := norm_of_sharp_square (zero_le_one.trans (hX τ (2*N))) hD N (d-1) (d-1) v _ (HD τ N v hv)
    apply Hn.trans
    calc
      _ ≤ (C+D+2)*(N+1 : ℝ)^(d-1)*B^(d-1)*‖v‖ := by
        have hhX := zero_le_one.trans (hX τ (2*N))
        gcongr <;> linarith [HB τ (2*N)]
      _ = _ := by dsimp [K]; ring
  have Hpos (τ : EnergyBand) (N m : ℕ) (hm : 0 < m) (v : W) (hv : v ∈ M.energyCutoff τ N) :
      ‖M.physicalMode a d m v‖ ≤ K*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*‖v‖ ∧
      ‖M.physicalMode a d (-(m : ℤ)) v‖ ≤ K*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*‖v‖ := by
    have Hn := HC τ N m hm v hv
    have hbound : C*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*X τ N^(d-1)*‖v‖ ≤
        K*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*‖v‖ := by
      have hhX := zero_le_one.trans (hX τ N)
      calc
        _ ≤ (C+D+2)*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*B^(d-1)*‖v‖ := by
          gcongr
          · linarith
          · exact HB τ N
        _ = _ := by dsimp [K]; ring
    exact ⟨Hn.1.trans hbound, Hn.2.trans hbound⟩
  refine ⟨K, hK, ?_⟩
  intro τ N m v hv
  rcases m with m | m
  · by_cases hm0 : m = 0
    · subst m
      simpa using Hzero τ N v hv
    · simpa only [Int.ofNat_eq_natCast, Int.cast_natCast,
        abs_of_nonneg (show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m), add_comm 1 (m : ℝ)] using
        (Hpos τ N m (by omega) v hv).1
  · have he : Int.negSucc m = -((m+1 : ℕ) : ℤ) := by omega
    rw [he]
    simpa only [Int.cast_neg, abs_neg, Int.cast_natCast,
      abs_of_nonneg (show (0 : ℝ) ≤ ((m+1 : ℕ) : ℝ) from Nat.cast_nonneg (m+1)),
      add_comm 1 ((m+1 : ℕ) : ℝ)] using (Hpos τ N (m+1) (by omega) v hv).2

end UnitaryStructure

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
