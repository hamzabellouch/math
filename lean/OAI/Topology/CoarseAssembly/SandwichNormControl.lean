import OAI.Topology.CoarseAssembly.LocalizationNormContinuity

namespace OAI

/-! # Uniform estimates for changing localization isometries -/

noncomputable section

namespace CoarseAssembly

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def operatorSandwich (P : E →L[ℂ] H) (F : E →L[ℂ] E) : H →L[ℂ] H :=
  P.comp (F.comp P.adjoint)

theorem operatorSandwich_sub_norm_le (P Q : E →L[ℂ] H)
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (F G : E →L[ℂ] E) (C : ℝ) (hG : ‖G‖ ≤ C) :
    ‖operatorSandwich P F - operatorSandwich Q G‖ ≤
      ‖F - G‖ + 2 * C * ‖P - Q‖ := by
  have hC : 0 ≤ C := (norm_nonneg G).trans hG
  have hPa : ‖P.adjoint‖ ≤ 1 := by simpa only [ContinuousLinearMap.adjoint.norm_map] using hP
  have hd : ‖P.adjoint - Q.adjoint‖ = ‖P - Q‖ := by
    rw [← map_sub, ContinuousLinearMap.adjoint.norm_map]
  have h1 : ‖P.comp ((F - G).comp P.adjoint)‖ ≤ ‖F - G‖ := by
    calc
      _ ≤ ‖P‖ * (‖F - G‖ * ‖P.adjoint‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖F - G‖ * 1) := by gcongr
      _ = _ := by ring
  have h2 : ‖(P - Q).comp (G.comp P.adjoint)‖ ≤ C * ‖P - Q‖ := by
    calc
      _ ≤ ‖P - Q‖ * (‖G‖ * ‖P.adjoint‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ ‖P - Q‖ * (C * 1) := by gcongr
      _ = _ := by ring
  have h3 : ‖Q.comp (G.comp (P.adjoint - Q.adjoint))‖ ≤ C * ‖P - Q‖ := by
    calc
      _ ≤ ‖Q‖ * (‖G‖ * ‖P.adjoint - Q.adjoint‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (C * ‖P - Q‖) := by rw [hd]; gcongr
      _ = _ := by ring
  have he : operatorSandwich P F - operatorSandwich Q G =
      P.comp ((F - G).comp P.adjoint) + (P - Q).comp (G.comp P.adjoint) +
        Q.comp (G.comp (P.adjoint - Q.adjoint)) := by
    simp only [operatorSandwich, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖P.comp ((F - G).comp P.adjoint)‖ + ‖(P - Q).comp (G.comp P.adjoint)‖ +
        ‖Q.comp (G.comp (P.adjoint - Q.adjoint))‖ := (norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖F - G‖ + C * ‖P - Q‖ + C * ‖P - Q‖ := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

end CoarseAssembly

end

end OAI
