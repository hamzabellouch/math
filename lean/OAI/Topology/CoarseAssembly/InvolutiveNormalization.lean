import OAI.Topology.CoarseAssembly.RealNormalization
import OAI.Topology.CoarseAssembly.CompactFunctionalCalculus
import OAI.Topology.CoarseAssembly.UnitalCycleInvertible

namespace OAI

/-! # Involutive representatives by compact functional calculus -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem squareDefect_cfc (F : End H) (hF : IsSelfAdjoint F) :
    cfc (fun x : ℝ => x ^ 2 - 1) F = F * F - 1 := by
  rw [cfc_sub (fun x : ℝ => x ^ 2) (fun _ => 1) F,
    cfc_pow_id F 2 hF, cfc_const_one ℝ F hF, pow_two]

theorem inverseSqrtCorrection_continuousOn (F : End H) (hF : IsSelfAdjoint F)
    (hu : IsUnit F) :
    ContinuousOn inverseSqrtCorrection (quasispectrum ℝ (F * F - 1)) := by
  rw [quasispectrum_eq_spectrum_union_zero, ← squareDefect_cfc F hF,
    cfc_map_spectrum (fun x : ℝ => x ^ 2 - 1) F hF]
  intro t ht
  rcases ht with ⟨x, hx, rfl⟩ | ht
  · apply (inverseSqrtCorrection_continuousAt _).continuousWithinAt
    have hx0 : x ≠ 0 := fun h => spectrum.zero_notMem ℝ hu (h ▸ hx)
    simpa using sq_pos_of_ne_zero hx0
  · have ht0 : t = 0 := ht
    subst t
    exact (inverseSqrtCorrection_continuousAt (by norm_num)).continuousWithinAt

theorem inverseSqrtCorrection_continuousOn_image (F : End H) (hu : IsUnit F) :
    ContinuousOn inverseSqrtCorrection ((fun x : ℝ => x ^ 2 - 1) '' spectrum ℝ F) := by
  rintro t ⟨x, hx, rfl⟩
  apply (inverseSqrtCorrection_continuousAt _).continuousWithinAt
  have hx0 : x ≠ 0 := fun h => spectrum.zero_notMem ℝ hu (h ▸ hx)
  simpa using sq_pos_of_ne_zero hx0

theorem normalizedReal_continuousOn (F : End H) (hu : IsUnit F) :
    ContinuousOn normalizedReal (spectrum ℝ F) := by
  have hc := (inverseSqrtCorrection_continuousOn_image F hu).comp
    ((continuous_id.pow 2).sub continuous_const).continuousOn (Set.mapsTo_image _ _)
  exact continuousOn_id.add (continuousOn_id.mul hc)

def involutiveNormalization (F : End H) : End H := cfc normalizedReal F

theorem involutiveNormalization_eq (F : End H) (hF : IsSelfAdjoint F) (hu : IsUnit F) :
    involutiveNormalization F = F + F * cfc inverseSqrtCorrection (F * F - 1) := by
  have hg := inverseSqrtCorrection_continuousOn_image F hu
  have hc : ContinuousOn (fun x : ℝ => inverseSqrtCorrection (x ^ 2 - 1))
      (spectrum ℝ F) := by
    exact hg.comp (by fun_prop) (Set.mapsTo_image _ _)
  unfold involutiveNormalization normalizedReal
  rw [cfc_add F (fun x : ℝ => x) (fun x => x * inverseSqrtCorrection (x ^ 2 - 1))
    continuousOn_id (continuousOn_id.mul hc),
    cfc_mul (fun x : ℝ => x) (fun x => inverseSqrtCorrection (x ^ 2 - 1)) F
      continuousOn_id hc,
    cfc_id' ℝ F hF,
    cfc_comp' inverseSqrtCorrection (fun x : ℝ => x ^ 2 - 1) F hg,
    squareDefect_cfc F hF]

theorem involutiveNormalization_sq (F : End H) (hF : IsSelfAdjoint F) (hu : IsUnit F) :
    involutiveNormalization F * involutiveNormalization F = 1 := by
  rw [← pow_two, involutiveNormalization, ← cfc_pow normalizedReal 2 F
    (normalizedReal_continuousOn F hu) hF]
  calc
    cfc (fun x => normalizedReal x ^ 2) F = cfc (fun _ : ℝ => 1) F := by
      apply cfc_congr
      intro x hx
      exact normalizedReal_sq (fun h => spectrum.zero_notMem ℝ hu (h ▸ hx))
    _ = 1 := cfc_const_one ℝ F hF

theorem involutiveNormalization_selfAdjoint (F : End H) :
    IsSelfAdjoint (involutiveNormalization F) := IsSelfAdjoint.cfc

theorem involutiveCorrection_compact (F : End H) (hF : IsSelfAdjoint F) (hu : IsUnit F)
    (hc : IsCompactOperator (F * F - 1 : End H)) :
    IsCompactOperator (F * cfc inverseSqrtCorrection (F * F - 1) : End H) ∧
    IsCompactOperator (star (F * cfc inverseSqrtCorrection (F * F - 1)) : End H) := by
  have hs : star (F * F - 1) = F * F - 1 := by rw [star_sub, star_mul, hF.star_eq, star_one]
  have hcs : IsCompactOperator (star (F * F - 1) : End H) := by rw [hs]; exact hc
  have hq := compact_cfc inverseSqrtCorrection (F * F - 1) hc hcs
    (inverseSqrtCorrection_continuousOn F hF hu) inverseSqrtCorrection_zero
  refine ⟨compact_mul_left hq F, ?_⟩
  rw [star_mul, (IsSelfAdjoint.cfc (f := inverseSqrtCorrection) (a := F * F - 1)).star_eq]
  exact compact_mul_right hq (star F)

variable {A : Type} [CStarAlgebra A]

theorem exists_involutive_representative (c : OddCycle A) (hunital : c.representation 1 = 1) :
    ∃ d : OddCycle A, cycleClass A d = cycleClass A c ∧ d.representation 1 = 1 ∧
      IsSelfAdjoint d.operator ∧ d.operator * d.operator = 1 := by
  obtain ⟨d, hdc, hdu, hds, hdi⟩ := exists_invertible_selfAdjoint_representative c hunital
  have hc : IsCompactOperator (d.operator * d.operator - 1 : End d.space) := by
    simpa only [hdu, mul_one] using d.square_compact 1
  obtain ⟨hK, hKs⟩ := involutiveCorrection_compact d.operator hds hdi hc
  refine ⟨d.compactPerturb _ hK hKs, (compactPerturb_class d _ hK hKs).trans hdc, hdu, ?_, ?_⟩
  · change IsSelfAdjoint (d.operator + d.operator * cfc inverseSqrtCorrection
      (d.operator * d.operator - 1))
    rw [← involutiveNormalization_eq d.operator hds hdi]
    exact involutiveNormalization_selfAdjoint d.operator
  · change (d.operator + d.operator * cfc inverseSqrtCorrection (d.operator * d.operator - 1)) *
      (d.operator + d.operator * cfc inverseSqrtCorrection (d.operator * d.operator - 1)) = 1
    rw [← involutiveNormalization_eq d.operator hds hdi]
    exact involutiveNormalization_sq d.operator hds hdi

end CoarseAssembly.Analytic

end

end OAI
