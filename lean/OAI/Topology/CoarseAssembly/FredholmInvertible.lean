import OAI.Topology.CoarseAssembly.KernelProjection

namespace OAI

/-! # Invertibility after the finite-rank kernel correction -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem isUnit_of_injective_compact_square (G : End H) (hinj : Function.Injective G)
    (hc : IsCompactOperator (G * G - 1 : End H)) : IsUnit G := by
  have hne : ¬ Module.End.HasEigenvalue (G * G - 1).toLinearMap (-1) := by
    intro he
    obtain ⟨x, hx, hxne⟩ := he.exists_hasEigenvector
    have hx' : G (G x) - x = -x := by
      simpa using (Module.End.mem_eigenspace_iff.mp hx)
    have hgg : G (G x) = 0 :=
      (sub_eq_iff_eq_add.mp hx').trans (neg_add_cancel x)
    have hg : G x = 0 := hinj (hgg.trans G.map_zero.symm)
    exact hxne (hinj (hg.trans G.map_zero.symm))
  have hr : (-1 : ℂ) ∈ resolventSet ℂ (G * G - 1) :=
    (hc.hasEigenvalue_or_mem_resolventSet (by norm_num)).resolve_left hne
  have hu := (spectrum.mem_resolventSet_iff.mp hr).neg
  simp only [map_neg, map_one] at hu
  have hs : IsUnit (G * G) := by
    convert hu using 1
    noncomm_ring
  rw [← pow_two] at hs
  exact (isUnit_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hs

theorem kernel_corrected_isUnit (F : End H) (hF : IsSelfAdjoint F)
    (hc : IsCompactOperator (F * F - 1 : End H)) : IsUnit (F + kernelProjection F) :=
  isUnit_of_injective_compact_square _ (kernel_corrected_injective F hF)
    (kernel_corrected_compact_square F hF hc)

end CoarseAssembly.Analytic

end

end OAI
