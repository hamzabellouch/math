import OAI.RingTheory.DirectFiniteness.SlabPatch

namespace OAI

noncomputable section
open Module
namespace KaplanskyCounterexample.FiniteGeometry

lemma exists_plane_operator (Q E : Type) [Field Q] [Fintype Q] [CharP Q 2]
    [AddCommGroup E] [Module Q E] [Fintype E] (P : Plane Q E) :
    ∃ J : P.val →ₗ[Q] P.val, NoEigenvector J := by
  obtain ⟨F,hF,hA,hfin,hD⟩ := exists_finite_extension Q 2 (by decide)
  let _ := hF
  let _ := hA
  let _ := hfin
  have hdP : finrank Q P.val=2 := P.property
  let e : P.val ≃ₗ[Q] F := LinearEquiv.ofFinrankEq _ _ (hdP.trans hD.symm)
  obtain ⟨J,hJ⟩ := exists_noEigenvector_of_quadratic hD
  refine ⟨e.symm.toLinearMap.comp (J.comp e.toLinearMap),?_⟩
  intro x hx c hc
  apply hJ (e x) (fun h => hx (e.injective (h.trans e.map_zero.symm))) c
  have he := congrArg e hc
  simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,map_smul] using he

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
