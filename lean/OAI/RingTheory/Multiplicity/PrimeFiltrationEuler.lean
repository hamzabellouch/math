import Mathlib
import OAI.RingTheory.Multiplicity.TensorEuler

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma tensorEuler_submodule
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F)
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] (N : Submodule R M) :
    shortEuler R ((tensorModuleFunctor F).obj (ModuleCat.of R M))=
      shortEuler R ((tensorModuleFunctor F).obj (ModuleCat.of R N))+
      shortEuler R ((tensorModuleFunctor F).obj (ModuleCat.of R (M ⧸ N))) := by
  let S := ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ (by ext x; simp)
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (by change Function.Exact N.subtype N.mkQ; exact LinearMap.exact_iff.mpr (by simp))
    N.injective_subtype N.mkQ_surjective
  have hT := tensorModule_shortExact F (fun i => by have := hF.term_free i; infer_instance) S hS
  apply shortEuler_additive (S.map (tensorModuleFunctor F)) hT
  · exact tensorModule_homology_finite F hF (ModuleCat.of R N)
  · exact tensorModule_homology_finite F hF (ModuleCat.of R M)
  · exact tensorModule_homology_finite F hF (ModuleCat.of R (M ⧸ N))
  · exact tensorModule_homology_bounded F hF (ModuleCat.of R (M ⧸ N)) _ (Or.inl (by omega))
  · exact tensorModule_homology_bounded F hF (ModuleCat.of R N) _ (Or.inr (by omega))

namespace PrimeFiltration
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
lemma Factors.tensorEuler {N : Submodule R M} {ps : List (Ideal R)} (h : Factors N ps)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
    shortEuler R ((tensorModuleFunctor F).obj (ModuleCat.of R (M ⧸ N)))=
      (ps.map (fun P => shortEuler R ((tensorModuleFunctor F).obj (ModuleCat.of R (R ⧸ P))))).sum := by
  induction h with
  | top =>
      have hz := (tensorModuleFunctor F).map_isZero
        ((ModuleCat.isZero_iff_subsingleton (M:=ModuleCat.of R (M ⧸ (⊤:Submodule R M)))).mpr inferInstance)
      simp only [List.map_nil,List.sum_nil,shortEuler]
      apply Finset.sum_eq_zero
      intro i hi
      have : Subsingleton (((tensorModuleFunctor F).obj (ModuleCat.of R (M ⧸ (⊤:Submodule R M)))).homology (-(i:ℤ))) :=
        ModuleCat.isZero_iff_subsingleton.mp ((homologyFunctor _ _ (-(i:ℤ))).map_isZero hz)
      simp
  | @cons N J hNJ P hP e qs tail ih =>
      obtain ⟨e⟩ := e
      rw [tensorEuler_submodule F hF (J.map N.mkQ),tensorEuler_equiv F e,
        tensorEuler_equiv F (Submodule.quotientQuotientEquivQuotient N J hNJ),ih]
      rfl

lemma Factors.euler_self {ps : List (Ideal R)} (h : Factors (⊥ : Submodule R R) ps)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
    shortEuler R F=
      (ps.map (fun P => shortEuler R ((tensorModuleFunctor F).obj (ModuleCat.of R (R ⧸ P))))).sum := by
  have he := h.tensorEuler F hF
  rw [tensorEuler_equiv F (Submodule.quotEquivOfEqBot _ rfl),
    shortEuler_eq_of_iso (tensorModuleUnitIso F)] at he
  exact he
end PrimeFiltration
end Lech

end

end OAI
