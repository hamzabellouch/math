import Mathlib
import OAI.RingTheory.Multiplicity.QuotientParameters

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped Pointwise
namespace Lech
universe u
variable {R : Type u} [CommRing R]

lemma scalar_range_eq (M : Type u) [AddCommGroup M] [Module R M] (g : R) :
    (LinearMap.lsmul R M g).range = Ideal.span {g} • (⊤ : Submodule R M) := by
  rw [Submodule.ideal_span_singleton_smul]
  ext x
  simp only [LinearMap.mem_range,LinearMap.lsmul_apply,
    Submodule.mem_smul_pointwise_iff_exists,Submodule.mem_top,true_and]

lemma scalar_comp_quotientπ (g : R) (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    (g • 𝟙 F) ≫ complexQuotientπ (Ideal.span {g}) F = 0 := by
  ext i : 1
  apply ModuleCat.hom_ext
  ext x
  change (Ideal.span {g} • (⊤ : Submodule R (F.X i))).mkQ (g • x) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [← scalar_range_eq]
  exact ⟨x,rfl⟩

def scalarQuotientShortComplex (g : R) (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (g • 𝟙 F) (complexQuotientπ (Ideal.span {g}) F) (scalar_comp_quotientπ g F)

lemma scalarQuotientShortExact (g : R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hg : ∀ j,Function.Injective (fun x : F.X j => g • x)) :
    (scalarQuotientShortComplex g F).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro j
  refine {exact := ?_,mono_f := ?_,epi_g := ?_}
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    change (Ideal.span {g} • (⊤ : Submodule R (F.X j))).mkQ x = 0 at hx
    have hm := (Submodule.Quotient.mk_eq_zero _).mp hx
    rw [← scalar_range_eq] at hm
    exact hm
  · exact (ModuleCat.mono_iff_injective _).mpr (hg j)
  · exact (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

lemma scalarHomologyKer (g : R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hg : ∀ j,Function.Injective (fun x : F.X j => g • x)) (i : ℤ) :
    (homologyMap (complexQuotientπ (Ideal.span {g}) F) i).hom.ker =
      (LinearMap.lsmul R (F.homology i) g).range := by
  have he := (scalarQuotientShortExact g F hg).homology_exact₂ i
  have hm := (ShortComplex.moduleCat_exact_iff _).mp he
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := hm x hx
    refine ⟨y,?_⟩
    change homologyMap (g • 𝟙 F) i y = x at hy
    rw [Koszul.homologyMap_smul,homologyMap_id] at hy
    exact hy
  · rintro ⟨y,rfl⟩
    have heq := congrArg (fun f => homologyMap f i) (scalar_comp_quotientπ g F)
    rw [homologyMap_comp,Koszul.homologyMap_smul,homologyMap_id,homologyMap_zero] at heq
    exact congrArg (fun f => f y) heq

def scalarHomologyCokernelEmbedding (g : R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hg : ∀ j,Function.Injective (fun x : F.X j => g • x)) (i : ℤ) :
    (F.homology i) ⧸ (LinearMap.lsmul R (F.homology i) g).range →ₗ[R]
      (((complexQuotient (Ideal.span {g}) (.up ℤ)).obj F).homology i) :=
  let f := (homologyMap (complexQuotientπ (Ideal.span {g}) F) i).hom
  let e := (Submodule.quotEquivOfEq _ _ (scalarHomologyKer g F hg i).symm).trans
    f.quotKerEquivRange
  f.range.subtype.comp e.toLinearMap

lemma scalarHomologyCokernelEmbedding_injective (g : R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hg : ∀ j,Function.Injective (fun x : F.X j => g • x)) (i : ℤ) :
    Function.Injective (scalarHomologyCokernelEmbedding g F hg i) := by
  let e := (Submodule.quotEquivOfEq _ _ (scalarHomologyKer g F hg i).symm).trans
    (homologyMap (complexQuotientπ (Ideal.span {g}) F) i).hom.quotKerEquivRange
  intro x y hxy
  apply e.injective
  apply Subtype.ext
  exact hxy

lemma homology_kernel_killed_of_scalar_retract
    {F G : CochainComplex (ModuleCat.{u} R) ℤ} (u : F ⟶ G) (v : G ⟶ F)
    (g : R) (h : u ≫ v = g • 𝟙 F) (i : ℤ) :
    ∀ x : (homologyMap u i).hom.ker, g • x = 0 := by
  intro x
  apply Subtype.ext
  have heq := congrArg (fun f => homologyMap f i) h
  rw [homologyMap_comp,Koszul.homologyMap_smul,homologyMap_id] at heq
  have hx := congrArg (fun f => f x) heq
  change homologyMap v i (homologyMap u i x) = g • (x : F.homology i) at hx
  rw [x.property,map_zero] at hx
  exact hx.symm

lemma homology_length_le_of_scalar_retract
    {F G : CochainComplex (ModuleCat.{u} R) ℤ} (u : F ⟶ G) (v : G ⟶ F)
    (g : R) (h : u ≫ v = g • 𝟙 F) (i : ℤ)
    (hg : ∀ j,Function.Injective (fun x : F.X j => g • x))
    (hfin : Module.length R (F.homology i) ≠ ⊤) :
    Module.length R (F.homology i) ≤ Module.length R (G.homology i) +
      Module.length R ((((complexQuotient (Ideal.span {g}) (.up ℤ)).obj F).homology i)) := by
  let f := (homologyMap u i).hom
  have hk := length_torsion_subquotient_le f.ker.subtype (LinearMap.id : f.ker →ₗ[R] f.ker)
    f.ker.subtype_injective Function.surjective_id g
    (homology_kernel_killed_of_scalar_retract u v g h i) hfin
  have he := Module.length_eq_add_of_exact f.rangeRestrict.ker.subtype f.rangeRestrict
    f.rangeRestrict.ker.subtype_injective f.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map f.rangeRestrict)
  have hk' : f.rangeRestrict.ker = f.ker := by ext; simp
  rw [hk'] at he
  rw [he,add_comm]
  exact add_le_add (Module.length_le_of_injective f.range.subtype f.range.subtype_injective)
    (hk.trans (Module.length_le_of_injective (scalarHomologyCokernelEmbedding g F hg i)
      (scalarHomologyCokernelEmbedding_injective g F hg i)))

lemma normalized_homology_length_le_of_scalar_retract (T : NormalizedLength.Tower R)
    {F G : CochainComplex (ModuleCat.{u} R) ℤ} (u : F ⟶ G) (v : G ⟶ F)
    (g : R) (h : u ≫ v = g • 𝟙 F) (i : ℤ)
    (hg : ∀ j,Function.Injective (fun x : F.X j => g • x))
    (hfin : T.length (F.homology i) ≠ ⊤) :
    T.length (F.homology i) ≤ T.length (G.homology i) +
      T.length ((((complexQuotient (Ideal.span {g}) (.up ℤ)).obj F).homology i)) := by
  let f := (homologyMap u i).hom
  have hk := T.length_torsion_subquotient_le f.ker.subtype (LinearMap.id : f.ker →ₗ[R] f.ker)
    f.ker.subtype_injective Function.surjective_id g
    (homology_kernel_killed_of_scalar_retract u v g h i) hfin
  have he := T.length_eq_add_of_exact f.rangeRestrict.ker.subtype f.rangeRestrict
    f.rangeRestrict.ker.subtype_injective f.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map f.rangeRestrict)
  have hk' : f.rangeRestrict.ker = f.ker := by ext; simp
  rw [hk'] at he
  rw [he,add_comm]
  exact add_le_add (T.length_le_of_injective f.range.subtype f.range.subtype_injective)
    (hk.trans (T.length_le_of_injective (scalarHomologyCokernelEmbedding g F hg i)
      (scalarHomologyCokernelEmbedding_injective g F hg i)))
end Lech

end

end OAI
