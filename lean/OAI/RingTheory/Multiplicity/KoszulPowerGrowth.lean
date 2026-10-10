import Mathlib
import OAI.RingTheory.Multiplicity.KoszulSwap
import OAI.RingTheory.Multiplicity.LechLengthLe

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech.Koszul
universe u
variable {R : Type u} [CommRing R]

lemma length_le_sum_of_exact (S : ShortComplex (ModuleCat.{u} R)) (hS : S.Exact) :
    Module.length R S.X₂ ≤ Module.length R S.X₁ + Module.length R S.X₃ := by
  have he : Function.Exact S.f.hom S.g.hom := by
    rw [LinearMap.exact_iff]
    ext x
    constructor
    · exact S.moduleCat_exact_iff.mp hS x
    · rintro ⟨y,rfl⟩
      exact congrArg (fun f : S.X₁ ⟶ S.X₃ => f y) S.zero
  have he' : Function.Exact S.f.hom S.g.hom.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, LinearMap.exact_iff.mp he]
  exact (Lech.length_le_add_of_exact S.f.hom S.g.hom.rangeRestrict
    S.g.hom.surjective_rangeRestrict he').trans
    (add_le_add le_rfl (Module.length_le_of_injective S.g.hom.range.subtype
      S.g.hom.range.subtype_injective))

lemma length_cone_comp_le {F G H : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : F ⟶ G) (g : G ⟶ H) (i : ℤ) :
    Module.length R ((mappingCone (f ≫ g)).homology i) ≤
      Module.length R ((mappingCone f).homology i) +
      Module.length R ((mappingCone g).homology i) := by
  let Q := HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i
  let T := mappingConeCompTriangleh f g
  have hT := HomotopyCategory.mappingConeCompTriangleh_distinguished f g
  have hex := Q.map_distinguished_exact T hT
  have hl := length_le_sum_of_exact _ hex
  let e := HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (.up ℤ) i
  have he (E : CochainComplex (ModuleCat.{u} R) ℤ) :
      Module.length R (Q.obj ((HomotopyCategory.quotient _ _).obj E)) =
        Module.length R (E.homology i) := (e.app E).toLinearEquiv.length_eq
  change Module.length R (Q.obj T.obj₂) ≤
    Module.length R (Q.obj T.obj₁) + Module.length R (Q.obj T.obj₃) at hl
  rw [← he (mappingCone (f ≫ g)), ← he (mappingCone f), ← he (mappingCone g)]
  exact hl

lemma length_cone_pow_le (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (x : R) (n : ℕ) (i : ℤ) :
    Module.length R ((mappingCone (x^n • 𝟙 F)).homology i) ≤
      n • Module.length R ((mappingCone (x • 𝟙 F)).homology i) := by
  induction n with
  | zero =>
    have he : mappingCone (x^0 • 𝟙 F) ≅ mappingCone (𝟙 F) :=
      eqToIso (congrArg (fun f : F ⟶ F => mappingCone f) (by simp))
    have hl : Module.length R ((mappingCone (x^0 • 𝟙 F)).homology i) =
        Module.length R ((mappingCone (𝟙 F)).homology i) :=
      ((homologyFunctor _ _ i).mapIso he).toLinearEquiv.length_eq
    rw [hl,zero_nsmul,le_zero_iff]
    apply Module.length_eq_zero_iff.mpr
    apply ModuleCat.isZero_iff_subsingleton.mp
    apply (IsZero.iff_id_eq_zero _).mpr
    simpa using (mappingCone.homotopyToZeroOfId F).homologyMap_eq i
  | succ n ih =>
    have he : x^(n+1) • 𝟙 F = (x^n • 𝟙 F) ≫ (x • 𝟙 F) := by
      simp [pow_succ,Linear.comp_smul,smul_smul,mul_comm]
    rw [he,add_nsmul,one_nsmul]
    exact (length_cone_comp_le _ _ i).trans (add_le_add ih le_rfl)

 

lemma length_tensor_powers_le (zs : List R) (q : ℕ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    Module.length R ((tensor (zs.map (fun z => z^q)) F).homology i) ≤
      (q^zs.length) • Module.length R ((tensor zs F).homology i) := by
  induction zs generalizing F with
  | nil =>
    change Module.length R (F.homology i) ≤ 1 • Module.length R (F.homology i)
    simp
  | cons a zs ih =>
    simp only [tensor_cons,List.length_cons,pow_succ]
    have h₁ := length_cone_pow_le (tensor (zs.map (fun z => z^q)) F) a q i
    have h₂ := ih (scalarCone a F)
    have he (ys : List R) :
        Module.length R ((scalarCone a (tensor ys F)).homology i) =
          Module.length R ((tensor ys (scalarCone a F)).homology i) :=
      ((homologyFunctor _ _ i).mapIso (tensorConeIso ys a F)).toLinearEquiv.length_eq
    rw [← he zs, ← he (zs.map (fun z => z^q))] at h₂
    calc
      _ ≤ q • Module.length R ((scalarCone a (tensor (zs.map (fun z => z^q)) F)).homology i) := h₁
      _ ≤ q • ((q^zs.length) • Module.length R ((scalarCone a (tensor zs F)).homology i)) :=
        nsmul_le_nsmul_right h₂ q
      _ = _ := by
        rw [smul_smul, Nat.mul_comm]
        rfl

end Lech.Koszul

end

end OAI
