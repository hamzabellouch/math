import Mathlib
import OAI.RingTheory.Multiplicity.RootTowerNormalizedLength

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
namespace Lech.PowerSeries
open RingTheory.Sequence
open scoped TensorProduct
variable (h : ℕ) (k : Type*) [Field k]

lemma flat_variables_weaklyRegular (M : Type*) [AddCommGroup M]
    [Module (MvPowerSeries (Fin h) k) M] [Module.Flat (MvPowerSeries (Fin h) k) M] :
    IsWeaklyRegular M (List.ofFn (MvPowerSeries.X : Fin h → MvPowerSeries (Fin h) k)) := by
  let A := MvPowerSeries (Fin h) k
  have hh := (variables_weaklyRegular k h).isWeaklyRegular_rTensor (M₂ := M)
  exact ((TensorProduct.lid A M).isWeaklyRegular_congr _).mp hh

lemma perfect_free_variables_weaklyRegular (p : ℕ) [Fact p.Prime]
    [CharP k p] [PerfectRing k p] (r : ℕ) :
    IsWeaklyRegular (Fin r → PerfectClosure (MvPowerSeries (Fin h) k) p)
      ((List.ofFn (MvPowerSeries.X : Fin h → MvPowerSeries (Fin h) k)).map
        (PerfectClosure.of (MvPowerSeries (Fin h) k) p)) := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let : Algebra A P := (PerfectClosure.of A p).toAlgebra
  have : Module.Flat A P := (RingHom.flat_algebraMap_iff).mp (RootTower.perfectClosure_flat (Fin h) k p)
  have : Module.Flat A (Fin r → P) := Module.Flat.trans A P (Fin r → P)
  exact (isWeaklyRegular_map_algebraMap_iff P (Fin r → P) _).mpr
    (flat_variables_weaklyRegular h k (Fin r → P))
end Lech.PowerSeries


namespace Lech
open RingTheory.Sequence
open scoped TensorProduct
lemma weaklyRegular_map_of_flat {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (zs : List R) (h : IsWeaklyRegular R zs) :
    IsWeaklyRegular S (zs.map f) := by
  let : Algebra R S := f.toAlgebra
  let : Module.Flat R S := hf
  apply (isWeaklyRegular_map_algebraMap_iff S S zs).mpr
  exact ((TensorProduct.lid R S).isWeaklyRegular_congr zs).mp
    (h.isWeaklyRegular_rTensor (M₂ := S))
end Lech


namespace Lech.PowerSeries
open RingTheory.Sequence
variable (h : ℕ) (k : Type*) [Field k]
lemma variables_pow_weaklyRegular (a : ℕ) (ha : a ≠ 0) :
    IsWeaklyRegular (MvPowerSeries (Fin h) k)
      (List.ofFn (fun i : Fin h => (MvPowerSeries.X i : MvPowerSeries (Fin h) k)^a)) := by
  let : NeZero a := ⟨ha⟩
  have hh := Lech.weaklyRegular_map_of_flat
    (MvPowerSeries.expand (σ := Fin h) (R := k) a ha).toRingHom
    (RootTower.expansion_flat a) _ (variables_weaklyRegular k h)
  simpa only [List.map_ofFn,Function.comp_def,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,MvPowerSeries.expand_X] using hh

lemma perfect_free_variables_pow_weaklyRegular (p : ℕ) [Fact p.Prime]
    [CharP k p] [PerfectRing k p] (r a : ℕ) (ha : a ≠ 0) :
    IsWeaklyRegular (Fin r → PerfectClosure (MvPowerSeries (Fin h) k) p)
      ((List.ofFn (fun i : Fin h => (MvPowerSeries.X i : MvPowerSeries (Fin h) k)^a)).map
        (PerfectClosure.of (MvPowerSeries (Fin h) k) p)) := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let : Algebra A P := (PerfectClosure.of A p).toAlgebra
  have : Module.Flat A P := (RingHom.flat_algebraMap_iff).mp (RootTower.perfectClosure_flat (Fin h) k p)
  have : Module.Flat A (Fin r → P) := Module.Flat.trans A P (Fin r → P)
  apply (isWeaklyRegular_map_algebraMap_iff P (Fin r → P) _).mpr
  exact ((TensorProduct.lid A (Fin r → P)).isWeaklyRegular_congr _).mp
    ((variables_pow_weaklyRegular h k a ha).isWeaklyRegular_rTensor (M₂ := Fin r → P))
end Lech.PowerSeries

open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace Lech.Koszul

variable {R : Type*} [CommRing R]
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  [CategoryTheory.Linear R C]
variable {F G : CochainComplex C ℤ}

instance (a : R) : (coneFunctor (C := C) a).Additive where
  map_add {F G} f g := by
    change mappingCone.map (a • 𝟙 F) (a • 𝟙 G) (f + g) (f + g)
        (by simp [Linear.smul_comp, Linear.comp_smul]) =
      mappingCone.map (a • 𝟙 F) (a • 𝟙 G) f f (by simp [Linear.smul_comp, Linear.comp_smul]) +
        mappingCone.map (a • 𝟙 F) (a • 𝟙 G) g g (by simp [Linear.smul_comp, Linear.comp_smul])
    ext i
    rw [HomologicalComplex.add_f_apply]
    simp [mappingCone.ext_from_iff _ (i + 1) i rfl, mappingCone.map,
      HomologicalComplex.add_f_apply, Preadditive.add_comp, Preadditive.comp_add]

instance (zs : List R) : (tensorFunctor (C := C) zs).Additive := by
  induction zs with
  | nil => exact inferInstanceAs (𝟭 (CochainComplex C ℤ)).Additive
  | cons a zs ih =>
    change (tensorFunctor zs ⋙ coneFunctor a).Additive
    infer_instance

 

end Lech.Koszul

open scoped ENNReal ZeroObject
namespace Lech
universe u
variable {R : Type u} [CommRing R]

 

namespace TorsionLength
variable {I : Ideal R} (ℓ : TorsionLength I)

end TorsionLength
end Lech

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex











open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech.FiniteComplex

variable {C : Type*} [Category C] [Abelian C]
variable (F : CochainComplex C ℤ) (n : ℤ)
  (hn : ∀ i, n < i → IsZero (F.X i))

end Lech.FiniteComplex

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian




namespace Lech
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
open scoped ZeroObject
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

 

end Lech






















namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
open RingTheory.Sequence
universe u v
variable {R : Type u} [CommRing R]

lemma cone_homology_zero_of_mono {C : Type*} [Category C] [Abelian C]
    {F G : CochainComplex C ℤ}
    (f : F ⟶ G) (i : ℤ) (hG : IsZero (G.homology i))
    [Mono (homologyMap f (i+1))] : IsZero ((mappingCone f).homology i) := by
  have hfmono : Mono (homologyMap f (i+1)) := inferInstance
  let Q := HomotopyCategory.homologyFunctor C (.up ℤ) i
  let T := mappingCone.triangleh f
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished f
  let e := HomotopyCategory.homologyFunctorFactors C (.up ℤ) i
  let e' := (HomotopyCategory.homologyFunctor C (.up ℤ) 0).shiftIso
    1 i (i+1) (by omega)
  let e'' := HomotopyCategory.homologyFunctorFactors C (.up ℤ) (i+1)
  have hm : Mono (Q.map ((CategoryTheory.shiftFunctor (HomotopyCategory C (.up ℤ)) (1 : ℤ)).map T.mor₁)) := by
    have hm' : Mono ((HomotopyCategory.homologyFunctor C (.up ℤ)
        (i+1)).map T.mor₁) := by
      have hh := e''.hom.naturality f
      have : Mono ((e''.hom.app F) ≫ homologyMap f (i+1)) :=
        mono_comp' (inferInstance : Mono (e''.hom.app F)) hfmono
      change Mono (e''.hom.app F ≫ (homologyFunctor C (.up ℤ) (i+1)).map f) at this
      rw [← hh] at this
      change Mono ((HomotopyCategory.homologyFunctor C (.up ℤ) (i+1)).map T.mor₁ ≫
        e''.hom.app G) at this
      exact mono_of_mono _ (e''.hom.app G)
    have : Mono (((e'.hom.app T.obj₁) ≫
        (HomotopyCategory.homologyFunctor C (.up ℤ) (i+1)).map T.mor₁)) :=
      mono_comp' (inferInstance : Mono (e'.hom.app T.obj₁)) hm'
    change Mono (e'.hom.app T.obj₁ ≫
      ((HomotopyCategory.homologyFunctor C (.up ℤ) 0).shift (i+1)).map T.mor₁) at this
    rw [← e'.hom.naturality T.mor₁] at this
    change Mono (Q.map ((CategoryTheory.shiftFunctor (HomotopyCategory C (.up ℤ)) (1 : ℤ)).map T.mor₁) ≫
      e'.hom.app T.obj₂) at this
    exact mono_of_mono (Q.map ((CategoryTheory.shiftFunctor (HomotopyCategory C (.up ℤ)) (1 : ℤ)).map T.mor₁))
      (e'.hom.app T.obj₂)
  have hex := Q.map_distinguished_exact T.rotate (Pretriangulated.rot_of_distTriang T hT)
  have hmneg : Mono (Q.map (-((CategoryTheory.shiftFunctor (HomotopyCategory C (.up ℤ)) (1 : ℤ)).map T.mor₁))) := by
    rw [Functor.map_neg]
    infer_instance
  have hz3 : Q.map T.mor₃ = 0 := by
    apply (cancel_mono (Q.map (-((CategoryTheory.shiftFunctor (HomotopyCategory C (.up ℤ)) (1 : ℤ)).map T.mor₁)))).mp
    rw [zero_comp]
    have hw := ((Pretriangulated.shortComplexOfDistTriangle T.rotate.rotate
      (Pretriangulated.rot_of_distTriang _ (Pretriangulated.rot_of_distTriang T hT))).map Q).zero
    exact hw
  have hzG : IsZero (Q.obj T.obj₂) := hG.of_iso (e.app G)
  have hz := hex.isZero_X₂ (hzG.eq_zero_of_src _) hz3
  exact hz.of_iso (e.app (mappingCone f)).symm

noncomputable def singleModule (M : ModuleCat.{v} R) : CochainComplex (ModuleCat.{v} R) ℤ :=
  (single _ (.up ℤ) 0).obj M

noncomputable def singleTensorHomologyZeroIso (M : ModuleCat.{v} R) (zs : List R) :
    (tensor zs (singleModule M)).homology 0 ≅
      ModuleCat.of R (M ⧸ (entryIdeal zs • (⊤ : Submodule R M))) := by
  let F := singleModule M
  have := quotientAugmentation_homology_top F 0 zs
    (fun j hj => isZero_single_obj_X (.up ℤ) 0 M j (by omega))
    (by apply (isZero_single_obj_X (.up ℤ) 0 M (-1) (by omega)).eq_zero_of_src)
  exact asIso (homologyMap (quotientAugmentation F zs) 0) ≪≫
    (homologyFunctor _ (.up ℤ) 0).mapIso
      ((singleMapHomologicalComplex (moduleQuotient (entryIdeal zs)) (.up ℤ) 0).app M) ≪≫
    singleObjHomologySelfIso (.up ℤ) 0 _

lemma tensor_single_homology_zero_of_regular (M : ModuleCat.{v} R) (zs : List R)
    (hreg : IsWeaklyRegular M zs.reverse) (i : ℤ) (hi : i < 0) :
    IsZero ((tensor zs (singleModule M)).homology i) := by
  induction zs generalizing i with
  | nil =>
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact isZero_single_obj_X (.up ℤ) 0 M i (by omega)
  | cons a zs ih =>
    rw [List.reverse_cons,isWeaklyRegular_append_iff,isWeaklyRegular_singleton_iff] at hreg
    have hreg' := hreg.1
    let F := tensor zs (singleModule M)
    have hm : Mono (homologyMap (a • 𝟙 F) (i+1)) := by
      rw [homologyMap_smul,homologyMap_id]
      by_cases hz : i+1 = 0
      · rw [hz]
        apply (ModuleCat.mono_iff_injective _).mpr
        let e := (singleTensorHomologyZeroIso M zs).toLinearEquiv
        have hh : IsSMulRegular (M ⧸ (entryIdeal zs • (⊤ : Submodule R M))) a := by
          have heq : Ideal.ofList zs.reverse = entryIdeal zs := by
            simp [entryIdeal,Ideal.ofList,List.mem_reverse]
          rw [heq] at hreg
          exact hreg.2
        intro x y hxy
        apply e.injective
        apply hh
        change a • x = a • y at hxy
        simpa only [map_smul] using congrArg e hxy
      · have hzero : IsZero (F.homology (i+1)) := ih hreg' (i+1) (by omega)
        exact hzero.mono _
    exact cone_homology_zero_of_mono (a • 𝟙 F) i (ih hreg' i hi)
end Lech.Koszul
end

end OAI
