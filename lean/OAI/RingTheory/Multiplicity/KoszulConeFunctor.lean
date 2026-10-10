import Mathlib
import OAI.RingTheory.Multiplicity.PowerSeriesFlatVariables

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
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
variable {R : Type*} [CommRing R] {C : Type*} [Category C] [Abelian C]
  [CategoryTheory.Linear R C]

instance coneFunctor_linear (a : R) : Functor.Linear R (coneFunctor (C := C) a) where
  map_smul f r := by
    rename_i F G
    change mappingCone.map (a • 𝟙 F) (a • 𝟙 G) (r • f) (r • f)
        (by
          simp only [Linear.smul_comp, Linear.comp_smul, Category.comp_id, Category.id_comp]
          exact smul_comm r a f) =
      r • mappingCone.map (a • 𝟙 F) (a • 𝟙 G) f f
        (by simp [Linear.smul_comp, Linear.comp_smul])
    ext i
    rw [smul_f_apply]
    simp [mappingCone.ext_from_iff _ (i+1) i rfl, mappingCone.map,
      smul_f_apply,Linear.smul_comp,Linear.comp_smul]

instance tensorFunctor_linear (zs : List R) : Functor.Linear R (tensorFunctor (C := C) zs) := by
  induction zs with
  | nil => exact inferInstanceAs (Functor.Linear R (𝟭 (CochainComplex C ℤ)))
  | cons a zs ih =>
    change Functor.Linear R (tensorFunctor zs ⋙ coneFunctor a)
    infer_instance

instance single_linear (j : ℤ) : Functor.Linear R (single C (.up ℤ) j) where
  map_smul f r := by
    apply HomologicalComplex.Hom.ext
    funext i
    by_cases hi : i = j
    · subst i
      simp [single_map_f_self]
    · apply (isZero_single_obj_X (.up ℤ) j _ i hi).eq_of_src

end Lech.Koszul


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
universe u v
variable {R : Type u} [CommRing R]

lemma scalar_homology_zero_of_factorization (zs : List R) (M N : ModuleCat.{v} R)
    (u : N ⟶ M) (v : M ⟶ N) (a : R) (ha : v ≫ u = a • 𝟙 M)
    (i : ℤ) (hN : IsZero ((tensor zs (singleModule N)).homology i)) :
    a • 𝟙 ((tensor zs (singleModule M)).homology i) = 0 := by
  let K := single (ModuleCat.{v} R) (.up ℤ) (0 : ℤ) ⋙ tensorFunctor zs
  have hNK : IsZero ((K.obj N).homology i) := hN
  have he : homologyMap (K.map (v ≫ u)) i = 0 := by
    rw [K.map_comp,homologyMap_comp]
    rw [hNK.eq_zero_of_tgt (homologyMap (K.map v) i),zero_comp]
  rw [ha,K.map_smul,K.map_id,homologyMap_smul,homologyMap_id] at he
  exact he

lemma scalar_smul_homology_zero_of_factorization
    (zs : List R) (M : Type u) [AddCommGroup M] [Module R M]
    (r : ℕ) (u : (Fin r → R) →ₗ[R] M) (v : M →ₗ[R] (Fin r → R))
    (a : R) (ha : u.comp v = a • LinearMap.id)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (Fin r → R) zs.reverse)
    (i : ℤ) (hi : i < 0) (x : (tensor zs (singleModule (ModuleCat.of R M))).homology i) :
    a • x = 0 := by
  have he : (ModuleCat.ofHom v) ≫ (ModuleCat.ofHom u) =
      a • 𝟙 (ModuleCat.of R M) := by
    apply ModuleCat.hom_ext
    exact ha
  have hh := scalar_homology_zero_of_factorization zs (ModuleCat.of R M)
    (ModuleCat.of R (Fin r → R)) (ModuleCat.ofHom u) (ModuleCat.ofHom v) a he i
      (tensor_single_homology_zero_of_regular _ zs hreg i hi)
  exact congrArg (fun f => f x) hh
end Lech.Koszul


namespace Lech.PerfectDomainStages
open Lech.RootTower Lech.Koszul
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [CharP K p] [CharP L p]

local instance : IsDomain (MvPowerSeries (Fin h) k) := NoZeroDivisors.to_isDomain _

include K L in
 

theorem normalizedLength_regular_koszul (ys : List (MvPowerSeries (Fin h) k))
    (hys : (entryIdeal ys).radical = IsLocalRing.maximalIdeal (MvPowerSeries (Fin h) k))
    (hreg : ∀ r : ℕ, RingTheory.Sequence.IsWeaklyRegular
      (Fin r → PerfectClosure (MvPowerSeries (Fin h) k) p)
      (ys.map (PerfectClosure.of (MvPowerSeries (Fin h) k) p)))
    (i : ℤ) (hi : i < 0) :
    normalizedLength (Fin h) k p
      ((tensor ((ys.map (PerfectClosure.of (MvPowerSeries (Fin h) k) p)).reverse)
        (singleModule (ModuleCat.of (PerfectClosure (MvPowerSeries (Fin h) k) p)
          (PerfectClosure D p)))).homology i) = 0 := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let C := PerfectClosure D p
  let zs : List P := (ys.map (PerfectClosure.of A p)).reverse
  let F := singleModule (ModuleCat.of P C)
  have hflat := perfectClosure_flat (Fin h) k p
  let : IsIntegrallyClosed A := isIntegrallyClosed_of_flat_frobenius A p
    (fun n => iterateFrobenius_flat (σ := Fin h) (R := k) p n)
  have hinj (n : ℕ) := tensorMap_injective A D p L K hflat n
  obtain ⟨g,hg,hgc⟩ := exists_conductor A D p L K
  obtain ⟨r,a,ha,hfac⟩ := exists_root_finite_free_factorization A D p hinj ⟨g,hg,hgc⟩
  apply normalizedLength_eq_zero_of_root_annihilated h k p
    ((tensor zs F).homology i) (entryIdeal ys) hys ha
  · have hvars : (entryIdeal ys).map (PerfectClosure.of A p) ≤ entryIdeal zs := by
      rw [entryIdeal, Ideal.map_span]
      apply Ideal.span_le.mpr
      rintro _ ⟨y,hy,rfl⟩
      apply Ideal.subset_span
      change PerfectClosure.of A p y ∈ zs
      simp only [zs,List.mem_reverse,List.mem_map]
      exact ⟨y,hy,rfl⟩
    intro b hb x
    exact Module.mem_annihilator.mp
      (tensor_homology_annihilator zs F i (hvars (Ideal.mem_map_of_mem _ hb))) x
  · intro n x
    obtain ⟨u,v,huv⟩ := hfac n
    apply scalar_smul_homology_zero_of_factorization zs C r u v (rootMap A p n a) huv _ i hi x
    simpa only [zs,List.reverse_reverse] using hreg r

include K L in
 

theorem normalizedLength_coordinate_power_koszul (a : ℕ) (ha : a ≠ 0)
    (i : ℤ) (hi : i < 0) :
    normalizedLength (Fin h) k p
      ((tensor (((List.ofFn (fun j : Fin h =>
          (MvPowerSeries.X j : MvPowerSeries (Fin h) k)^a)).map
          (PerfectClosure.of (MvPowerSeries (Fin h) k) p)).reverse)
        (singleModule (ModuleCat.of (PerfectClosure (MvPowerSeries (Fin h) k) p)
          (PerfectClosure D p)))).homology i) = 0 := by
  apply normalizedLength_regular_koszul h k D p K L _ _
    (fun r => Lech.PowerSeries.perfect_free_variables_pow_weaklyRegular h k p r a ha) i hi
  let A := MvPowerSeries (Fin h) k
  have hm := Lech.PowerSeries.maximalIdeal_eq_variables (σ := Fin h) (k := k)
  apply le_antisymm
  · apply (IsLocalRing.maximalIdeal.isMaximal A).isPrime.isRadical.radical_le_iff.mpr
    apply Ideal.span_le.mpr
    intro x hx
    change x ∈ List.ofFn (fun j : Fin h => (MvPowerSeries.X j : A)^a) at hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    apply (IsLocalRing.maximalIdeal A).pow_mem_of_mem ?_ a (Nat.pos_of_ne_zero ha)
    rw [hm]
    exact Ideal.subset_span ⟨j,rfl⟩
  · rw [hm]
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact ⟨a, Ideal.subset_span (by simp only [Set.mem_ofPred_eq,List.mem_ofFn]; exact ⟨j,rfl⟩)⟩

include K L in
 

theorem normalizedLength_coordinate_koszul (i : ℤ) (hi : i < 0) :
    normalizedLength (Fin h) k p
      ((tensor (((List.ofFn (MvPowerSeries.X : Fin h → MvPowerSeries (Fin h) k)).map
          (PerfectClosure.of (MvPowerSeries (Fin h) k) p)).reverse)
        (singleModule (ModuleCat.of (PerfectClosure (MvPowerSeries (Fin h) k) p)
          (PerfectClosure D p)))).homology i) = 0 := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let C := PerfectClosure D p
  let zs : List P := ((List.ofFn (MvPowerSeries.X : Fin h → A)).map (PerfectClosure.of A p)).reverse
  let F := singleModule (ModuleCat.of P C)
  have hflat := perfectClosure_flat (Fin h) k p
  let : IsIntegrallyClosed A := isIntegrallyClosed_of_flat_frobenius A p
    (fun n => iterateFrobenius_flat (σ := Fin h) (R := k) p n)
  have hinj (n : ℕ) := tensorMap_injective A D p L K hflat n
  obtain ⟨g,hg,hgc⟩ := exists_conductor A D p L K
  obtain ⟨r,a,ha,hfac⟩ := exists_root_finite_free_factorization A D p hinj ⟨g,hg,hgc⟩
  apply normalizedLength_eq_zero_of_root_annihilated h k p
    ((tensor zs F).homology i) (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal.isMaximal A).isPrime.isRadical.radical ha
  · have hvars : (IsLocalRing.maximalIdeal A).map (PerfectClosure.of A p) ≤ entryIdeal zs := by
      rw [Lech.PowerSeries.maximalIdeal_eq_variables,Ideal.map_span]
      apply Ideal.span_le.mpr
      rintro _ ⟨_,⟨j,rfl⟩,rfl⟩
      apply Ideal.subset_span
      change PerfectClosure.of A p (MvPowerSeries.X j) ∈ zs
      simp only [zs,List.mem_reverse,List.mem_map,List.mem_ofFn]
      exact ⟨MvPowerSeries.X j,⟨j,rfl⟩,rfl⟩
    intro b hb x
    exact Module.mem_annihilator.mp
      (tensor_homology_annihilator zs F i (hvars (Ideal.mem_map_of_mem _ hb))) x
  · intro n x
    obtain ⟨u,v,huv⟩ := hfac n
    apply scalar_smul_homology_zero_of_factorization zs C r u v (rootMap A p n a) huv _ i hi x
    simpa only [zs,List.reverse_reverse] using
      Lech.PowerSeries.perfect_free_variables_weaklyRegular h k p r
end Lech.PerfectDomainStages


namespace Lech
universe u v
variable {R : Type u} [CommRing R] {C : Type v} [Category C] [Abelian C]

 

end Lech




namespace Lech.NormalizedLength.Tower
open CategoryTheory CategoryTheory.Limits
universe u
variable {P C : Type u} [CommRing P] [CommRing C]
 

noncomputable def torsionLength (T : Tower P) (f : P →+* C) (I : Ideal C) :
    Lech.TorsionLength I where
  value M := T.length ((ModuleCat.restrictScalars f).obj M)
  zero {M} hM := by
    have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp hM
    let : Subsingleton ((ModuleCat.restrictScalars f).obj M) := by
      change Subsingleton M
      infer_instance
    exact T.length_zero
  additive {S} hS _ := by
    let : Mono S.f := hS.mono_f
    let : Epi S.g := hS.epi_g
    let S' := S.map (ModuleCat.restrictScalars f)
    have hS' : S'.ShortExact := hS.map (ModuleCat.restrictScalars f)
    let : Mono S'.f := hS'.mono_f
    let : Epi S'.g := hS'.epi_g
    exact T.length_eq_add_of_exact S'.f.hom S'.g.hom
      ((ModuleCat.mono_iff_injective S'.f).mp inferInstance)
      ((ModuleCat.epi_iff_surjective S'.g).mp inferInstance)
      (fun x => ⟨S'.moduleCat_exact_iff.mp hS'.exact x, fun ⟨y,hy⟩ => by
        rw [← hy]
        exact ConcreteCategory.congr_hom S'.zero y⟩)
end Lech.NormalizedLength.Tower


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

lemma restrictScalars_map_scalar (f : R →+* S) (a : R)
    (F : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map (f a • 𝟙 F) =
      a • 𝟙 (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj F) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  rfl

 

noncomputable def restrictScalarsTensorIso (f : R →+* S) (zs : List R)
    (F : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj (tensor (zs.map f) F) ≅
      tensor zs (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj F) := by
  induction zs with
  | nil => exact Iso.refl _
  | cons a zs ih =>
    change ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
      (mappingCone (f a • 𝟙 (tensor (zs.map f) F))) ≅ _
    refine mappingCone.mapHomologicalComplexIso _ (ModuleCat.restrictScalars f) ≪≫ ?_
    rw [restrictScalars_map_scalar]
    exact (coneFunctor a).mapIso ih

noncomputable def restrictScalarsHomologyIso (f : R →+* S)
    (F : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) :
    (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj F).homology i ≅
      (ModuleCat.restrictScalars f).obj (F.homology i) :=
  (F.sc i).mapHomologyIso (ModuleCat.restrictScalars f)

 
noncomputable def restrictScalarsTensorHomologyIso (f : R →+* S) (zs : List R)
    (F : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) :
    (ModuleCat.restrictScalars f).obj ((tensor (zs.map f) F).homology i) ≅
      (tensor zs (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj F)).homology i :=
  (restrictScalarsHomologyIso f _ i).symm ≪≫
    (homologyFunctor _ _ i).mapIso (restrictScalarsTensorIso f zs F)

noncomputable def restrictScalarsSingleTensorHomologyIso (f : R →+* S) (zs : List R)
    (M : ModuleCat.{u} S) (i : ℤ) :
    (ModuleCat.restrictScalars f).obj
      ((tensor (zs.map f) ((single (ModuleCat S) (.up ℤ) 0).obj M)).homology i) ≅
      (tensor zs ((single (ModuleCat R) (.up ℤ) 0).obj
        ((ModuleCat.restrictScalars f).obj M))).homology i :=
  restrictScalarsTensorHomologyIso f zs _ i ≪≫
    (homologyFunctor _ _ i).mapIso
      ((tensorFunctor zs).mapIso
        ((singleMapHomologicalComplex (ModuleCat.restrictScalars f) (.up ℤ) 0).app M))
end Lech.Koszul


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
universe u
variable {R : Type u} [CommRing R]

noncomputable def coneTermEquiv (F : CochainComplex (ModuleCat.{u} R) ℤ) (a : R) (i : ℤ) :
    (mappingCone (a • 𝟙 F)).X i ≃ₗ[R] (F.X (i+1) × F.X i) :=
  (homotopyCofiber.XIsoBiprod (a • 𝟙 F) i (i+1) rfl ≪≫
    ModuleCat.biprodIsoProd _ _).toLinearEquiv

lemma tensor_terms_free (zs : List R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : ∀ i, Module.Free R (F.X i)) : ∀ i, Module.Free R ((tensor zs F).X i) := by
  induction zs with
  | nil => exact hF
  | cons a zs ih =>
    intro i
    let := ih (i+1)
    let := ih i
    exact Module.Free.of_equiv (coneTermEquiv (tensor zs F) a i).symm

lemma tensor_terms_finite (zs : List R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : ∀ i, Module.Finite R (F.X i)) : ∀ i, Module.Finite R ((tensor zs F).X i) := by
  induction zs with
  | nil => exact hF
  | cons a zs ih =>
    intro i
    let := ih (i+1)
    let := ih i
    exact Module.Finite.equiv (coneTermEquiv (tensor zs F) a i).symm

lemma unit_terms_free (zs : List R) (i : ℤ) : Module.Free R ((unit zs).X i) := by
  apply tensor_terms_free
  intro j
  by_cases hj : j = 0
  · subst j
    exact Module.Free.of_equiv
      ((singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).symm.toLinearEquiv)
  · let : Subsingleton (((singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).X j) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) j hj)
    infer_instance

lemma unit_terms_finite (zs : List R) (i : ℤ) : Module.Finite R ((unit zs).X i) := by
  apply tensor_terms_finite
  intro j
  by_cases hj : j = 0
  · subst j
    exact Module.Finite.equiv
      ((singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).symm.toLinearEquiv)
  · let : Subsingleton (((singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)).X j) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) j hj)
    infer_instance

 
def nullScalarIdeal (F : CochainComplex (ModuleCat.{u} R) ℤ) : Ideal R where
  carrier := {a | Nonempty (Homotopy (a • 𝟙 F) 0)}
  zero_mem' := by simpa using (show Nonempty (Homotopy (0 : F ⟶ F) 0) from ⟨Homotopy.refl _⟩)
  add_mem' := by
    rintro a b ⟨ha⟩ ⟨hb⟩
    change Nonempty (Homotopy ((a+b) • 𝟙 F) 0)
    simpa only [add_smul,add_zero] using (show Nonempty (Homotopy _ _) from ⟨ha.add hb⟩)
  smul_mem' := by
    rintro r a ⟨ha⟩
    change Nonempty (Homotopy ((r*a) • 𝟙 F) 0)
    simpa only [smul_eq_mul,mul_smul,smul_zero] using
      (show Nonempty (Homotopy _ _) from ⟨ha.smul r⟩)

lemma entryIdeal_le_nullScalarIdeal (zs : List R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) : entryIdeal zs ≤ nullScalarIdeal (tensor zs F) := by
  apply Ideal.span_le.mpr
  exact fun a ha => tensor_entry_nullhomotopic zs F a ha

lemma unit_nullhomotopic_of_mem (zs : List R) (a : R) (ha : a ∈ entryIdeal zs) :
    Nonempty (Homotopy (a • 𝟙 (unit zs)) 0) :=
  entryIdeal_le_nullScalarIdeal zs _ ha
end Lech.Koszul


namespace Lech.PerfectDomainStages
open Lech.RootTower Lech.Koszul CategoryTheory CategoryTheory.Limits CochainComplex
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [CharP K p] [CharP L p]

local instance : IsDomain (MvPowerSeries (Fin h) k) := NoZeroDivisors.to_isDomain _

include K L in
 

theorem normalizedLength_parameter_koszul (ys : List D) (hlen : ys.length = h)
    (hys : (entryIdeal ys).radical = IsLocalRing.maximalIdeal D) (i : ℤ) (hi : i < 0) :
    normalizedLength (Fin h) k p
      ((ModuleCat.restrictScalars (algebraMap (PerfectClosure (MvPowerSeries (Fin h) k) p)
        (PerfectClosure D p))).obj ((unit (ys.map (PerfectClosure.of D p))).homology i)) = 0 := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let C := PerfectClosure D p
  let f := algebraMap A D
  let Q := entryIdeal ys
  let I := (IsLocalRing.maximalIdeal A).map f
  have hIQ : I ≤ Q.radical := by
    rw [hys]
    exact IsLocalRing.map_maximalIdeal_le f
  obtain ⟨t,ht⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIQ
    (Ideal.FG.map (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A)) f)
  let a := t+1
  have ha : a ≠ 0 := Nat.succ_ne_zero t
  have hp : I^a ≤ Q := (Ideal.pow_le_pow_right (Nat.le_add_right t 1)).trans ht
  let zsA : List A := List.ofFn fun j : Fin h => (MvPowerSeries.X j : A)^a
  let zsP : List P := (zsA.map (PerfectClosure.of A p)).reverse
  let zsC : List C := zsP.map (algebraMap P C)
  let F := unit (ys.map (PerfectClosure.of D p))
  let T := regularTower (Fin h) k p
  let ell : Lech.TorsionLength (⊥ : Ideal C) := T.torsionLength (algebraMap P C) ⊥
  have hzlen : zsC.length = h := by simp [zsC,zsP,zsA]
  have hK (j : ℤ) (hj : j < 0) : ell.zeroClass ((unit zsC).homology j) := by
    refine ⟨⟨1, by simp⟩,?_⟩
    change T.length ((ModuleCat.restrictScalars (algebraMap P C)).obj
      ((unit zsC).homology j)) = 0
    change T.length ((ModuleCat.restrictScalars (algebraMap P C)).obj
      ((tensor (zsP.map (algebraMap P C)) ((single (ModuleCat C) (.up ℤ) 0).obj
        (ModuleCat.of C C))).homology j)) = 0
    rw [T.length_eq_of_equiv
      (restrictScalarsSingleTensorHomologyIso (algebraMap P C) zsP (ModuleCat.of C C) j).toLinearEquiv]
    exact normalizedLength_coordinate_power_koszul h k D p K L a ha j hj
  have hnull (b : C) (hb : b ∈ zsC) : Nonempty (Homotopy (b • 𝟙 F) 0) := by
    apply unit_nullhomotopic_of_mem
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hb
    change w ∈ (zsA.map (PerfectClosure.of A p)).reverse at hw
    have hw' : w ∈ zsA.map (PerfectClosure.of A p) := by simpa only [List.mem_reverse] using hw
    obtain ⟨v,hv,heq⟩ := List.mem_map.mp hw'
    subst w
    change v ∈ List.ofFn (fun j : Fin h => (MvPowerSeries.X j : A)^a) at hv
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hv
    subst v
    have hm : (MvPowerSeries.X j : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [Lech.PowerSeries.maximalIdeal_eq_variables]
      exact Ideal.subset_span ⟨j,rfl⟩
    have hq : f (MvPowerSeries.X j)^a ∈ Q := hp
      (Ideal.pow_mem_pow (Ideal.mem_map_of_mem f hm) a)
    have hmap : algebraMap P C (PerfectClosure.of A p ((MvPowerSeries.X j : A)^a)) =
        PerfectClosure.of D p (f (MvPowerSeries.X j)^a) := by
      change perfectMap p f (PerfectClosure.of A p _) = _
      rw [perfectMap_of,map_pow]
    rw [hmap]
    have hspan : Q.map (PerfectClosure.of D p) = entryIdeal (ys.map (PerfectClosure.of D p)) := by
      dsimp only [Q]
      rw [entryIdeal,Ideal.map_span]
      congr 1
      ext z
      simp only [Set.mem_image,Set.mem_ofPred_eq,List.mem_map]
    rw [← hspan]
    exact Ideal.mem_map_of_mem _ hq
  have hh := Lech.acyclicity_of_koszul ell.zeroClass zsC F
    (unit_terms_free _) (unit_terms_finite _) (fun j hj => ?_) hnull hK i hi
  · exact hh.2
  · apply unit_bounded
    simpa only [F,List.length_map,hlen,hzlen] using hj
end Lech.PerfectDomainStages
end

end OAI
