import Mathlib
import OAI.RingTheory.Multiplicity.LechNatTrans

namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech.Koszul
variable {R : Type*} [CommRing R] {C : Type*} [Category C] [Abelian C]
  [CategoryTheory.Linear R C]

 
noncomputable def tensorSingleHomologyIso (zs : List R) (M : C) (j i : ℤ) :
    (tensor zs ((singleFunctor C j).obj M)).homology i ≅
      (tensor zs ((singleFunctor C 0).obj M)).homology (i - j) := by
  let e : ((singleFunctor C 0).obj M)⟦-j⟧ ≅ (singleFunctor C j).obj M :=
    ((CochainComplex.singleFunctors C).shiftIso (-j) j 0 (by omega)).app M
  have e' : tensor zs ((singleFunctor C j).obj M) ≅
      tensor zs (((singleFunctor C 0).obj M)⟦-j⟧) := by
    simpa only [tensorFunctor_obj] using (tensorFunctor zs).mapIso e.symm
  exact (homologyFunctor C (ComplexShape.up ℤ) i).mapIso
      (e' ≪≫ (tensorShiftIso zs ((singleFunctor C 0).obj M) (-j)).symm) ≪≫
    ((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso (-j) i (i - j)
      (by omega)).app _

end Lech.Koszul


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
universe u
variable {R : Type u} [CommRing R]

 

lemma augmentation_scalar_isoMod (P : ObjectProperty (ModuleCat.{u} R))
    [P.IsSerreClass] (zs : List R)
    (hKos : ∀ i : ℤ, i < 0 → P ((unit zs).homology i)) (j i : ℤ) :
    P.isoModSerre (homologyMap (quotientAugmentation
      ((single (ModuleCat.{u} R) (.up ℤ) j).obj (ModuleCat.of R R)) zs) i) := by
  let F := (single (ModuleCat.{u} R) (.up ℤ) j).obj (ModuleCat.of R R)
  have hF : ∀ k, j < k → IsZero (F.X k) := fun k hk =>
    isZero_single_obj_X (.up ℤ) j _ k (by omega)
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · have hK : P ((tensor zs F).homology i) :=
      (P.prop_iff_of_iso (tensorSingleHomologyIso zs (ModuleCat.of R R) j i)).mpr
        (hKos (i-j) (by omega))
    have hG : IsZero (((complexQuotient (entryIdeal zs) (.up ℤ)).obj F).homology i) :=
      ExactAt.isZero_homology (ExactAt.of_isZero
        ((moduleQuotient (entryIdeal zs)).map_isZero
          (isZero_single_obj_X (.up ℤ) j _ i (by omega))))
    rw [hG.eq_zero_of_tgt (homologyMap (quotientAugmentation F zs) i)]
    exact (P.isoModSerre_zero_iff _ _).mpr ⟨hK, P.prop_of_isZero hG⟩
  · have : IsIso (homologyMap (quotientAugmentation F zs) i) :=
      quotientAugmentation_homology_top F i zs hF rfl
    exact P.isoModSerre_of_isIso _
  · have hK : IsZero ((tensor zs F).homology i) :=
      ExactAt.isZero_homology (ExactAt.of_isZero (tensor_isZero_above F zs j hF i hgt))
    have hG : IsZero (((complexQuotient (entryIdeal zs) (.up ℤ)).obj F).homology i) :=
      ExactAt.isZero_homology (ExactAt.of_isZero
        ((moduleQuotient (entryIdeal zs)).map_isZero (hF i hgt)))
    rw [hG.eq_zero_of_tgt (homologyMap (quotientAugmentation F zs) i)]
    exact (P.isoModSerre_zero_iff _ _).mpr ⟨P.prop_of_isZero hK, P.prop_of_isZero hG⟩

lemma augmentation_free_isoMod (P : ObjectProperty (ModuleCat.{u} R))
    [P.IsSerreClass] (zs : List R)
    (hKos : ∀ i : ℤ, i < 0 → P ((unit zs).homology i))
    (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M] (j i : ℤ) :
    P.isoModSerre (homologyMap (quotientAugmentation
      ((single (ModuleCat.{u} R) (.up ℤ) j).obj M) zs) i) := by
  let Q := P.isoModSerre.Q
  let := ObjectProperty.SerreClassLocalization.abelian Q P
  let α := CategoryTheory.Functor.whiskerLeft (single (ModuleCat.{u} R) (.up ℤ) j)
    (CategoryTheory.Functor.whiskerRight (CategoryTheory.Functor.whiskerRight (quotientAugmentationNat zs)
      (homologyFunctor _ (.up ℤ) i)) Q)
  have : IsIso (α.app (ModuleCat.of R R)) :=
    (ObjectProperty.SerreClassLocalization.isIso_map_iff Q P _).mpr
      (augmentation_scalar_isoMod P zs hKos j i)
  have : IsIso (α.app M) := isIso_app_of_finite_free _ _ α M
  exact (ObjectProperty.SerreClassLocalization.isIso_map_iff Q P _).mp this

 

lemma augmentation_finiteFree_bounded_isoMod
    (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass] (zs : List R)
    (hKos : ∀ i : ℤ, i < 0 → P ((unit zs).homology i))
    (F : CochainComplex (ModuleCat.{u} R) ℤ) [∀ j, Module.Free R (F.X j)]
    [∀ j, Module.Finite R (F.X j)] (n : ℤ) (h : ℕ)
    (hsupp : ∀ i, i < n ∨ n+h ≤ i → IsZero (F.X i)) (i : ℤ) :
    P.isoModSerre (homologyMap (quotientAugmentation F zs) i) := by
  apply quotientAugmentation_bounded P F zs n h hsupp
  intro j k
  exact augmentation_free_isoMod P zs hKos (F.X j) j k

end Lech.Koszul


namespace Lech
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

lemma monoModSerre_of_comp (P : ObjectProperty C) [P.IsSerreClass]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : P.monoModSerre (f ≫ g)) : P.monoModSerre f := by
  let k : kernel f ⟶ kernel (f ≫ g) := kernel.lift _ (kernel.ι f) (by simp)
  have hk : k ≫ kernel.ι (f ≫ g) = kernel.ι f := by simp [k]
  let : Mono k := mono_of_mono_fac hk
  exact P.prop_of_mono k h

 
lemma isIso_of_image_factorizations {A B D I : C}
    (u : A ⟶ B) (v : A ⟶ D) [Mono v] (f : B ⟶ D)
    (e : B ⟶ I) [Epi e] (m : I ⟶ D) [Mono m]
    (hfac : e ≫ m = f) (hforward : u ≫ f = v)
    (backward : B ⟶ A) (hbackward : backward ≫ v = f) :
    IsIso (u ≫ e) := by
  have he : (u ≫ e) ≫ m = v := by rw [Category.assoc, hfac, hforward]
  have : Mono (u ≫ e) := mono_of_mono_fac he
  have hb : backward ≫ (u ≫ e) = e := by
    apply (cancel_mono m).mp
    rw [Category.assoc, he, hbackward, hfac]
  have : Epi (u ≫ e) := epi_of_epi_fac hb
  exact isIso_of_mono_of_epi _

 

lemma cofinal_stableImage_isoMod (P : ObjectProperty C) [P.IsSerreClass]
    {A N M Jb Ja : C}
    (iN : A ⟶ N) (iM : A ⟶ M) (ib : A ⟶ Jb) (ia : A ⟶ Ja)
    (f : N ⟶ M) (u : N ⟶ Jb) (v : Jb ⟶ Ja) (w : Ja ⟶ M)
    (hn : iN ≫ f = iM) (hb : ib ≫ v = ia) (ha : ia ≫ w = iM)
    (hfact : u ≫ v ≫ w = f) (hmono : P.monoModSerre iM)
    (hstable : P.isoModSerre (ib ≫ factorThruImage v)) :
    P.isoModSerre (iN ≫ factorThruImage f) := by
  let Q := P.isoModSerre.Q
  let := ObjectProperty.SerreClassLocalization.abelian Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits Q P
  have : Mono (Q.map iM) :=
    (ObjectProperty.SerreClassLocalization.mono_map_iff Q P _).mpr hmono
  let j := Q.map (ib ≫ factorThruImage v)
  have : IsIso j := (ObjectProperty.SerreClassLocalization.isIso_map_iff Q P _).mpr hstable
  let lift := Q.map (factorThruImage v) ≫ inv j
  have hj : j ≫ Q.map (Limits.image.ι v) = Q.map ia := by
    dsimp only [j]
    rw [← Q.map_comp, Category.assoc, Limits.image.fac, hb]
  have hl : lift ≫ Q.map ia = Q.map v := by
    dsimp only [lift]
    rw [← hj, Category.assoc, IsIso.inv_hom_id_assoc, ← Q.map_comp, Limits.image.fac]
  have hback : (Q.map u ≫ lift) ≫ Q.map iM = Q.map f := by
    rw [← ha, Q.map_comp, Category.assoc, ← Category.assoc lift, hl,
      ← Q.map_comp, ← Q.map_comp]
    simpa only [Category.assoc] using congrArg Q.map hfact
  have hiso : IsIso (Q.map iN ≫ Q.map (factorThruImage f)) :=
    isIso_of_image_factorizations (Q.map iN) (Q.map iM) (Q.map f)
      (Q.map (factorThruImage f)) (Q.map (Limits.image.ι f))
      (by rw [← Q.map_comp, Limits.image.fac]) (by rw [← Q.map_comp, hn])
      (Q.map u ≫ lift) hback
  apply (ObjectProperty.SerreClassLocalization.isIso_map_iff Q P _).mp
  simpa only [Q.map_comp] using hiso

end Lech

open scoped BigOperators
namespace Lech

variable {R : Type*} [CommRing R]

 
lemma sup_pow_add_pred_le (I J : Ideal R) (n m : ℕ) :
    (I ⊔ J) ^ (n + m - 1) ≤ I ^ n ⊔ J ^ m := by
  rw [← Ideal.add_eq_sup, ← Ideal.add_eq_sup, add_pow, Ideal.sum_eq_sup]
  apply Finset.sup_le
  intro i hi
  by_cases hn : n ≤ i
  · exact Ideal.mul_le_left.trans (Ideal.mul_le_left.trans
      ((Ideal.pow_le_pow_right hn).trans le_sup_left))
  · refine Ideal.mul_le_left.trans (Ideal.mul_le_right.trans
      ((Ideal.pow_le_pow_right ?_).trans le_sup_right))
    omega

 
lemma finset_sup_pow_le {ι : Type*} (s : Finset ι) (I : ι → Ideal R)
    (a : ℕ) (ha : 1 ≤ a) :
    s.sup I ^ (s.card * (a - 1) + 1) ≤ s.sup (fun j => I j ^ a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj hs =>
    rw [Finset.sup_insert, Finset.sup_insert, Finset.card_insert_of_notMem hj]
    have he : (s.card + 1) * (a - 1) + 1 = a + (s.card * (a - 1) + 1) - 1 := by
      rw [add_mul, one_mul]
      omega
    rw [he]
    exact (sup_pow_add_pred_le (I j) (s.sup I) a _).trans (sup_le_sup_left hs _)

 

lemma parameter_power_cofinality (h a : ℕ) (ha : 1 ≤ a) (z : Fin h → R) :
    (Ideal.span (Set.range z)) ^ (h * (a - 1) + 1) ≤
      Ideal.span (Set.range fun j => z j ^ a) ∧
    Ideal.span (Set.range fun j => z j ^ a) ≤ (Ideal.span (Set.range z)) ^ a := by
  constructor
  · have H := finset_sup_pow_le Finset.univ (fun j : Fin h => Ideal.span {z j}) a ha
    simpa only [Finset.card_univ, Fintype.card_fin, Finset.sup_univ_eq_iSup,
      Ideal.span_singleton_pow, ← Ideal.span_range_eq_iSup] using H
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self j)) a

end Lech


namespace Lech
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
open Koszul
universe u v
variable {R : Type u} [CommRing R]

lemma entryIdeal_power_antitone (zs : List R) {a b : ℕ} (h : a ≤ b) :
    entryIdeal (zs.map (· ^ b)) ≤ entryIdeal (zs.map (· ^ a)) := by
  apply Ideal.span_le.mpr
  intro x hx
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
  have he : r^b = r^(b-a) * r^a := by rw [← pow_add, Nat.sub_add_cancel h]
  rw [he]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (List.mem_map.mpr ⟨r,hr,rfl⟩))

 
lemma quotientAugmentation_power_naturality
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (zs : List R)
    (a b : ℕ) (hab : a ≤ b) :
    quotientAugmentation F (zs.map (· ^ b)) ≫
        (complexQuotientMap (entryIdeal_power_antitone zs hab) (.up ℤ)).app F =
      powerMap F a b hab zs ≫ quotientAugmentation F (zs.map (· ^ a)) := by
  let Ha : ∀ r ∈ zs.map (· ^ a), r • 𝟙 ((complexQuotient
      (entryIdeal (zs.map (· ^ a))) (.up ℤ)).obj F) = 0 := fun r hr =>
    complexQuotient_annihilated _ r (Ideal.subset_span hr) F
  let Hb : ∀ r ∈ zs.map (· ^ b), r • 𝟙 ((complexQuotient
      (entryIdeal (zs.map (· ^ a))) (.up ℤ)).obj F) = 0 := fun r hr =>
    complexQuotient_annihilated _ r
      (entryIdeal_power_antitone zs hab (Ideal.subset_span hr)) F
  simp only [quotientAugmentation]
  let Hbb := fun r hr => complexQuotient_annihilated
    (entryIdeal (zs.map (· ^ b))) r (Ideal.subset_span hr) F
  exact (augmentation_naturality_target
    (complexQuotientπ (entryIdeal (zs.map (· ^ b))) F)
    ((complexQuotientMap (entryIdeal_power_antitone zs hab) (.up ℤ)).app F)
    (zs.map (· ^ b)) Hbb Hb).trans
    ((congrArg (fun k => augmentation k (zs.map (· ^ b)) Hb)
      (complexQuotientπ_map (entryIdeal_power_antitone zs hab) F)).trans
      (powerMap_augmentation _ zs a b hab Ha Hb).symm)

 

lemma koszul_stableImage_isIso
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (zs : List R) (t a b : ℕ)
    (H : ∀ r ∈ zs, Homotopy (r^t • 𝟙 F) 0)
    (hta : t ≤ a) (hab : a ≤ b) (hgap : zs.length*t ≤ b-a) (i : ℤ) :
    IsIso (homologyMap (inclusion F (zs.map (· ^ b))) i ≫
      factorThruImage (homologyMap (powerMap F a b hab zs) i)) := by
  classical
  apply stableImage_isIso _ (homologyMap (inclusion F (zs.map (· ^ a))) i)
  · rw [← homologyMap_comp, powerMap_inclusion]
  · apply inclusion_homology_injective
    intro x hx
    let e := List.mem_map.mp hx
    exact e.choose_spec.2 ▸ scalarPowerHomotopy F e.choose t a hta (H _ e.choose_spec.1)
  · exact powerMap_range_eq F zs t H a b hab hgap i

 

lemma parameterPower_stableImage_isoMod
    (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ j, Module.Free R (F.X j)] [∀ j, Module.Finite R (F.X j)]
    (n : ℤ) (h : ℕ) (hsupp : ∀ i, i < n ∨ n+h ≤ i → IsZero (F.X i))
    (zs : List R) (t a b : ℕ)
    (H : ∀ r ∈ zs, Homotopy (r^t • 𝟙 F) 0)
    (hta : t ≤ a) (hab : a ≤ b) (hgap : zs.length*t ≤ b-a)
    (hKos : ∀ c ∈ [a,b], ∀ i : ℤ, i < 0 → P ((unit (zs.map (· ^ c))).homology i)) (i : ℤ) :
    P.isoModSerre (homologyMap
      (complexQuotientπ (entryIdeal (zs.map (· ^ b))) F) i ≫
        factorThruImage (homologyMap
          ((complexQuotientMap (entryIdeal_power_antitone zs hab) (.up ℤ)).app F) i)) := by
  let f := homologyMap (powerMap F a b hab zs) i
  let g := homologyMap
    ((complexQuotientMap (entryIdeal_power_antitone zs hab) (.up ℤ)).app F) i
  let s : Arrow.mk f ⟶ Arrow.mk g := Arrow.homMk
    (homologyMap (quotientAugmentation F (zs.map (· ^ b))) i)
    (homologyMap (quotientAugmentation F (zs.map (· ^ a))) i) (by
      change _ ≫ g = f ≫ _
      dsimp only [f,g]
      rw [← homologyMap_comp, ← homologyMap_comp]
      exact congrArg (fun f => homologyMap f i)
        (quotientAugmentation_power_naturality F zs a b hab))
  have hs : P.isoModSerre (Limits.image.map s) := imageMap_isoModSerre P s
    (augmentation_finiteFree_bounded_isoMod P _ (hKos b (by simp)) F n h hsupp i)
    (augmentation_finiteFree_bounded_isoMod P _ (hKos a (by simp)) F n h hsupp i)
  have hi := koszul_stableImage_isIso F zs t a b H hta hab hgap i
  have hh : P.isoModSerre
      ((homologyMap (inclusion F (zs.map (· ^ b))) i ≫ factorThruImage f) ≫
        Limits.image.map s) := P.isoModSerre.comp_mem _ _ (P.isoModSerre_of_isIso _) hs
  have hm : factorThruImage f ≫ Limits.image.map s = s.left ≫ factorThruImage g :=
    Limits.image.factor_map s
  rw [Category.assoc, hm] at hh
  change P.isoModSerre (homologyMap (inclusion F (zs.map (· ^ b))) i ≫
    homologyMap (quotientAugmentation F (zs.map (· ^ b))) i ≫ factorThruImage g) at hh
  simpa only [← Category.assoc, ← homologyMap_comp, quotientAugmentation_inclusion] using hh

end Lech


namespace Lech
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
open Koszul
universe u
variable {R : Type u} [CommRing R]

lemma entryIdeal_ofFn {h : ℕ} (z : Fin h → R) :
    entryIdeal (List.ofFn z) = Ideal.span (Set.range z) := by
  unfold entryIdeal
  congr 1
  ext x
  exact List.mem_ofFn

lemma parameterPower_source_monoMod
    (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ j, Module.Free R (F.X j)] [∀ j, Module.Finite R (F.X j)]
    (n : ℤ) (d : ℕ) (hsupp : ∀ i, i < n ∨ n+d ≤ i → IsZero (F.X i))
    (zs : List R) (a : ℕ) (H : ∀ r ∈ zs, Homotopy (r^a • 𝟙 F) 0)
    (hKos : ∀ i : ℤ, i < 0 → P ((unit (zs.map (· ^ a))).homology i)) (i : ℤ) :
    P.monoModSerre (homologyMap
      (complexQuotientπ (entryIdeal (zs.map (· ^ a))) F) i) := by
  classical
  have : Mono (homologyMap (inclusion F (zs.map (· ^ a))) i) := by
    apply (ModuleCat.mono_iff_injective _).mpr
    apply inclusion_homology_injective
    intro x hx
    let e := List.mem_map.mp hx
    exact e.choose_spec.2 ▸ H e.choose e.choose_spec.1
  have ha := augmentation_finiteFree_bounded_isoMod P _ hKos F n d hsupp i
  rw [← quotientAugmentation_inclusion F (zs.map (· ^ a)), homologyMap_comp]
  exact P.monoModSerre.comp_mem _ _ (P.monoModSerre_of_mono _) ha.1

@[reassoc]
lemma complexQuotientMap_comp {I J K : Ideal R} (h : I ≤ J) (h' : J ≤ K)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    (complexQuotientMap h (.up ℤ)).app F ≫ (complexQuotientMap h' (.up ℤ)).app F =
      (complexQuotientMap (h.trans h') (.up ℤ)).app F := by
  ext i : 1
  exact moduleQuotientMap_comp h h' (F.X i)

 

lemma ordinaryPower_stableImage_isoMod
    (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ j, Module.Free R (F.X j)] [∀ j, Module.Finite R (F.X j)]
    (n : ℤ) (d : ℕ) (hsupp : ∀ i, i < n ∨ n+d ≤ i → IsZero (F.X i))
    (h : ℕ) (z : Fin h → R) (t : ℕ) (ht : 1 ≤ t)
    (H : ∀ j, Homotopy (z j ^ t • 𝟙 F) 0)
    (hKos : ∀ a : ℕ, 1 ≤ a → ∀ i : ℤ, i < 0 → P ((unit (List.ofFn fun j => z j ^ a)).homology i)) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∃ N₀ : ℕ, ∃ hMN₀ : M ≤ N₀,
      ∀ N : ℕ, ∀ hN : N₀ ≤ N, ∀ i : ℤ,
        P.isoModSerre (homologyMap
          (complexQuotientπ (Ideal.span (Set.range z) ^ N) F) i ≫
            factorThruImage (homologyMap
              ((complexQuotientMap (Ideal.pow_le_pow_right
                (hMN₀.trans hN))
                (.up ℤ)).app F) i)) := by
  classical
  let I := Ideal.span (Set.range z)
  let zs := List.ofFn z
  let J := fun a => entryIdeal (zs.map (· ^ a))
  have hJ (a : ℕ) : J a = Ideal.span (Set.range fun j => z j ^ a) := by
    simp only [zs, List.map_ofFn, Function.comp_def, entryIdeal_ofFn, J]
  have H' : ∀ r ∈ zs, Homotopy (r^t • 𝟙 F) 0 := by
    intro r hr
    let e := List.mem_ofFn.mp hr
    exact e.choose_spec ▸ H e.choose
  have hKos' (a : ℕ) (ha : 1 ≤ a) : ∀ i : ℤ, i < 0 → P ((unit (zs.map (· ^ a))).homology i) := by
    simpa only [zs, List.map_ofFn, Function.comp_def] using hKos a ha
  refine ⟨h*(t-1)+1, fun M hM => ?_⟩
  let a := max M t
  let b := a+h*t
  have hMa : M ≤ a := le_max_left _ _
  have hta : t ≤ a := le_max_right _ _
  have hab : a ≤ b := Nat.le_add_right _ _
  have hapos : 1 ≤ a := ht.trans hta
  have hbpos : 1 ≤ b := hapos.trans hab
  let N₀ := max M (h*(b-1)+1)
  have hMN₀ : M ≤ N₀ := le_max_left _ _
  refine ⟨N₀,hMN₀,fun N hN i => ?_⟩
  have hNM : M ≤ N := hMN₀.trans hN
  have hIMJ : I^M ≤ J t := by
    rw [hJ]
    exact (Ideal.pow_le_pow_right hM).trans (parameter_power_cofinality h t ht z).1
  have hINJ : I^N ≤ J b := by
    rw [hJ]
    exact (Ideal.pow_le_pow_right ((le_max_right M _).trans hN)).trans
      (parameter_power_cofinality h b hbpos z).1
  have hJIM : J a ≤ I^M := by
    rw [hJ]
    exact (parameter_power_cofinality h a hapos z).2.trans (Ideal.pow_le_pow_right hMa)
  have hJba : J b ≤ J a := entryIdeal_power_antitone zs hab
  have hmono : P.monoModSerre (homologyMap (complexQuotientπ (I^M) F) i) := by
    apply monoModSerre_of_comp P _
      (homologyMap ((complexQuotientMap hIMJ (.up ℤ)).app F) i)
    rw [← homologyMap_comp, complexQuotientπ_map]
    exact parameterPower_source_monoMod P F n d hsupp zs t H' (hKos' t ht) i
  have hstable : P.isoModSerre (homologyMap (complexQuotientπ (J b) F) i ≫
      factorThruImage (homologyMap ((complexQuotientMap hJba (.up ℤ)).app F) i)) := by
    have hx := parameterPower_stableImage_isoMod P F n d hsupp zs t a b H' hta hab
      (by simp only [zs, List.length_ofFn]; dsimp [b]; omega)
      (fun c hc => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact hKos' a hapos
        · exact hKos' b hbpos) i
    exact hx
  apply cofinal_stableImage_isoMod P
    (homologyMap (complexQuotientπ (I^N) F) i)
    (homologyMap (complexQuotientπ (I^M) F) i)
    (homologyMap (complexQuotientπ (J b) F) i)
    (homologyMap (complexQuotientπ (J a) F) i)
    (homologyMap ((complexQuotientMap (Ideal.pow_le_pow_right hNM) (.up ℤ)).app F) i)
    (homologyMap ((complexQuotientMap hINJ (.up ℤ)).app F) i)
    (homologyMap ((complexQuotientMap hJba (.up ℤ)).app F) i)
    (homologyMap ((complexQuotientMap hJIM (.up ℤ)).app F) i)
    (by rw [← homologyMap_comp, complexQuotientπ_map])
    (by rw [← homologyMap_comp, complexQuotientπ_map])
    (by rw [← homologyMap_comp, complexQuotientπ_map])
    ?_ hmono hstable
  rw [← homologyMap_comp, ← homologyMap_comp, complexQuotientMap_comp,
    complexQuotientMap_comp]

end Lech
end
end

end OAI
