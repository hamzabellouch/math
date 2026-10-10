import Mathlib

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech.FiniteComplex

section

variable {C : Type*} [Category C] [Abelian C]
variable (F : CochainComplex C ℤ) (n : ℤ)
  (hn : ∀ i, n < i → IsZero (F.X i))

noncomputable def topInclusion : (single C (ComplexShape.up ℤ) n).obj (F.X n) ⟶ F :=
  mkHomFromSingle (𝟙 _) (by
    intro i hi
    have hi' : n + 1 = i := hi
    exact (hn i (by omega)).eq_of_tgt _ _)

instance topInclusion_mono : Mono (topInclusion F n hn) := by
  apply mono_of_mono_f
  intro i
  by_cases hi : i = n
  · subst i
    dsimp [topInclusion]
    rw [mkHomFromSingle_f, Category.comp_id]
    infer_instance
  · exact (isZero_single_obj_X _ _ _ _ hi).mono _

noncomputable def dropTop : CochainComplex C ℤ := cokernel (topInclusion F n hn)

noncomputable def topShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (topInclusion F n hn) (cokernel.π _) (cokernel.condition _)

lemma topShortExact : (topShortComplex F n hn).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := topInclusion_mono F n hn
  epi_g := inferInstanceAs (Epi (cokernel.π (topInclusion F n hn)))

lemma topShortExact_eval (i : ℤ) :
    ((topShortComplex F n hn).map (eval C (ComplexShape.up ℤ) i)).ShortExact :=
  (topShortExact F n hn).map_of_exact _

lemma topInclusion_f_isIso : IsIso ((topInclusion F n hn).f n) := by
  dsimp [topInclusion]
  rw [mkHomFromSingle_f, Category.comp_id]
  infer_instance

lemma dropTop_X_top : IsZero ((dropTop F n hn).X n) := by
  apply (topShortExact_eval F n hn n).isIso_f_iff.mp
  exact topInclusion_f_isIso F n hn

lemma dropTop_π_isIso (i : ℤ) (hi : i ≠ n) :
    IsIso ((cokernel.π (topInclusion F n hn)).f i) := by
  apply (topShortExact_eval F n hn i).isIso_g_iff.mpr
  exact isZero_single_obj_X (ComplexShape.up ℤ) n (F.X n) i hi

noncomputable def dropTopXIso (i : ℤ) (hi : i ≠ n) :
    F.X i ≅ (dropTop F n hn).X i := by
  exact @asIso _ _ _ _ ((cokernel.π (topInclusion F n hn)).f i)
    (dropTop_π_isIso F n hn i hi)

noncomputable def topSplitting (i : ℤ) :
    ((topShortComplex F n hn).map (eval C (ComplexShape.up ℤ) i)).Splitting := by
  let S := (topShortComplex F n hn).map (eval C (ComplexShape.up ℤ) i)
  have hS : S.ShortExact := topShortExact_eval F n hn i
  by_cases hi : i = n
  · subst i
    haveI : IsIso S.f := topInclusion_f_isIso F n hn
    exact ShortComplex.Splitting.ofExactOfRetraction S hS.exact (inv S.f)
      (by simp) hS.epi_g
  · haveI : IsIso S.g := dropTop_π_isIso F n hn i hi
    exact ShortComplex.Splitting.ofExactOfSection S hS.exact (inv S.g)
      (by simp) hS.mono_f

omit hn in
lemma isZero_of_X (hF : ∀ i, IsZero (F.X i)) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext i
  exact (hF i).eq_of_src _ _


theorem devissage (Q : ObjectProperty (CochainComplex C ℤ))
    [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]
    (hQ : ∀ (S : ShortComplex (CochainComplex C ℤ)),
      (∀ i, (S.map (eval C (ComplexShape.up ℤ) i)).Splitting) →
      Q S.X₁ → Q S.X₃ → Q S.X₂)
    (m : ℤ) (N : ℕ) (F : CochainComplex C ℤ)
    (hb : ∀ i, i < m ∨ m + N ≤ i → IsZero (F.X i))
    (hg : ∀ i, Q ((single C (ComplexShape.up ℤ) i).obj (F.X i))) : Q F := by
  induction N generalizing F with
  | zero =>
    apply Q.prop_of_isZero
    exact isZero_of_X F (fun i => hb i (by omega))
  | succ N ih =>
    let n : ℤ := m + N
    have hn : ∀ i, n < i → IsZero (F.X i) := fun i hi => hb i (by
      right
      dsimp [n] at hi
      exact_mod_cast (by omega : m + ((N : ℤ) + 1) ≤ i))
    let D := dropTop F n hn
    have hbD : ∀ i, i < m ∨ m + (N : ℤ) ≤ i → IsZero (D.X i) := by
      intro i hi
      by_cases hin : i = n
      · subst i
        exact dropTop_X_top F n hn
      · exact (hb i (by dsimp [n] at hin; omega)).of_iso (dropTopXIso F n hn i hin).symm
    have hgD : ∀ i, Q ((single C (ComplexShape.up ℤ) i).obj (D.X i)) := by
      intro i
      by_cases hin : i = n
      · subst i
        exact Q.prop_of_isZero ((single C (ComplexShape.up ℤ) n).map_isZero
          (dropTop_X_top F n hn))
      · exact Q.prop_of_iso ((single C (ComplexShape.up ℤ) i).mapIso
          (dropTopXIso F n hn i hin)) (hg i)
    exact hQ (topShortComplex F n hn) (topSplitting F n hn) (hg n) (ih D hbD hgD)


theorem homology_devissage (P : ObjectProperty C) [P.IsSerreClass]
    (T : CochainComplex C ℤ ⥤ CochainComplex C ℤ) [T.Additive]
    (hT : ∀ (S : ShortComplex (CochainComplex C ℤ)),
      (∀ j, (S.map (eval C (ComplexShape.up ℤ) j)).Splitting) →
      ∀ j, ((S.map T).map (eval C (ComplexShape.up ℤ) j)).Splitting)
    (m : ℤ) (N : ℕ) (F : CochainComplex C ℤ) (i : ℤ)
    (hb : ∀ j, j < m ∨ m + N ≤ j → IsZero (F.X j))
    (hg : ∀ j, P ((T.obj ((single C (ComplexShape.up ℤ) j).obj
      (F.X j))).homology i)) : P ((T.obj F).homology i) := by
  let Q := P.inverseImage (T ⋙ homologyFunctor C (ComplexShape.up ℤ) i)
  apply devissage Q ?_ m N F hb hg
  intro S hs h₁ h₃
  have hS : (S.map T).ShortExact :=
    shortExact_of_degreewise_shortExact _ (fun j => (hT S hs j).shortExact)
  exact P.prop_X₂_of_exact (hS.homology_exact₂ i) h₁ h₃

end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
lemma homology_devissage_to (P : ObjectProperty D) [P.IsSerreClass]
    (T : CochainComplex C ℤ ⥤ CochainComplex D ℤ) [T.Additive]
    (hT : ∀ (S : ShortComplex (CochainComplex C ℤ)),
      (∀ j, (S.map (eval C (ComplexShape.up ℤ) j)).Splitting) →
      ∀ j, ((S.map T).map (eval D (ComplexShape.up ℤ) j)).Splitting)
    (m : ℤ) (N : ℕ) (F : CochainComplex C ℤ) (i : ℤ)
    (hb : ∀ j, j < m ∨ m + N ≤ j → IsZero (F.X j))
    (hg : ∀ j, P ((T.obj ((single C (ComplexShape.up ℤ) j).obj
      (F.X j))).homology i)) : P ((T.obj F).homology i) := by
  let Q := P.inverseImage (T ⋙ homologyFunctor D (ComplexShape.up ℤ) i)
  apply devissage Q ?_ m N F hb hg
  intro S hs h₁ h₃
  have hS : (S.map T).ShortExact :=
    shortExact_of_degreewise_shortExact _ (fun j => (hT S hs j).shortExact)
  exact P.prop_X₂_of_exact (hS.homology_exact₂ i) h₁ h₃
end Lech.FiniteComplex


namespace Lech.BicomplexTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
abbrev Row := CochainComplex (ModuleCat.{u} R) ℤ
abbrev Double := CochainComplex (Row (R := R)) ℤ
abbrev functor : Double (R := R) ⥤ Row (R := R) :=
  totalFunctor (ModuleCat.{u} R) (.up ℤ) (.up ℤ) (.up ℤ)
variable {F G H : Double (R := R)}
def degreeMap (a : ∀ j, F.X j ⟶ G.X j) (i : ℤ) :
    ((functor (R := R)).obj F).X i ⟶ ((functor (R := R)).obj G).X i :=
  totalDesc F (fun p q hpq => (a p).f q ≫ ιTotal G (.up ℤ) p q i hpq)
@[reassoc (attr := simp)] lemma ι_degreeMap (a : ∀ j, F.X j ⟶ G.X j)
    (p q i : ℤ) (hpq : p+q=i) :
    ιTotal F (.up ℤ) p q i hpq ≫ degreeMap a i =
      (a p).f q ≫ ιTotal G (.up ℤ) p q i hpq := by
  apply ι_totalDesc
lemma degreeMap_id (i : ℤ) : degreeMap (fun j => 𝟙 (F.X j)) i = 𝟙 _ := by
  apply total.hom_ext
  intro p q hpq
  change _ = ιTotal F (.up ℤ) p q i hpq ≫ 𝟙 ((total F (.up ℤ)).X i)
  simp
lemma degreeMap_comp (a : ∀ j, F.X j ⟶ G.X j) (b : ∀ j, G.X j ⟶ H.X j) (i : ℤ) :
    degreeMap (fun j => a j ≫ b j) i=degreeMap a i ≫ degreeMap b i := by
  apply total.hom_ext
  intro p q hpq
  exact (ι_degreeMap (fun j => a j ≫ b j) p q i hpq).trans
    ((Category.assoc _ _ _).trans
      ((congrArg ((a p).f q ≫ ·) (ι_degreeMap b p q i hpq).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ degreeMap b i) (ι_degreeMap a p q i hpq).symm).trans
            (Category.assoc _ _ _)))))
lemma degreeMap_add (a b : ∀ j, F.X j ⟶ G.X j) (i : ℤ) :
    degreeMap (fun j => a j+b j) i=degreeMap a i+degreeMap b i := by
  apply total.hom_ext
  intro p q hpq
  exact (ι_degreeMap (fun j => a j + b j) p q i hpq).trans
    ((Preadditive.add_comp _ _ _ _ _ _).trans
      ((congrArg₂ (· + ·) (ι_degreeMap a p q i hpq).symm
        (ι_degreeMap b p q i hpq).symm).trans (Preadditive.comp_add _ _ _ _ _ _).symm))
lemma map_f (f : F ⟶ G) (i : ℤ) :
    ((functor (R := R)).map f).f i=degreeMap f.f i := by
  apply total.hom_ext
  intro p q hpq
  exact (ιTotal_map F G f (.up ℤ) p q i hpq).trans (ι_degreeMap f.f p q i hpq).symm
instance : (functor (R := R)).Additive where
  map_add {F G} f g := by
    apply HomologicalComplex.Hom.ext
    funext i
    change ((functor (R := R)).map (f+g)).f i=((functor (R := R)).map f).f i+((functor (R := R)).map g).f i
    simp only [map_f]
    exact degreeMap_add f.f g.f i
 
def splitting (S : ShortComplex (Double (R := R)))
    (s : ∀ j, (S.map (eval (Row (R := R)) (.up ℤ) j)).Splitting) (i : ℤ) :
    ((S.map (functor (R := R))).map (eval (ModuleCat.{u} R) (.up ℤ) i)).Splitting where
  r := degreeMap (fun j => (s j).r) i
  s := degreeMap (fun j => (s j).s) i
  f_r := by
    change ((functor (R := R)).map S.f).f i ≫ degreeMap (fun j => (s j).r) i = 𝟙 _
    rw [map_f,←degreeMap_comp]
    simp only [show (fun j => S.f.f j ≫ (s j).r)=(fun j => 𝟙 (S.X₁.X j)) from
      funext (fun j => (s j).f_r),degreeMap_id]
  s_g := by
    change degreeMap (fun j => (s j).s) i ≫ ((functor (R := R)).map S.g).f i = 𝟙 _
    rw [map_f,←degreeMap_comp]
    simp only [show (fun j => (s j).s ≫ S.g.f j)=(fun j => 𝟙 (S.X₃.X j)) from
      funext (fun j => (s j).s_g),degreeMap_id]
  id := by
    change degreeMap (fun j => (s j).r) i ≫ ((functor (R := R)).map S.f).f i + ((functor (R := R)).map S.g).f i ≫ degreeMap (fun j => (s j).s) i = 𝟙 _
    rw [map_f,map_f,←degreeMap_comp,←degreeMap_comp,←degreeMap_add]
    simp only [show (fun j => (show S.X₂.X j ⟶ S.X₁.X j from (s j).r) ≫ S.f.f j + S.g.f j ≫ (show S.X₃.X j ⟶ S.X₂.X j from (s j).s))=
      (fun j => 𝟙 (S.X₂.X j)) from funext (fun j => (s j).id),degreeMap_id]
lemma devissage (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (m : ℤ) (N : ℕ) (F : Double (R := R)) (i : ℤ)
    (hb : ∀ j, j < m ∨ m + N ≤ j → IsZero (F.X j))
    (hg : ∀ j, P (((functor (R := R)).obj
      ((single (Row (R := R)) (.up ℤ) j).obj (F.X j))).homology i)) :
    P (((functor (R := R)).obj F).homology i) :=
  FiniteComplex.homology_devissage_to P functor splitting m N F i hb hg
end Lech.BicomplexTotal

open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
namespace Lech

section

section
universe u
variable {R : Type u} [CommRing R]

 
def powerTorsion (I : Ideal R) : ObjectProperty (ModuleCat.{u} R) :=
  fun M => ∃ n : ℕ, I ^ n ≤ Module.annihilator R M

lemma powerTorsion_zero (I : Ideal R) {M : ModuleCat.{u} R} (hM : IsZero M) :
    powerTorsion I M := by
  have := ModuleCat.isZero_iff_subsingleton.mp hM
  exact ⟨0, by simp [Module.annihilator_eq_top_iff.mpr ‹Subsingleton M›]⟩

lemma powerTorsion_mono (I : Ideal R) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) [Mono f] (hN : powerTorsion I N) : powerTorsion I M := by
  obtain ⟨n, hn⟩ := hN
  exact ⟨n, hn.trans (f.hom.annihilator_le_of_injective
    ((ModuleCat.mono_iff_injective f).mp inferInstance))⟩

lemma powerTorsion_epi (I : Ideal R) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) [Epi f] (hM : powerTorsion I M) : powerTorsion I N := by
  obtain ⟨n, hn⟩ := hM
  exact ⟨n, hn.trans (f.hom.annihilator_le_of_surjective
    ((ModuleCat.epi_iff_surjective f).mp inferInstance))⟩

lemma powerTorsion_extension (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.Exact) (h₁ : powerTorsion I S.X₁) (h₃ : powerTorsion I S.X₃) :
    powerTorsion I S.X₂ := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₃
  refine ⟨a + b, ?_⟩
  rw [pow_add, Ideal.mul_le]
  intro r hr s hs
  rw [Module.mem_annihilator]
  intro x
  have hx : S.g (s • x) = 0 := by
    rw [map_smul]
    exact Module.mem_annihilator.mp (hb hs) _
  obtain ⟨y, hy⟩ := (S.moduleCat_exact_iff.mp hS) _ hx
  rw [mul_smul, ← hy, ← map_smul, Module.mem_annihilator.mp (ha hr) y, map_zero]

instance powerTorsion_serre (I : Ideal R) : (powerTorsion I).IsSerreClass where
  exists_zero := ⟨0, isZero_zero _, powerTorsion_zero I (isZero_zero _)⟩
  prop_of_mono f _ h := powerTorsion_mono I f h
  prop_of_epi f _ h := powerTorsion_epi I f h
  prop_X₂_of_shortExact h h₁ h₃ := powerTorsion_extension I h.exact h₁ h₃


structure TorsionLength (I : Ideal R) where
  value : ModuleCat.{u} R → ℝ≥0∞
  zero : ∀ {M}, IsZero M → value M = 0
  additive : ∀ {S : ShortComplex (ModuleCat.{u} R)}, S.ShortExact →
    powerTorsion I S.X₂ → value S.X₂ = value S.X₁ + value S.X₃

namespace TorsionLength
variable {I : Ideal R} (ℓ : TorsionLength I)

lemma le_of_mono {M N : ModuleCat.{u} R} (f : M ⟶ N) [Mono f]
    (hN : powerTorsion I N) : ℓ.value M ≤ ℓ.value N := by
  have hS : (ShortComplex.cokernelSequence f).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact f
      mono_f := (inferInstance : Mono f) }
  have h := ℓ.additive hS hN
  exact h.symm ▸ le_add_right le_rfl

lemma le_of_epi {M N : ModuleCat.{u} R} (f : M ⟶ N) [Epi f]
    (hM : powerTorsion I M) : ℓ.value N ≤ ℓ.value M := by
  have hS : (ShortComplex.kernelSequence f).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact f
      epi_g := (inferInstance : Epi f) }
  have h := ℓ.additive hS hM
  exact h.symm ▸ le_add_left le_rfl

def zeroClass : ObjectProperty (ModuleCat.{u} R) :=
  fun M => powerTorsion I M ∧ ℓ.value M = 0

def finiteClass : ObjectProperty (ModuleCat.{u} R) :=
  fun M => powerTorsion I M ∧ ℓ.value M ≠ ⊤

instance zeroClass_serre : ℓ.zeroClass.IsSerreClass where
  exists_zero := ⟨0, isZero_zero _, powerTorsion_zero I (isZero_zero _),
    ℓ.zero (isZero_zero _)⟩
  prop_of_mono f _ h := ⟨powerTorsion_mono I f h.1,
    le_antisymm ((ℓ.le_of_mono f h.1).trans_eq h.2) bot_le⟩
  prop_of_epi f _ h := ⟨powerTorsion_epi I f h.1,
    le_antisymm ((ℓ.le_of_epi f h.1).trans_eq h.2) bot_le⟩
  prop_X₂_of_shortExact h h₁ h₃ := by
    have h₂ := powerTorsion_extension I h.exact h₁.1 h₃.1
    exact ⟨h₂, by rw [ℓ.additive h h₂, h₁.2, h₃.2, zero_add]⟩

instance finiteClass_serre : ℓ.finiteClass.IsSerreClass where
  exists_zero := ⟨0, isZero_zero _, powerTorsion_zero I (isZero_zero _),
    by rw [ℓ.zero (isZero_zero _)]; exact ENNReal.zero_ne_top⟩
  prop_of_mono f _ h := ⟨powerTorsion_mono I f h.1,
    ne_top_of_le_ne_top h.2 (ℓ.le_of_mono f h.1)⟩
  prop_of_epi f _ h := ⟨powerTorsion_epi I f h.1,
    ne_top_of_le_ne_top h.2 (ℓ.le_of_epi f h.1)⟩
  prop_X₂_of_shortExact h h₁ h₃ := by
    have h₂ := powerTorsion_extension I h.exact h₁.1 h₃.1
    exact ⟨h₂, by rw [ℓ.additive h h₂]; exact ENNReal.add_ne_top.mpr ⟨h₁.2, h₃.2⟩⟩

end TorsionLength
end


universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]


lemma imageMap_isoModSerre (P : ObjectProperty C) [P.IsSerreClass]
    {f g : Arrow C} (φ : f ⟶ g)
    (h₁ : P.isoModSerre φ.left) (h₂ : P.isoModSerre φ.right) :
    P.isoModSerre (image.map φ) := by
  constructor
  · have h := P.monoModSerre.comp_mem (image.ι f.hom) φ.right
      (P.monoModSerre_of_mono _) h₂.1
    rw [← image.map_ι φ] at h
    exact P.prop_of_mono
      (kernel.map (image.map φ) (image.map φ ≫ image.ι g.hom)
        (𝟙 _) (image.ι g.hom) (by simp)) h
  · have h := P.epiModSerre.comp_mem φ.left (factorThruImage g.hom)
      h₁.2 (P.epiModSerre_of_epi _)
    rw [← image.factor_map φ] at h
    exact P.prop_of_epi
      (cokernel.map (factorThruImage f.hom ≫ image.map φ) (image.map φ)
        (factorThruImage f.hom) (𝟙 _) (by simp)) h

variable {R : Type u} [CommRing R] {I : Ideal R}
namespace TorsionLength
variable (ℓ : TorsionLength I)

lemma eq_of_iso {M N : ModuleCat.{u} R} (e : M ≅ N)
    (hM : powerTorsion I M) (hN : powerTorsion I N) : ℓ.value M = ℓ.value N :=
  le_antisymm (ℓ.le_of_mono e.hom hN) (ℓ.le_of_mono e.inv hM)

lemma eq_of_isoModSerre {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hM : powerTorsion I M) (hN : powerTorsion I N)
    (hf : ℓ.zeroClass.isoModSerre f) : ℓ.value M = ℓ.value N := by
  have h₁ : (ShortComplex.kernelSequence (Abelian.factorThruImage f)).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact _
      epi_g := (inferInstance : Epi (Abelian.factorThruImage f)) }
  have h₂ : (ShortComplex.cokernelSequence (Abelian.image.ι f)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := (inferInstance : Mono (Abelian.image.ι f)) }
  have e₁ := ℓ.additive h₁ hM
  have e₂ := ℓ.additive h₂ hN
  have hker := hf.1.isoModSerre_factorThruImage.1.2
  have hcoker := hf.2.isoModSerre_image_ι.2.2
  dsimp only [ShortComplex.kernelSequence, ShortComplex.cokernelSequence] at e₁ e₂
  rw [hker, zero_add] at e₁
  rw [hcoker, add_zero] at e₂
  exact e₁.trans e₂.symm

lemma image_value_eq {f g : Arrow (ModuleCat.{u} R)} (φ : f ⟶ g)
    (h₁ : ℓ.zeroClass.isoModSerre φ.left) (h₂ : ℓ.zeroClass.isoModSerre φ.right)
    (hMf : powerTorsion I f.right) (hMg : powerTorsion I g.right) :
    ℓ.value (image f.hom) = ℓ.value (image g.hom) :=
  ℓ.eq_of_isoModSerre (image.map φ)
    (powerTorsion_mono I (image.ι f.hom) hMf)
    (powerTorsion_mono I (image.ι g.hom) hMg)
    (imageMap_isoModSerre ℓ.zeroClass φ h₁ h₂)

end TorsionLength
end


universe u
variable {R : Type u} [CommRing R] {I : Ideal R}

lemma powerTorsion_prod {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (hM : powerTorsion I (ModuleCat.of R M)) (hN : powerTorsion I (ModuleCat.of R N)) :
    powerTorsion I (ModuleCat.of R (M × N)) := by
  obtain ⟨a, ha⟩ := hM
  obtain ⟨b, hb⟩ := hN
  refine ⟨max a b, ?_⟩
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  ext
  · exact Module.mem_annihilator.mp (ha (Ideal.pow_le_pow_right (le_max_left a b) hr)) x.1
  · exact Module.mem_annihilator.mp (hb (Ideal.pow_le_pow_right (le_max_right a b) hr)) x.2

lemma powerTorsion_pi {M : Type u} [AddCommGroup M] [Module R M] (ι : Type u)
    (hM : powerTorsion I (ModuleCat.of R M)) :
    powerTorsion I (ModuleCat.of R (ι → M)) := by
  obtain ⟨a, ha⟩ := hM
  refine ⟨a, ?_⟩
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  ext i
  exact Module.mem_annihilator.mp (ha hr) (x i)

lemma powerTorsion_fin {M : Type u} [AddCommGroup M] [Module R M] (n : ℕ)
    (hM : powerTorsion I (ModuleCat.of R M)) :
    powerTorsion I (ModuleCat.of R (Fin n → M)) := by
  obtain ⟨a, ha⟩ := hM
  refine ⟨a, ?_⟩
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  ext i
  exact Module.mem_annihilator.mp (ha hr) (x i)

namespace TorsionLength
variable (ℓ : TorsionLength I)

lemma additive_linear {M N P : Type u} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hf : Function.Injective f)
    (hg : Function.Surjective g) (he : Function.Exact f g)
    (ht : powerTorsion I (ModuleCat.of R N)) :
    ℓ.value (ModuleCat.of R N) =
      ℓ.value (ModuleCat.of R M) + ℓ.value (ModuleCat.of R P) := by
  let S := ShortComplex.moduleCatMk f g (LinearMap.range_le_ker_iff.mp
    ((LinearMap.exact_iff.mp he).symm.le))
  have hS : S.ShortExact :=
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr he
      mono_f := (ModuleCat.mono_iff_injective _).mpr hf
      epi_g := (ModuleCat.epi_iff_surjective _).mpr hg }
  exact ℓ.additive hS ht

lemma value_prod {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (hM : powerTorsion I (ModuleCat.of R M)) (hN : powerTorsion I (ModuleCat.of R N)) :
    ℓ.value (ModuleCat.of R (M × N)) =
      ℓ.value (ModuleCat.of R M) + ℓ.value (ModuleCat.of R N) := by
  apply ℓ.additive_linear (LinearMap.inl R M N) (LinearMap.snd R M N)
  · intro x y h
    exact congrArg Prod.fst h
  · intro n
    exact ⟨(0, n), rfl⟩
  · intro ⟨m, n⟩
    simp only [LinearMap.snd_apply]
    constructor
    · intro hn
      exact ⟨m, by simp [hn]⟩
    · rintro ⟨x, hx⟩
      exact (congrArg Prod.snd hx).symm
  · exact powerTorsion_prod hM hN

lemma value_linearEquiv {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N)
    (hN : powerTorsion I (ModuleCat.of R N)) :
    ℓ.value (ModuleCat.of R M) = ℓ.value (ModuleCat.of R N) := by
  let e' := e.toModuleIso
  exact ℓ.eq_of_iso e' ((powerTorsion I).prop_of_iso e'.symm hN) hN

lemma value_fin {M : Type u} [AddCommGroup M] [Module R M]
    (hM : powerTorsion I (ModuleCat.of R M)) (n : ℕ) :
    ℓ.value (ModuleCat.of R (Fin n → M)) = n • ℓ.value (ModuleCat.of R M) := by
  induction n with
  | zero =>
    rw [ℓ.zero (ModuleCat.isZero_iff_subsingleton.mpr inferInstance), zero_nsmul]
  | succ n ih =>
    let e : (Fin (n + 1) → M) ≃ₗ[R] M × (Fin n → M) :=
      (LinearEquiv.piCongrLeft R (fun _ : Option (Fin n) => M) (finSuccEquiv n)) ≪≫ₗ
        LinearEquiv.piOptionEquivProd R
    rw [ℓ.value_linearEquiv e (powerTorsion_prod hM (powerTorsion_fin _ hM)),
      ℓ.value_prod hM (powerTorsion_fin _ hM), ih, succ_nsmul, add_comm]

lemma value_fintype {M : Type u} [AddCommGroup M] [Module R M]
    (hM : powerTorsion I (ModuleCat.of R M)) (ι : Type u) [Fintype ι] :
    ℓ.value (ModuleCat.of R (ι → M)) = Fintype.card ι • ℓ.value (ModuleCat.of R M) := by
  classical
  let e : (ι → M) ≃ₗ[R] (Fin (Fintype.card ι) → M) :=
    LinearEquiv.piCongrLeft R (fun _ => M) (Fintype.equivFin ι)
  exact (ℓ.value_linearEquiv e (powerTorsion_fin _ hM)).trans (ℓ.value_fin hM _)

end TorsionLength
end Lech

end

end OAI
