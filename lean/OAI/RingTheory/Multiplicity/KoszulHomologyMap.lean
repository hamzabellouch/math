import Mathlib
import OAI.RingTheory.Multiplicity.SourceGradedThickeningNat

namespace OAI

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
namespace Lech.Koszul
universe u
variable {R : Type u} [CommRing R]

@[simp] lemma homologyMap_smul {C : Type*} [Category C] [Preadditive C]
    [CategoryTheory.Linear R C] {F G : CochainComplex C ℤ}
    (f : F ⟶ G) (a : R) (i : ℤ) [F.HasHomology i] [G.HasHomology i] :
    homologyMap (a • f) i = a • homologyMap f i := by
  exact ShortComplex.homologyMap_smul ((shortComplexFunctor C (ComplexShape.up ℤ) i).map f) a

lemma scalar_annihilates_homology (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (a : R) (ha : Homotopy (a • 𝟙 F) 0) (i : ℤ) :
    a ∈ Module.annihilator R (F.homology i) := by
  rw [Module.mem_annihilator]
  have h : a • 𝟙 (F.homology i) = 0 := by simpa using ha.homologyMap_eq i
  intro m
  exact congrArg (fun f : F.homology i ⟶ F.homology i => f m) h

def entryIdeal (zs : List R) : Ideal R := Ideal.span {x | x ∈ zs}

lemma tensor_homology_annihilator (zs : List R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    entryIdeal zs ≤ Module.annihilator R ((tensor zs F).homology i) := by
  apply Ideal.span_le.mpr
  intro a ha
  obtain ⟨h⟩ := tensor_entry_nullhomotopic zs F a ha
  exact scalar_annihilates_homology _ _ h _

lemma tensor_homology_torsion (zs : List R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    powerTorsion (entryIdeal zs) ((tensor zs F).homology i) :=
  ⟨1, by simpa using tensor_homology_annihilator zs F i⟩

variable {C : Type*} [Category C] [Abelian C] [CategoryTheory.Linear R C]

lemma tensor_bounded (zs : List R) (F : CochainComplex C ℤ) (m n : ℤ)
    (hF : ∀ i, i < m ∨ n < i → IsZero (F.X i)) :
    ∀ i, i < m - zs.length ∨ n < i → IsZero ((tensor zs F).X i) := by
  induction zs with
  | nil => simpa using hF
  | cons a zs ih =>
    intro i hi
    rw [tensor_cons, mappingCone.isZero_X_iff]
    constructor <;> apply ih <;> simp only [List.length_cons, Nat.cast_add,
      Nat.cast_one] at hi <;> omega

noncomputable def unit (zs : List R) : CochainComplex (ModuleCat.{u} R) ℤ :=
  tensor zs ((singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R))

lemma unit_bounded (zs : List R) (i : ℤ) (hi : i < -(zs.length : ℤ) ∨ 0 < i) :
    IsZero ((unit zs).X i) := by
  apply tensor_bounded zs ((singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)) 0 0
    (fun j hj => isZero_single_obj_X (ComplexShape.up ℤ) 0 _ j (by omega)) i
  simpa using hi

lemma unit_homology_zero (zs : List R) (i : ℤ)
    (hi : i < -(zs.length : ℤ) ∨ 0 < i) : IsZero ((unit zs).homology i) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (unit_bounded zs i hi)

variable {F G : CochainComplex C ℤ}

 
lemma cone_homology_exact (f : F ⟶ G) (i : ℤ) :
    (ShortComplex.mk (homologyMap f i) (homologyMap (mappingCone.inr f) i)
      (by rw [← homologyMap_comp]
          change homologyMap (f ≫ homotopyCofiber.inr f) i = 0
          simpa only [homologyMap_zero] using
        (homotopyCofiber.inrCompHomotopy f
          (fun j => ⟨j - 1, by change j - 1 + 1 = j; omega⟩)).homologyMap_eq i)).Exact := by
  let e := HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i
  let Q := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i
  have h := Q.map_distinguished_exact _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)
  refine ShortComplex.exact_of_iso ?_ h
  exact ShortComplex.isoMk (e.app F) (e.app G) (e.app (mappingCone f))
    (e.hom.naturality f).symm (e.hom.naturality (mappingCone.inr f)).symm

lemma cone_homology_inr_epi (f : F ⟶ G) (i : ℤ)
    (hF : IsZero (F.homology (i + 1))) : Epi (homologyMap (mappingCone.inr f) i) := by
  let e := HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i
  let Q := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i
  let T := mappingCone.triangleh f
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished f
  let e' : Q.obj (T.obj₁⟦(1 : ℤ)⟧) ≅ F.homology (i + 1) :=
    ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso 1 i
        (i + 1) (by omega)).app T.obj₁ ≪≫
      (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) (i + 1)).app F
  have hz : IsZero (Q.obj (T.obj₁⟦(1 : ℤ)⟧)) := hF.of_iso e'
  have hex := Q.map_distinguished_exact T.rotate (CategoryTheory.Pretriangulated.rot_of_distTriang T hT)
  have : Epi (Q.map T.mor₂) := hex.epi_f_iff.mpr (hz.eq_of_tgt _ _)
  have : Epi (e.hom.app G ≫ homologyMap (mappingCone.inr f) i) := by
    change Epi (e.hom.app G ≫ (homologyFunctor C (ComplexShape.up ℤ) i).map
      (mappingCone.inr f))
    rw [← e.hom.naturality (mappingCone.inr f)]
    change Epi (Q.map T.mor₂ ≫ (e.app (mappingCone f)).hom)
    exact epi_comp' (inferInstanceAs (Epi (Q.map T.mor₂)))
      (inferInstanceAs (Epi (e.app (mappingCone f)).hom))
  exact epi_of_epi (e.hom.app G) _

 

noncomputable def unitHomologyGenerator (zs : List R) :
    ModuleCat.of R R ⟶ (unit zs).homology 0 := by
  induction zs with
  | nil => exact (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).inv
  | cons a zs ih => exact ih ≫ homologyMap (mappingCone.inr (a • 𝟙 (unit zs))) 0

instance unitHomologyGenerator_epi (zs : List R) : Epi (unitHomologyGenerator zs) := by
  induction zs with
  | nil =>
    change Epi (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).inv
    infer_instance
  | cons a zs ih =>
    have := cone_homology_inr_epi (a • 𝟙 (unit zs)) 0
      (unit_homology_zero zs 1 (Or.inr (by omega)))
    change Epi (unitHomologyGenerator zs ≫ homologyMap
      (mappingCone.inr (a • 𝟙 (unit zs))) 0)
    infer_instance

noncomputable def unitHomologyQuotient (zs : List R) :
    ModuleCat.of R (R ⧸ entryIdeal zs) ⟶ (unit zs).homology 0 :=
  ModuleCat.ofHom ((entryIdeal zs).liftQ (unitHomologyGenerator zs).hom (by
    intro x hx
    change unitHomologyGenerator zs x = 0
    rw [show x = x • (1 : R) by simp, map_smul]
    exact Module.mem_annihilator.mp (tensor_homology_annihilator zs _ 0 hx) _))

instance unitHomologyQuotient_epi (zs : List R) : Epi (unitHomologyQuotient zs) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro x
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (unitHomologyGenerator zs)).mp
    inferInstance x
  exact ⟨Submodule.Quotient.mk y, rfl⟩

end Lech.Koszul


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex
universe u v
variable {R : Type u} [CommRing R]

 
noncomputable def inclusion (F : CochainComplex (ModuleCat.{v} R) ℤ) :
    (zs : List R) → F ⟶ tensor zs F
  | [] => 𝟙 F
  | r :: zs => inclusion F zs ≫ mappingCone.inr (r • 𝟙 _)

noncomputable def retraction (F : CochainComplex (ModuleCat.{v} R) ℤ) :
    (zs : List R) → (∀ r ∈ zs, Homotopy (r • 𝟙 F) 0) → (tensor zs F ⟶ F)
  | [], _ => 𝟙 F
  | r :: zs, H => coneRetraction
      (tensorScalarHomotopy r zs (H r (by simp))) ≫
        retraction F zs (fun s hs => H s (by simp [hs]))

@[reassoc (attr := simp)]
lemma inclusion_retraction (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (zs : List R) (H : ∀ r ∈ zs, Homotopy (r • 𝟙 F) 0) :
    inclusion F zs ≫ retraction F zs H = 𝟙 F := by
  induction zs with
  | nil => simp [inclusion, retraction]
  | cons r zs ih =>
    change (inclusion F zs ≫ mappingCone.inr (r • 𝟙 (tensor zs F))) ≫
      (coneRetraction (tensorScalarHomotopy r zs (H r (by simp))) ≫
        retraction F zs (fun s hs => H s (by simp [hs]))) = 𝟙 F
    rw [Category.assoc, ← Category.assoc (mappingCone.inr _),
      inr_coneRetraction, Category.id_comp]
    exact ih _

lemma inclusion_homology_injective
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (zs : List R) (H : ∀ r ∈ zs, Homotopy (r • 𝟙 F) 0) (i : ℤ) :
    Function.Injective (HomologicalComplex.homologyMap (inclusion F zs) i) := by
  have he := congrArg (fun f => HomologicalComplex.homologyMap f i)
    (inclusion_retraction F zs H)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] at he
  intro x y hxy
  have hx := congrArg (fun f => f x) he
  have hy := congrArg (fun f => f y) he
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hx hy
  rw [← hx, ← hy, hxy]

 
noncomputable def powerMap (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (a b : ℕ) (hab : a ≤ b) :
    (zs : List R) → tensor (zs.map (· ^ b)) F ⟶ tensor (zs.map (· ^ a)) F
  | [] => 𝟙 F
  | r :: zs => mappingCone.map
      (r ^ b • 𝟙 (tensor (zs.map (· ^ b)) F))
      (r ^ a • 𝟙 (tensor (zs.map (· ^ a)) F))
      (r ^ (b-a) • powerMap F a b hab zs) (powerMap F a b hab zs) (by
        simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
          Category.comp_id, smul_smul]
        rw [← pow_add, Nat.add_sub_of_le hab])

@[reassoc (attr := simp)]
lemma powerMap_inclusion (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (a b : ℕ) (hab : a ≤ b) (zs : List R) :
    inclusion F (zs.map (· ^ b)) ≫ powerMap F a b hab zs =
      inclusion F (zs.map (· ^ a)) := by
  induction zs with
  | nil => exact Category.id_comp _
  | cons r zs ih =>
    change (inclusion F (zs.map (· ^ b)) ≫ mappingCone.inr _) ≫
      mappingCone.map _ _ _ _ _ = inclusion F (zs.map (· ^ a)) ≫ mappingCone.inr _
    simp only [Category.assoc, mappingCone.map, mappingCone.inr_desc]
    exact congrArg (fun f => f ≫ mappingCone.inr _) ih

lemma powerMap_refl (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (a : ℕ) (zs : List R) : powerMap F a a le_rfl zs = 𝟙 _ := by
  induction zs with
  | nil => rfl
  | cons r zs ih =>
    simp only [powerMap, Nat.sub_self, pow_zero, one_smul, ih]
    exact mappingCone.map_id _

lemma powerMap_comp (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) (zs : List R) :
    powerMap F a c (hab.trans hbc) zs =
      powerMap F b c hbc zs ≫ powerMap F a b hab zs := by
  induction zs with
  | nil => exact (Category.id_comp _).symm
  | cons r zs ih =>
    have hc := mappingCone.map_comp
      (r^c • 𝟙 (tensor (zs.map (· ^ c)) F))
      (r^b • 𝟙 (tensor (zs.map (· ^ b)) F))
      (r^a • 𝟙 (tensor (zs.map (· ^ a)) F))
      (r^(c-b) • powerMap F b c hbc zs) (powerMap F b c hbc zs)
      (by simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
            Category.comp_id, smul_smul]
          rw [← pow_add, Nat.add_sub_of_le hbc])
      (r^(b-a) • powerMap F a b hab zs) (powerMap F a b hab zs)
      (by simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
            Category.comp_id, smul_smul]
          rw [← pow_add, Nat.add_sub_of_le hab])
    refine Eq.trans ?_ hc
    simp only [Linear.smul_comp, Linear.comp_smul, smul_smul,
      ← pow_add, show b-a+(c-b) = c-a by omega, ← ih]
    rfl




noncomputable def coneFst (F G : CochainComplex (ModuleCat.{v} R) ℤ) (f : F ⟶ G) :
    mappingCone f ⟶ F⟦(1 : ℤ)⟧ where
  f i := (mappingCone.fst f).1.v i (i + 1) rfl
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    subst j
    simp [mappingCone.d_fst_v _ i (i + 1) (i + 1 + 1) rfl rfl]

lemma homology_middle_range_le {ι : Type*} {c : ComplexShape ι} {S T : ShortComplex (HomologicalComplex (ModuleCat.{v} R) c)}
    (f : S ⟶ T) (hT : T.ShortExact) (i : ι)
    (hzero : HomologicalComplex.homologyMap f.τ₃ i = 0) :
    LinearMap.range (HomologicalComplex.homologyMap f.τ₂ i).hom ≤
      LinearMap.range (HomologicalComplex.homologyMap T.f i).hom := by
  rw [(hT.homology_exact₂ i).moduleCat_range_eq_ker]
  rintro _ ⟨x,rfl⟩
  have he : HomologicalComplex.homologyMap f.τ₂ i ≫
      HomologicalComplex.homologyMap T.g i = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, f.comm₂₃,
      HomologicalComplex.homologyMap_comp, hzero, comp_zero]
  exact congrArg (fun a => a x) he

noncomputable def coneShortComplex {F G : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ G) : ShortComplex (CochainComplex (ModuleCat.{v} R) ℤ) :=
  ShortComplex.mk (mappingCone.inr f) (coneFst F G f) (by
    ext i : 1
    simp [coneFst])

lemma coneShortComplex_shortExact {F G : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ G) : (coneShortComplex f).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  let s : ((coneShortComplex f).map
      (HomologicalComplex.eval (ModuleCat.{v} R) (.up ℤ) i)).Splitting :=
    { r := (mappingCone.snd f).v i i (by omega)
      s := (mappingCone.inl f).v (i+1) i (by omega)
      f_r := by
        change (mappingCone.inr f).f i ≫ (mappingCone.snd f).v i i _ = 𝟙 (G.X i)
        simp
      s_g := by
        change (mappingCone.inl f).v (i+1) i _ ≫ (mappingCone.fst f).1.v i (i+1) _ = 𝟙 (F.X (i+1))
        simp
      id := by
        change (mappingCone.snd f).v i i (by omega) ≫ (mappingCone.inr f).f i +
          (mappingCone.fst f).1.v i (i+1) rfl ≫ (mappingCone.inl f).v (i+1) i (by omega) =
            𝟙 ((mappingCone f).X i)
        exact (add_comm _ _).trans (mappingCone.id_X f i (i+1) rfl) }
  exact s.shortExact

noncomputable def coneShortComplexMap
    {F G F' G' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ G) (f' : F' ⟶ G') (a : F ⟶ F') (b : G ⟶ G')
    (h : f ≫ b = a ≫ f') : coneShortComplex f ⟶ coneShortComplex f' where
  τ₁ := b
  τ₂ := mappingCone.map f f' a b h
  τ₃ := (CategoryTheory.shiftFunctor _ (1 : ℤ)).map a
  comm₁₂ := by ext i : 1; simp [coneShortComplex, mappingCone.map]
  comm₂₃ := by
    ext i : 1
    apply (mappingCone.ext_from_iff _ (i+1) i rfl _ _).mpr
    constructor <;> simp [coneShortComplex, coneFst, mappingCone.map]

noncomputable def scalarPowerHomotopy
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (r : R) (t d : ℕ) (htd : t ≤ d)
    (H : Homotopy (r^t • 𝟙 F) 0) : Homotopy (r^d • 𝟙 F) 0 := by
  simpa only [smul_zero, smul_smul, ← pow_add, Nat.sub_add_cancel htd] using H.smul (r^(d-t))

 

lemma powerMap_range_le_inr
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (r : R) (zs : List R)
    (a b t : ℕ) (hab : a ≤ b) (ht : t ≤ b-a)
    (H : Homotopy (r^t • 𝟙 F) 0) (i : ℤ) :
    LinearMap.range (HomologicalComplex.homologyMap (powerMap F a b hab (r::zs)) i).hom ≤
      LinearMap.range (HomologicalComplex.homologyMap
        (mappingCone.inr (r^a • 𝟙 (tensor (zs.map (· ^ a)) F)) ) i).hom := by
  let f := powerMap F a b hab zs
  let H' := tensorScalarHomotopy (r^t) (zs.map (· ^ b)) H
  let H'' := (scalarPowerHomotopy _ r t (b-a) ht H').compRight f
  let φ := coneShortComplexMap (r^b • 𝟙 _) (r^a • 𝟙 _)
    (r^(b-a) • f) f (by
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
        Category.comp_id, smul_smul]
      rw [← pow_add, Nat.add_sub_of_le hab])
  have hz : HomologicalComplex.homologyMap φ.τ₃ i = 0 := by
    have HH : Homotopy (r^(b-a) • f) 0 := by
      simpa only [Linear.smul_comp, Category.id_comp, zero_comp] using H''
    have he := (HH.shift (1 : ℤ)).homologyMap_eq i
    simp only [φ, coneShortComplexMap]
    change HomologicalComplex.homologyMap
      ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{v} R) ℤ) (1 : ℤ)).map
        (r^(b-a) • f)) i = 0
    simpa only [Functor.map_zero, HomologicalComplex.homologyMap_zero] using he
  apply homology_middle_range_le φ (coneShortComplex_shortExact _) i hz

 

lemma powerMap_range_eq
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (zs : List R) (t : ℕ)
    (H : ∀ r ∈ zs, Homotopy (r^t • 𝟙 F) 0)
    (a b : ℕ) (hab : a ≤ b) (hgap : zs.length * t ≤ b-a) (i : ℤ) :
    LinearMap.range (HomologicalComplex.homologyMap (powerMap F a b hab zs) i).hom =
      LinearMap.range (HomologicalComplex.homologyMap
        (inclusion F (zs.map (· ^ a))) i).hom := by
  induction zs generalizing a b with
  | nil => rfl
  | cons r zs ih =>
    let m := a + zs.length * t
    have ham : a ≤ m := by omega
    have hmb : m ≤ b := by simp only [List.length_cons, Nat.add_mul, one_mul] at hgap; dsimp [m]; omega
    have htm : t ≤ b-m := by simp only [List.length_cons, Nat.add_mul, one_mul] at hgap; dsimp [m]; omega
    apply le_antisymm
    · rintro _ ⟨x,rfl⟩
      have hx := powerMap_range_le_inr F r zs m b t hmb htm (H r (by simp)) i
        (show _ ∈ LinearMap.range
          (HomologicalComplex.homologyMap (powerMap F m b hmb (r::zs)) i).hom from ⟨x,rfl⟩)
      obtain ⟨y,hy⟩ := hx
      have hinner := ih (fun s hs => H s (by simp [hs])) a m ham (by dsimp [m]; omega)
      have hy' := hinner ▸ (show _ ∈ LinearMap.range
          (HomologicalComplex.homologyMap (powerMap F a m ham zs) i).hom from ⟨y,rfl⟩)
      obtain ⟨z,hz⟩ := hy'
      refine ⟨z, ?_⟩
      have hc := congrArg (fun f => HomologicalComplex.homologyMap f i)
        (powerMap_comp F a m b ham hmb (r::zs))
      have hn : mappingCone.inr (r^m • 𝟙 (tensor (zs.map (· ^ m)) F)) ≫
          powerMap F a m ham (r::zs) =
          powerMap F a m ham zs ≫ mappingCone.inr (r^a • 𝟙 (tensor (zs.map (· ^ a)) F)) := by
        change mappingCone.inr _ ≫ mappingCone.map _ _ _ _ _ = _
        simp [mappingCone.map]
      have hn' := congrArg (fun f => HomologicalComplex.homologyMap f i) hn
      simp only [HomologicalComplex.homologyMap_comp] at hc
      change (HomologicalComplex.homologyMap
        (inclusion F (zs.map (· ^ a)) ≫ mappingCone.inr _) i).hom z = _
      rw [HomologicalComplex.homologyMap_comp]
      change (HomologicalComplex.homologyMap
        (mappingCone.inr (r^a • 𝟙 (tensor (zs.map (· ^ a)) F))) i).hom
        ((HomologicalComplex.homologyMap (inclusion F (zs.map (· ^ a))) i).hom z) = _
      rw [hz, hc]
      change _ = (HomologicalComplex.homologyMap (powerMap F a m ham (r::zs)) i)
        ((HomologicalComplex.homologyMap (powerMap F m b hmb (r::zs)) i) x)
      rw [← hy]
      exact (congrArg (fun f => f y) (HomologicalComplex.homologyMap_comp
        (powerMap F a m ham zs)
        (mappingCone.inr (r^a • 𝟙 (tensor (zs.map (· ^ a)) F))) i)).symm.trans
          ((congrArg (fun f => f y) hn').symm.trans
            (congrArg (fun f => f y) (HomologicalComplex.homologyMap_comp
              (mappingCone.inr (r^m • 𝟙 (tensor (zs.map (· ^ m)) F)))
              (powerMap F a m ham (r::zs)) i)))
    · rintro _ ⟨x,rfl⟩
      refine ⟨(HomologicalComplex.homologyMap
        (inclusion F ((r::zs).map (· ^ b))) i) x, ?_⟩
      have he := congrArg (fun f => HomologicalComplex.homologyMap f i)
        (powerMap_inclusion F a b hab (r::zs))
      simpa only [HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply] using
        congrArg (fun f => f x) he




lemma scalar_comp_zero {F G : CochainComplex (ModuleCat.{v} R) ℤ}
    (r : R) (f : F ⟶ G) (h : r • 𝟙 G = 0) : (r • 𝟙 F) ≫ f = 0 := by
  calc (r • 𝟙 F) ≫ f = f ≫ (r • 𝟙 G) := by simp
       _ = 0 := by rw [h, comp_zero]

 
noncomputable def augmentation {F G : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ G) : (zs : List R) → (∀ r ∈ zs, r • 𝟙 G = 0) → (tensor zs F ⟶ G)
  | [], _ => f
  | r :: zs, H => mappingCone.desc (r • 𝟙 (tensor zs F)) 0
      (augmentation f zs (fun s hs => H s (by simp [hs])))
      (by rw [scalar_comp_zero r _ (H r (by simp))]; simp)

@[reassoc (attr := simp)]
lemma inclusion_augmentation {F G : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ G) (zs : List R) (H : ∀ r ∈ zs, r • 𝟙 G = 0) :
    inclusion F zs ≫ augmentation f zs H = f := by
  induction zs with
  | nil => exact Category.id_comp _
  | cons r zs ih =>
    change (inclusion F zs ≫ mappingCone.inr (r • 𝟙 (tensor zs F))) ≫
      mappingCone.desc (r • 𝟙 (tensor zs F)) 0 _ _ = f
    simpa only [Category.assoc, mappingCone.inr_desc] using ih _

@[reassoc]
lemma augmentation_naturality_target
    {F G G' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ G) (g : G ⟶ G') (zs : List R)
    (H : ∀ r ∈ zs, r • 𝟙 G = 0) (H' : ∀ r ∈ zs, r • 𝟙 G' = 0) :
    augmentation f zs H ≫ g = augmentation (f ≫ g) zs H' := by
  induction zs with
  | nil => rfl
  | cons r zs ih =>
    change mappingCone.desc (r • 𝟙 (tensor zs F)) 0 _ _ ≫ g =
      mappingCone.desc (r • 𝟙 (tensor zs F)) 0 _ _
    ext i : 1
    apply (mappingCone.ext_from_iff (r • 𝟙 (tensor zs F)) (i+1) i rfl _ _).mpr
    constructor
    · simp [HomologicalComplex.comp_f]
    · simpa only [augmentation, HomologicalComplex.comp_f, Category.assoc,
        mappingCone.inr_f_desc_f_assoc, mappingCone.inr_f_desc_f] using
        congrArg (fun f => f.f i) (ih _ _)

 
@[reassoc]
lemma powerMap_augmentation {F G : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ G) (zs : List R) (a b : ℕ) (hab : a ≤ b)
    (Ha : ∀ r ∈ zs.map (· ^ a), r • 𝟙 G = 0)
    (Hb : ∀ r ∈ zs.map (· ^ b), r • 𝟙 G = 0) :
    powerMap F a b hab zs ≫ augmentation f (zs.map (· ^ a)) Ha =
      augmentation f (zs.map (· ^ b)) Hb := by
  induction zs with
  | nil => exact Category.id_comp _
  | cons r zs ih =>
    change mappingCone.map _ _ _ _ _ ≫ mappingCone.desc _ 0 _ _ =
      mappingCone.desc _ 0 _ _
    ext i : 1
    apply (mappingCone.ext_from_iff _ (i+1) i rfl _ _).mpr
    constructor
    · simp [mappingCone.map, HomologicalComplex.comp_f, Category.assoc]
    · simpa [mappingCone.map, HomologicalComplex.comp_f, Category.assoc] using
        congrArg (fun f => f.f i) (ih _ _)

noncomputable def quotientAugmentation
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (zs : List R) :
    tensor zs F ⟶ (complexQuotient (entryIdeal zs) (.up ℤ)).obj F :=
  augmentation (complexQuotientπ _ F) zs (fun r hr =>
    complexQuotient_annihilated _ r (Ideal.subset_span hr) F)

@[reassoc (attr := simp)]
lemma quotientAugmentation_inclusion
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (zs : List R) :
    inclusion F zs ≫ quotientAugmentation F zs =
      complexQuotientπ (entryIdeal zs) F :=
  inclusion_augmentation _ zs _

end Lech.Koszul
end

end OAI
