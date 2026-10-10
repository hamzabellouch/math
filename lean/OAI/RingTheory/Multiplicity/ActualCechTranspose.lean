import Mathlib
import OAI.RingTheory.Multiplicity.PartialLaurentTotalDegree

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
namespace Lech.ActualCech

section
open scoped BigOperators
universe u
variable (A : Type u) [CommRing A]


def transpose (h n : ℕ) : Cochains A h n ≃ₗ[A]
    ((Fin n → Fin h) → ((Fin h → ℤ) →₀ A)) :=
  (Finsupp.mapRange.linearEquiv
    (Finsupp.linearEquivFunOnFinite A A (Fin n → Fin h)).symm).trans <|
  (Finsupp.curryLinearEquiv A).symm.trans <|
  (Finsupp.domLCongr (Equiv.prodComm _ _)).trans <|
  (Finsupp.curryLinearEquiv A).trans <|
  Finsupp.linearEquivFunOnFinite A ((Fin h → ℤ) →₀ A) (Fin n → Fin h)

@[simp] lemma transpose_apply (h n : ℕ) (f : Cochains A h n)
    (a : Fin n → Fin h) (e : Fin h → ℤ) : transpose A h n f a e = f e a := by
  simp [transpose, Finsupp.domLCongr_apply]

@[simp] lemma transpose_symm_apply (h n : ℕ)
    (f : (Fin n → Fin h) → ((Fin h → ℤ) →₀ A)) (e : Fin h → ℤ) (a : Fin n → Fin h) :
    (transpose A h n).symm f e a = f a e := by
  have he := congrArg (fun g => g a e) ((transpose A h n).apply_symm_apply f)
  simpa only [transpose_apply] using he

def allowedSet {h n : ℕ} (a : Fin n → Fin h) (t : ℤ) : Set (Fin h → ℤ) :=
  {e | (∑ i,e i) = t ∧ Allowed e a}


def supportedTranspose (h n : ℕ) (t : ℤ) : homogeneous A h n t ≃ₗ[A]
    ((a : Fin n → Fin h) → Finsupp.supported A A (allowedSet a t)) where
  toFun f a := ⟨transpose A h n f.val a, by
    rw [Finsupp.mem_supported']
    intro e he
    rw [transpose_apply]
    apply f.property e a
    simpa only [allowedSet,Set.mem_ofPred_eq,not_and_or] using he⟩
  invFun f := ⟨(transpose A h n).symm (fun a => (f a).val), by
    intro e a he
    rw [transpose_symm_apply]
    apply (Finsupp.mem_supported' A (f a).val).mp (f a).property e
    simpa only [allowedSet,Set.mem_ofPred_eq,not_and_or] using he⟩
  left_inv f := by apply Subtype.ext; exact (transpose A h n).symm_apply_apply f.val
  right_inv f := by
    funext a
    apply Subtype.ext
    exact congrFun ((transpose A h n).apply_symm_apply (fun a => (f a).val)) a
  map_add' f g := by funext a; apply Subtype.ext; exact congrFun (map_add (transpose A h n) f.val g.val) a
  map_smul' r f := by funext a; apply Subtype.ext; exact congrFun (map_smul (transpose A h n) r f.val) a

 
def intersection {h n : ℕ} (a : Fin n → Fin h) : Finset (Fin h) :=
  Finset.univ.image a
@[simp] lemma mem_intersection {h n : ℕ} (a : Fin n → Fin h) (i : Fin h) :
    i ∈ intersection a ↔ i ∈ Set.range a := by simp [intersection]

lemma mem_exponents_intersection {h n : ℕ} (a : Fin n → Fin h) (e : Fin h → ℤ) :
    e ∈ PartialLaurent.exponents (intersection a) ↔ Allowed e a := by
  change (∀ i, i ∉ intersection a → 0 ≤ e i) ↔ (∀ i, e i < 0 → i ∈ Set.range a)
  simp only [mem_intersection]
  constructor
  · intro he i hi
    by_contra hn
    exact (not_lt_of_ge (he i hn)) hi
  · intro he i hi
    exact le_of_not_gt (fun hn => hi (he i hn))


def exponentEquiv {h n : ℕ} (a : Fin n → Fin h) (t : ℤ) :
    allowedSet a t ≃ {e : PartialLaurent.exponents (intersection a) //
      PartialLaurent.degree (intersection a) e = t} where
  toFun e := ⟨⟨e.val,(mem_exponents_intersection a e.val).mpr e.property.2⟩,e.property.1⟩
  invFun e := ⟨e.val.val, e.property,(mem_exponents_intersection a e.val.val).mp e.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl


abbrev laurentCochains (h n : ℕ) (t : ℤ) :=
  (a : Fin n → Fin h) → PartialLaurent.homogeneous A (intersection a) t
 

def laurentEquiv (h n : ℕ) (t : ℤ) : homogeneous A h n t ≃ₗ[A]
    laurentCochains A h n t :=
  (supportedTranspose A h n t).trans <|
  LinearEquiv.piCongrRight (fun a =>
    (Finsupp.supportedEquivFinsupp (allowedSet a t)).trans <|
    (Finsupp.domLCongr (exponentEquiv a t)).trans <|
    (PartialLaurent.homogeneousEquiv A (intersection a) t).symm)
@[simp] lemma homogeneousEquiv_apply {h : ℕ} (s : Finset (Fin h)) (t : ℤ)
    (f : PartialLaurent.homogeneous A s t)
    (e : {e : PartialLaurent.exponents s // PartialLaurent.degree s e = t}) :
    PartialLaurent.homogeneousEquiv A s t f e = f.val.coeff e.val := rfl

@[simp] lemma laurentEquiv_homogeneousEquiv (h n : ℕ) (t : ℤ)
    (f : homogeneous A h n t) (a : Fin n → Fin h)
    (e : {e : PartialLaurent.exponents (intersection a) //
      PartialLaurent.degree (intersection a) e=t}) :
    PartialLaurent.homogeneousEquiv A (intersection a) t (laurentEquiv A h n t f a) e =
      f.val e.val.val a := by
  change PartialLaurent.homogeneousEquiv A (intersection a) t
    ((PartialLaurent.homogeneousEquiv A (intersection a) t).symm
      (Finsupp.domLCongr (R := A) (M := A) (exponentEquiv a t)
      (Finsupp.supportedEquivFinsupp (R := A) (allowedSet a t)
      (supportedTranspose A h n t f a)))) e = _
  rw [LinearEquiv.apply_symm_apply]
  rw [Finsupp.domLCongr_apply]
  change transpose A h n f.val a ((exponentEquiv a t).symm e).val = _
  exact transpose_apply A h n f.val a e.val.val

lemma laurentEquiv_coeff (h n : ℕ) (t : ℤ)
    (f : homogeneous A h n t) (a : Fin n → Fin h)
    (e : PartialLaurent.exponents (intersection a)) :
    (laurentEquiv A h n t f a).val.coeff e = f.val e.val a := by
  by_cases he : PartialLaurent.degree (intersection a) e=t
  · exact laurentEquiv_homogeneousEquiv A h n t f a ⟨e,he⟩
  · have hleft : (laurentEquiv A h n t f a).val.coeff e = 0 := by
      exact (Finsupp.mem_supported' A _).mp (laurentEquiv A h n t f a).property e he
    rw [hleft, f.property e.val a (Or.inl he)]

lemma intersection_delete {h n : ℕ} (a : Fin (n+1) → Fin h) (i : Fin (n+1)) :
    intersection (a ∘ i.succAbove) ⊆ intersection a := by
  intro j hj
  rw [mem_intersection] at hj ⊢
  obtain ⟨k,hk⟩ := hj
  exact ⟨i.succAbove k,hk⟩

 
def laurentD (h n : ℕ) (t : ℤ) :
    laurentCochains A h n t →ₗ[A] laurentCochains A h (n+1) t where
  toFun f a := ∑ i : Fin (n+1), (-1 : A)^i.val •
    PartialLaurent.coefficientChartRestrict A (intersection_delete a i) t (f (a ∘ i.succAbove))
  map_add' f g := by
    funext a
    simp only [Pi.add_apply,map_add,smul_add,Finset.sum_add_distrib]
  map_smul' r f := by
    funext a
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _

lemma restrict_coeff_image {h : ℕ} {s v : Finset (Fin h)} (hsv : s ⊆ v)
    (f : PartialLaurent.Laurent A s) (e : PartialLaurent.exponents s) :
    (PartialLaurent.restrict A hsv f).coeff (PartialLaurent.exponentInclusion hsv e) =
      f.coeff e := by
  change Finsupp.mapDomain (PartialLaurent.exponentInclusion hsv) f.coeff
    (PartialLaurent.exponentInclusion hsv e) = _
  apply Finsupp.mapDomain_apply_of_injective
  intro a b hab
  exact Subtype.ext (congrArg (fun e : PartialLaurent.exponents v => e.val) hab)

lemma restrict_coeff_zero {h : ℕ} {s v : Finset (Fin h)} (hsv : s ⊆ v)
    (f : PartialLaurent.Laurent A s) (e : PartialLaurent.exponents v)
    (he : e.val ∉ PartialLaurent.exponents s) :
    (PartialLaurent.restrict A hsv f).coeff e = 0 := by
  change Finsupp.mapDomain (PartialLaurent.exponentInclusion hsv) f.coeff e = _
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨a,ha⟩
  exact he ((congrArg Subtype.val ha) ▸ a.property)

lemma laurentEquiv_restrict_coeff (h n : ℕ) (t : ℤ)
    (f : homogeneous A h n t) (a : Fin (n+1) → Fin h) (i : Fin (n+1))
    (e : PartialLaurent.exponents (intersection a)) :
    (PartialLaurent.coefficientChartRestrict A (intersection_delete a i) t
      (laurentEquiv A h n t f (a ∘ i.succAbove))).val.coeff e =
      f.val e.val (a ∘ i.succAbove) := by
  by_cases he : e.val ∈ PartialLaurent.exponents (intersection (a ∘ i.succAbove))
  · let es : PartialLaurent.exponents (intersection (a ∘ i.succAbove)) := ⟨e.val,he⟩
    have hes : PartialLaurent.exponentInclusion (intersection_delete a i) es = e := rfl
    change (PartialLaurent.restrict A (intersection_delete a i)
      (laurentEquiv A h n t f (a ∘ i.succAbove)).val).coeff e = _
    rw [← hes, restrict_coeff_image, laurentEquiv_coeff]
    rfl
  · change (PartialLaurent.restrict A (intersection_delete a i)
      (laurentEquiv A h n t f (a ∘ i.succAbove)).val).coeff e = _
    rw [restrict_coeff_zero A _ _ e he]
    exact (f.property e.val (a ∘ i.succAbove)
      (Or.inr (fun ha => he ((mem_exponents_intersection _ _).mpr ha)))).symm

def homogeneousD (h n : ℕ) (t : ℤ) :
    homogeneous A h n t →ₗ[A] homogeneous A h (n+1) t where
  toFun f := ⟨d A h n f.val,d_mem A f.property⟩
  map_add' f g := Subtype.ext (map_add (d A h n) f.val g.val)
  map_smul' r f := Subtype.ext (map_smul (d A h n) r f.val)


lemma laurentD_equiv (h n : ℕ) (t : ℤ) (f : homogeneous A h n t) :
    laurentD A h n t (laurentEquiv A h n t f) =
      laurentEquiv A h (n+1) t (homogeneousD A h n t f) := by
  funext a
  apply Subtype.ext
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro e
  rw [laurentEquiv_coeff]
  change (∑ i : Fin (n+1), (-1 : A)^i.val •
    PartialLaurent.coefficientChartRestrict A (intersection_delete a i) t
      (laurentEquiv A h n t f (a ∘ i.succAbove))).val.coeff e =
        (∑ i : Fin (n+1), (-1 : A)^i.val * f.val e.val (a ∘ i.succAbove))
  simp only [Submodule.coe_sum, Submodule.coe_smul, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    laurentEquiv_restrict_coeff, smul_eq_mul]


theorem laurent_exact_nonnegative {h : ℕ} (hh : 0<h) (n : ℕ) {t : ℤ} (ht : 0≤t)
    (f : laurentCochains A h (n+1) t) (hf : laurentD A h (n+1) t f=0) :
    ∃ g : laurentCochains A h n t, laurentD A h n t g=f := by
  obtain ⟨x,rfl⟩ := (laurentEquiv A h (n+1) t).surjective f
  rw [laurentD_equiv] at hf
  have hc : d A h (n+1) x.val = 0 := by
    have hx := (laurentEquiv A h (n+2) t).injective (hf.trans (map_zero _).symm)
    exact congrArg Subtype.val hx
  obtain ⟨y,hy,hdy⟩ := exact_nonnegative A hh n ht x.val x.property hc
  refine ⟨laurentEquiv A h n t ⟨y,hy⟩, ?_⟩
  rw [laurentD_equiv]
  apply congrArg (laurentEquiv A h (n+1) t)
  exact Subtype.ext hdy
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (A : Type u) [CommRing A]

lemma homogeneousD_square (h n : ℕ) (t : ℤ) (f : homogeneous A h n t) :
    homogeneousD A h (n+1) t (homogeneousD A h n t f)=0 := by
  apply Subtype.ext
  apply Finsupp.ext
  intro e
  exact delta_square A n (f.val e)

lemma laurentD_square (h n : ℕ) (t : ℤ) (f : laurentCochains A h n t) :
    laurentD A h (n+1) t (laurentD A h n t f)=0 := by
  obtain ⟨x,rfl⟩ := (laurentEquiv A h n t).surjective f
  rw [laurentD_equiv,laurentD_equiv,homogeneousD_square,map_zero]


def augmentedComplex (h : ℕ) (t : ℤ) : CochainComplex (ModuleCat.{u} A) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of A (laurentCochains A h n t))
    (fun n => ModuleCat.ofHom (laurentD A h n t)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact laurentD_square A h n t f)

lemma augmentedComplex_exactAt {h : ℕ} (hh : 0<h) (n : ℕ) (t : ℤ) (ht : 0≤t) :
    (augmentedComplex A h t).ExactAt (n+1) := by
  apply ((augmentedComplex A h t).exactAt_iff' (i := n) (j := n+1) (k := n+2)
    (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change (CochainComplex.of.d
    (fun n => ModuleCat.of A (laurentCochains A h n t))
    (fun n => ModuleCat.ofHom (laurentD A h n t)) (n+1) ((n+1)+1)).hom f=0 at hf
  rw [CochainComplex.of_d] at hf
  obtain ⟨x, hx⟩ := laurent_exact_nonnegative A hh n ht f hf
  refine ⟨x, ?_⟩
  change (CochainComplex.of.d
    (fun n => ModuleCat.of A (laurentCochains A h n t))
    (fun n => ModuleCat.ofHom (laurentD A h n t)) n (n+1)).hom x=f
  rw [CochainComplex.of_d]
  exact hx

 
theorem augmentedComplex_homology_zero {h : ℕ} (hh : 0<h) (n : ℕ) (t : ℤ) (ht : 0≤t) :
    IsZero ((augmentedComplex A h t).homology (n+1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (augmentedComplex_exactAt A hh n t ht)
end Lech.ActualCech

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
namespace Lech

section

section
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]


lemma quasiIso_middle {S T : ShortComplex (CochainComplex C ℤ)}
    (f : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact)
    [QuasiIso f.τ₁] [QuasiIso f.τ₃] : QuasiIso f.τ₂ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hprev : (ComplexShape.up ℤ).Rel (i-1) i := by change i - 1 + 1 = i; omega
  have hnext : (ComplexShape.up ℤ).Rel i (i+1) := rfl
  have hm : Mono (homologyMap f.τ₂ i) :=
    mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ f hS hT (i-1) i hprev))
      (composableArrows₅_exact hS (i-1) i hprev).δ₀.δ₀
      (composableArrows₅_exact hT (i-1) i hprev).δ₀.δ₀
      (inferInstanceAs (Epi (homologyMap f.τ₃ (i-1))))
      (inferInstanceAs (Mono (homologyMap f.τ₁ i)))
      (inferInstanceAs (Mono (homologyMap f.τ₃ i)))
  have he : Epi (homologyMap f.τ₂ i) :=
    epi_of_epi_of_epi_of_mono
      ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ f hS hT i (i+1) hnext))
      (composableArrows₅_exact hS i (i+1) hnext).δlast.δlast
      (composableArrows₅_exact hT i (i+1) hnext).δlast.δlast
      (inferInstanceAs (Epi (homologyMap f.τ₁ i)))
      (inferInstanceAs (Epi (homologyMap f.τ₃ i)))
      (inferInstanceAs (Mono (homologyMap f.τ₁ (i+1))))
  exact isIso_of_mono_of_epi _

end


open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

lemma quasiIsoAt_localization_iff {ι : Type*} {c : ComplexShape ι}
    (P : ObjectProperty C) [P.IsSerreClass]
    {K L : HomologicalComplex C c} (f : K ⟶ L) (i : ι) :
    let Q := P.isoModSerre.Q
    let := ObjectProperty.SerreClassLocalization.abelian Q P
    let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits Q P
    let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits Q P
    QuasiIsoAt ((Q.mapHomologicalComplex c).map f) i ↔
      P.isoModSerre (HomologicalComplex.homologyMap f i) := by
  dsimp only
  let Q := P.isoModSerre.Q
  let := ObjectProperty.SerreClassLocalization.abelian Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits Q P
  let S := K.sc i
  let T := L.sc i
  let g := (HomologicalComplex.shortComplexFunctor C c i).map f
  rw [quasiIsoAt_iff]
  change ShortComplex.QuasiIso (Q.mapShortComplex.map g) ↔ _
  rw [ShortComplex.quasiIso_iff]
  rw [← ObjectProperty.SerreClassLocalization.isIso_map_iff Q P]
  change IsIso (ShortComplex.homologyMap (Q.mapShortComplex.map g)) ↔
    IsIso (Q.map (ShortComplex.homologyMap g))
  have he := ShortComplex.mapHomologyIso_hom_naturality g Q
  have hfact : Q.map (ShortComplex.homologyMap g) =
      (S.mapHomologyIso Q).inv ≫ ShortComplex.homologyMap (Q.mapShortComplex.map g) ≫
        (T.mapHomologyIso Q).hom := by
    rw [he, Iso.inv_hom_id_assoc]
  rw [hfact, isIso_comp_left_iff, isIso_comp_right_iff]


lemma homology_middle_isoModSerre (P : ObjectProperty C) [P.IsSerreClass]
    {S T : ShortComplex (CochainComplex C ℤ)} (f : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact)
    (h₁ : ∀ i, P.isoModSerre (HomologicalComplex.homologyMap f.τ₁ i))
    (h₃ : ∀ i, P.isoModSerre (HomologicalComplex.homologyMap f.τ₃ i)) (i : ℤ) :
    P.isoModSerre (HomologicalComplex.homologyMap f.τ₂ i) := by
  let Q := P.isoModSerre.Q
  let := ObjectProperty.SerreClassLocalization.abelian Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits Q P
  let F := Q.mapHomologicalComplex (ComplexShape.up ℤ)
  have : QuasiIso (F.map f.τ₁) := by
    rw [quasiIso_iff]
    intro j
    exact (quasiIsoAt_localization_iff P f.τ₁ j).mpr (h₁ j)
  have : QuasiIso (F.map f.τ₃) := by
    rw [quasiIso_iff]
    intro j
    exact (quasiIsoAt_localization_iff P f.τ₃ j).mpr (h₃ j)
  have heS : (S.map F).ShortExact := hS.map_of_exact F
  have heT : (T.map F).ShortExact := hT.map_of_exact F
  have : QuasiIso (F.mapShortComplex.map f).τ₁ :=
    inferInstanceAs (QuasiIso (F.map f.τ₁))
  have : QuasiIso (F.mapShortComplex.map f).τ₃ :=
    inferInstanceAs (QuasiIso (F.map f.τ₃))
  have : QuasiIso (F.map f.τ₂) :=
    quasiIso_middle (F.mapShortComplex.map f) heS heT
  exact (quasiIsoAt_localization_iff P f.τ₂ i).mp (inferInstanceAs (QuasiIsoAt (F.map f.τ₂) i))

end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
 

lemma homology_isoModSerre_of_termwise {ι : Type*} {c : ComplexShape ι}
    (P : ObjectProperty C) [P.IsSerreClass]
    {K L : HomologicalComplex C c} (f : K ⟶ L)
    (hf : ∀ i, P.isoModSerre (f.f i)) (i : ι) :
    P.isoModSerre (homologyMap f i) := by
  let Q := P.isoModSerre.Q
  let := ObjectProperty.SerreClassLocalization.abelian Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits Q P
  have (j : ι) : IsIso (((Q.mapHomologicalComplex c).map f).f j) :=
    (ObjectProperty.SerreClassLocalization.isIso_map_iff Q P (f.f j)).mpr (hf j)
  have : IsIso ((Q.mapHomologicalComplex c).map f) := Hom.isIso_of_components _
  exact (quasiIsoAt_localization_iff P f i).mp inferInstance
end Lech

end

end OAI
