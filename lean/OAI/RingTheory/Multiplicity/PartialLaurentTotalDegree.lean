import Mathlib
import OAI.RingTheory.Multiplicity.LechTorsionOf

namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
namespace Lech.PartialLaurent
open AddMonoidAlgebra HomogeneousLocalization
universe u
variable (R : Type u) [CommRing R] {h : ℕ} (s : Finset (Fin h))
def totalDegreeNat : (Fin h → ℕ) →+ ℕ where
  toFun a := ∑ i,a i
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]
def totalDegreeInt : exponents s →+ ℤ where
  toFun := degree s
  map_zero' := by simp [degree]
  map_add' a b := by simp [degree,Finset.sum_add_distrib]
abbrev polyGrade := gradeBy R (totalDegreeNat (h := h))
abbrev laurentGrade := gradeBy R (totalDegreeInt s)
lemma homogeneous_eq_grade (t : ℤ) : homogeneous R s t = laurentGrade R s t := by
  ext x
  rfl
lemma total_fromNat (a : Fin h → ℕ) : totalDegreeInt s (fromNat s a) = totalDegreeNat a := by
  change (∑ i,(a i : ℤ)) = ((∑ i,a i : ℕ) : ℤ)
  simp
lemma total_indicator : totalDegreeNat (indicator s) = s.card := by
  classical
  simp [totalDegreeNat,indicator]
lemma denominator_homogeneous : denominator R s ∈ polyGrade R s.card := by
  rw [← total_indicator s]
  exact single_mem_gradeBy _ _ _
lemma algebraMap_homogeneous {n : ℕ} {a : Poly R (h := h)} (ha : a ∈ polyGrade R n) :
    algebraMap (Poly R (h := h)) (Laurent R s) a ∈ laurentGrade R s (n : ℤ) := by
  classical
  intro e he
  change e ∈ (Finsupp.mapDomain (fromNat s) a.coeff).support at he
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support he)
  rw [total_fromNat,ha v hv]
lemma algebraMap_homogeneous_iff {n : ℕ} {a : Poly R (h := h)} :
    algebraMap (Poly R (h := h)) (Laurent R s) a ∈ laurentGrade R s (n : ℤ) ↔
      a ∈ polyGrade R n := by
  refine ⟨?_,algebraMap_homogeneous R s⟩
  intro ha e he
  have hh : fromNat s e ∈ (algebraMap (Poly R (h := h)) (Laurent R s) a).coeff.support := by
    change fromNat s e ∈ (Finsupp.mapDomain (fromNat s) a.coeff).support
    rw [Finsupp.mem_support_iff,Finsupp.mapDomain_apply_of_injective (fromNat_injective s)]
    exact Finsupp.mem_support_iff.mp he
  have hh := ha _ hh
  change totalDegreeInt s (fromNat s e) = (n : ℤ) at hh
  rw [total_fromNat] at hh
  exact Int.natCast_inj.mp hh

def zeroDegree : Subring (Laurent R s) where
  carrier := laurentGrade R s 0
  zero_mem' := Submodule.zero_mem _
  one_mem' := SetLike.one_mem_graded _
  add_mem' := Submodule.add_mem _
  neg_mem' := Submodule.neg_mem _
  mul_mem' ha hb := by simpa using SetLike.mul_mem_graded ha hb

abbrev projectiveChart := HomogeneousLocalization.Away (polyGrade R (h := h)) (denominator R s)
def homogeneousToLaurent : projectiveChart R s →+* Laurent R s :=
  (IsLocalization.algEquiv (Submonoid.powers (denominator R s))
    (Localization.Away (denominator R s)) (Laurent R s)).toRingEquiv.toRingHom.comp
    (algebraMap (projectiveChart R s) (Localization.Away (denominator R s)))
lemma homogeneousToLaurent_injective : Function.Injective (homogeneousToLaurent R s) :=
  (IsLocalization.algEquiv (Submonoid.powers (denominator R s))
    (Localization.Away (denominator R s)) (Laurent R s)).injective.comp
    (HomogeneousLocalization.val_injective _)
lemma inverse_denominator (n : ℕ) :
    algebraMap (Poly R (h := h)) (Laurent R s) ((denominator R s)^n) *
      single (n • negativeIndicator s) (1 : R) = 1 := by
  rw [denominator,single_pow,one_pow,algebraMap_single,single_mul_single,one_mul]
  have h : fromNat s (n • indicator s) + n • negativeIndicator s = 0 := by
    rw [map_nsmul,←nsmul_add,indicator_add_negative,nsmul_zero]
  rw [h]
  exact AddMonoidAlgebra.one_def.symm
lemma total_negative_indicator : totalDegreeInt s (negativeIndicator s) = -(s.card : ℤ) := by
  have hh := congrArg (totalDegreeInt s) (indicator_add_negative s)
  rw [map_add,map_zero,total_fromNat,total_indicator] at hh
  linarith
lemma inverse_denominator_homogeneous (n : ℕ) :
    single (n • negativeIndicator s) (1 : R) ∈ laurentGrade R s (-(n*s.card : ℕ) : ℤ) := by
  have ht : totalDegreeInt s (n • negativeIndicator s) = -(n*s.card : ℕ) := by
    rw [map_nsmul,total_negative_indicator]
    simp
  rw [←ht]
  exact single_mem_gradeBy _ _ _
lemma homogeneousToLaurent_mk (n : ℕ) (a : Poly R (h := h))
    (ha : a ∈ polyGrade R (n • s.card)) :
    homogeneousToLaurent R s (Away.mk _ (denominator_homogeneous R s) n a ha) =
      algebraMap (Poly R (h := h)) (Laurent R s) a *
        single (n • negativeIndicator s) 1 := by
  change (IsLocalization.algEquiv (Submonoid.powers (denominator R s))
    (Localization.Away (denominator R s)) (Laurent R s))
      (Localization.mk a ⟨(denominator R s)^n,⟨n,rfl⟩⟩) = _
  rw [Localization.mk_eq_mk',IsLocalization.algEquiv_mk']
  symm
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  rw [mul_assoc,mul_comm (AddMonoidAlgebra.single _ _),inverse_denominator,mul_one]
lemma homogeneousToLaurent_mem (x : projectiveChart R s) :
    homogeneousToLaurent R s x ∈ zeroDegree R s := by
  obtain ⟨n,a,ha,rfl⟩ := Away.mk_surjective _ (denominator_homogeneous R s) x
  rw [homogeneousToLaurent_mk]
  have hh := SetLike.mul_mem_graded (algebraMap_homogeneous R s ha)
    (inverse_denominator_homogeneous R s n)
  change _ ∈ laurentGrade R s 0
  simpa only [nsmul_eq_mul,Nat.cast_id,add_neg_cancel] using hh

def projectiveToZero : projectiveChart R s →+* zeroDegree R s :=
  (homogeneousToLaurent R s).codRestrict _ (homogeneousToLaurent_mem R s)

lemma projectiveToZero_surjective : Function.Surjective (projectiveToZero R s) := by
  intro x
  obtain ⟨n,a,ha⟩ := clear_denominators R s x.val
  have hden : (denominator R s)^n ∈ polyGrade R (n*s.card) := by
    simpa only [nsmul_eq_mul,Nat.cast_id] using SetLike.pow_mem_graded n (denominator_homogeneous R s)
  have hprod := SetLike.mul_mem_graded x.property (algebraMap_homogeneous R s hden)
  rw [ha] at hprod
  have hap : a ∈ polyGrade R (n*s.card) := (algebraMap_homogeneous_iff R s).mp (by
    simpa only [zero_add] using hprod)
  refine ⟨Away.mk _ (denominator_homogeneous R s) n a hap,?_⟩
  apply Subtype.ext
  change homogeneousToLaurent R s _ = x.val
  rw [homogeneousToLaurent_mk,←ha,mul_assoc,inverse_denominator,mul_one]
 

def projectiveEquiv : projectiveChart R s ≃+* zeroDegree R s :=
  RingEquiv.ofBijective (projectiveToZero R s)
    ⟨fun _a _b hab => homogeneousToLaurent_injective R s (congrArg Subtype.val hab),
      projectiveToZero_surjective R s⟩
end Lech.PartialLaurent


namespace Lech.PartialLaurent
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] {h : ℕ}
lemma restrict_homogeneous {s t : Finset (Fin h)} (hst : s ⊆ t)
    {d : ℤ} {a : Laurent R s} (ha : a ∈ laurentGrade R s d) :
    restrict R hst a ∈ laurentGrade R t d := by
  classical
  intro e he
  change e ∈ (Finsupp.mapDomain (exponentInclusion hst) a.coeff).support at he
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support he)
  exact ha v hv

def homogeneousRestrict {s t : Finset (Fin h)} (hst : s ⊆ t) (d : ℤ) :
    laurentGrade R s d →ₗ[R] laurentGrade R t d where
  toFun a := ⟨restrict R hst a,restrict_homogeneous R hst a.property⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' c a := by
    apply Subtype.ext
    apply coeff_injective
    change Finsupp.mapDomain (exponentInclusion hst) (c • a.val.coeff) =
      c • Finsupp.mapDomain (exponentInclusion hst) a.val.coeff
    exact Finsupp.mapDomain_smul c a.val.coeff

variable (s : Finset (Fin h)) (k : Fin h) (hk : k ∈ s)
def chartExponent : ℤ →+ exponents s where
  toFun t := ⟨Pi.single k t,by
    intro i hi
    have hne : i ≠ k := fun h => hi (h ▸ hk)
    simp [hne]⟩
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp [Pi.single_add]
lemma chartExponent_degree (t : ℤ) : totalDegreeInt s (chartExponent s k hk t) = t := by
  change (∑ i,Pi.single k t i) = t
  simp
lemma chartMonomial_mul (t u : ℤ) :
    single (chartExponent s k hk t) (1 : R) * single (chartExponent s k hk u) 1 =
      single (chartExponent s k hk (t+u)) 1 := by
  rw [single_mul_single,one_mul,map_add]
lemma chartMonomial_inverse (t : ℤ) :
    single (chartExponent s k hk (-t)) (1 : R) * single (chartExponent s k hk t) 1 = 1 := by
  rw [chartMonomial_mul,neg_add_cancel,map_zero]
  exact AddMonoidAlgebra.one_def.symm
lemma chartMonomial_homogeneous (t : ℤ) :
    single (chartExponent s k hk t) (1 : R) ∈ laurentGrade R s t := by
  simpa only [chartExponent_degree] using
    single_mem_gradeBy (totalDegreeInt s) (chartExponent s k hk t) (1 : R)
 

def twistTrivialization (t : ℤ) : laurentGrade R s 0 ≃ₗ[R] laurentGrade R s t where
  toFun a := ⟨single (chartExponent s k hk t) 1 * a.val,by
    simpa only [add_zero] using SetLike.mul_mem_graded (chartMonomial_homogeneous R s k hk t) a.property⟩
  invFun a := ⟨single (chartExponent s k hk (-t)) 1 * a.val,by
    simpa only [neg_add_cancel] using SetLike.mul_mem_graded (chartMonomial_homogeneous R s k hk (-t)) a.property⟩
  left_inv a := by
    apply Subtype.ext
    change single _ (1 : R) * (single _ 1 * a.val) = a.val
    rw [←mul_assoc,chartMonomial_inverse,one_mul]
  right_inv a := by
    apply Subtype.ext
    change single _ (1 : R) * (single _ 1 * a.val) = a.val
    rw [←mul_assoc,mul_comm (AddMonoidAlgebra.single _ _),chartMonomial_inverse,one_mul]
  map_add' a b := by apply Subtype.ext; exact mul_add _ _ _
  map_smul' c a := by apply Subtype.ext; exact mul_smul_comm _ _ _

end Lech.PartialLaurent


namespace Lech.PartialLaurent
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] {h : ℕ}

def degreeInclusion {s v : Finset (Fin h)} (hsv : s ⊆ v) (d : ℤ) :
    {e : exponents s // degree s e = d} → {e : exponents v // degree v e = d} :=
  fun e => ⟨exponentInclusion hsv e.val, e.property⟩

lemma homogeneousEquiv_symm_single (s : Finset (Fin h)) (d : ℤ)
    (e : {e : exponents s // degree s e = d}) (r : R) :
    ((homogeneousEquiv R s d).symm (Finsupp.single e r)).val = single e.val r := by
  apply coeff_injective
  change ((Finsupp.supportedEquivFinsupp (R := R) {e : exponents s | degree s e = d}).symm
    (Finsupp.single e r)).val = Finsupp.single e.val r
  exact Finsupp.supportedEquivFinsupp_symm_single _ _ _

def coefficientChartRestrict {s v : Finset (Fin h)} (hsv : s ⊆ v) (d : ℤ) :
    homogeneous R s d →ₗ[R] homogeneous R v d where
  toFun a := ⟨restrict R hsv a.val, restrict_homogeneous R hsv a.property⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' c a := by
    apply Subtype.ext
    apply coeff_injective
    exact Finsupp.mapDomain_smul c a.val.coeff

 

lemma homogeneousEquiv_restrict_symm {s v : Finset (Fin h)} (hsv : s ⊆ v) (d : ℤ)
    (a : {e : exponents s // degree s e = d} →₀ R) :
    coefficientChartRestrict R hsv d ((homogeneousEquiv R s d).symm a) =
      (homogeneousEquiv R v d).symm (Finsupp.mapDomain (degreeInclusion hsv d) a) := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    simpa only [map_add, Finsupp.mapDomain_add] using congrArg₂ (· + ·) ha hb
  | single e r =>
    apply Subtype.ext
    change restrict R hsv (((homogeneousEquiv R s d).symm (Finsupp.single e r)).val) = _
    rw [homogeneousEquiv_symm_single, restrict_single, Finsupp.mapDomain_single,
      homogeneousEquiv_symm_single]
    rfl

lemma homogeneousEquiv_restrict {s v : Finset (Fin h)} (hsv : s ⊆ v) (d : ℤ)
    (a : homogeneous R s d) :
    homogeneousEquiv R v d (coefficientChartRestrict R hsv d a) =
      Finsupp.mapDomain (degreeInclusion hsv d) (homogeneousEquiv R s d a) := by
  obtain ⟨b,rfl⟩ := (homogeneousEquiv R s d).symm.surjective a
  rw [homogeneousEquiv_restrict_symm, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

 

lemma exponent_allowed_iff (s : Finset (Fin h)) (e : Fin h → ℤ) :
    e ∈ exponents s ↔ {i : Fin h | e i < 0}.toFinset ⊆ s := by
  classical
  change (∀ i, i ∉ s → 0 ≤ e i) ↔ _
  constructor
  · intro ha i hi
    by_contra hn
    have he : e i < 0 := by simpa only [Set.mem_toFinset, Set.mem_ofPred_eq] using hi
    exact (not_lt_of_ge (ha i hn)) he
  · intro ha i hi
    by_contra hn
    apply hi
    apply ha
    simpa only [Set.mem_toFinset, Set.mem_ofPred_eq] using (lt_of_not_ge hn)
end Lech.PartialLaurent


namespace Lech.ActualCech
open scoped BigOperators
universe u v
variable (A : Type u) [CommRing A] {ι : Type v}
abbrev Row (n : ℕ) := (Fin n → ι) → A
 

def delta (n : ℕ) : Row A (ι := ι) n →ₗ[A] Row A (ι := ι) (n+1) where
  toFun f a := ∑ i : Fin (n+1), (-1 : A)^i.val * f (a ∘ i.succAbove)
  map_add' f g := by ext a; simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' r f := by
    ext a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
 
def extra (j : ι) (n : ℕ) : Row A (ι := ι) (n+1) →ₗ[A] Row A (ι := ι) n where
  toFun f a := f (Fin.cons j a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma delete_insert_zero {n : ℕ} (j : ι) (a : Fin n → ι) :
    Fin.cons j a ∘ (0 : Fin (n+1)).succAbove = a := by
  funext i
  simp
lemma delete_insert_succ {n : ℕ} (j : ι) (a : Fin (n+1) → ι) (i : Fin (n+1)) :
    Fin.cons j a ∘ i.succ.succAbove = Fin.cons j (a ∘ i.succAbove) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  · simp [Fin.succ_succAbove_succ]

 
lemma extra_delta (j : ι) (n : ℕ) (f : Row A (ι := ι) (n+1)) :
    extra A j (n+1) (delta A (n+1) f) + delta A n (extra A j n f) = f := by
  ext a
  change (∑ i : Fin (n+2), (-1 : A)^i.val * f (Fin.cons j a ∘ i.succAbove)) +
      (∑ i : Fin (n+1), (-1 : A)^i.val * f (Fin.cons j (a ∘ i.succAbove))) = f a
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,one_mul,delete_insert_zero,Fin.val_succ,
    pow_succ,delete_insert_succ,mul_neg_one,neg_mul,Finset.sum_neg_distrib]
  abel
lemma extra_delta_zero (j : ι) (f : Row A (ι := ι) 0) :
    extra A j 0 (delta A 0 f) = f := by
  ext a
  change (∑ i : Fin 1, (-1 : A)^i.val * f (Fin.cons j a ∘ i.succAbove)) = f a
  simp

 

lemma delta_square (n : ℕ) (f : Row A (ι := ι) n) :
    delta A (n+1) (delta A n f) = 0 := by
  induction n with
  | zero =>
    ext a
    have hf (b : Fin 0 → ι) : f b = f Fin.elim0 := congrArg f (Subsingleton.elim _ _)
    simp [delta,Fin.sum_univ_two,hf]
  | succ n ih =>
    have hh (j : ι) : extra A j (n+2) (delta A (n+2) (delta A (n+1) f))=0 := by
      have h₁ := extra_delta A j (n+1) (delta A (n+1) f)
      have h₂ := congrArg (delta A (n+1)) (extra_delta A j n f)
      rw [map_add, ih, add_zero] at h₂
      rw [h₂] at h₁
      exact add_right_cancel (h₁.trans (zero_add _).symm)
    ext a
    have he := congrFun (hh (a 0)) (fun i => a i.succ)
    change delta A (n+2) (delta A (n+1) f) (Fin.cons (a 0) (Fin.tail a))=0 at he
    rw [Fin.cons_self_tail] at he
    exact he

 

abbrev Cochains (h n : ℕ) := (Fin h → ℤ) →₀ Row A (ι := Fin h) n

def d (h n : ℕ) : Cochains A h n →ₗ[A] Cochains A h (n+1) :=
  Finsupp.mapRange.linearMap (delta A n)
@[simp] lemma d_apply (h n : ℕ) (f : Cochains A h n) (e : Fin h → ℤ) :
    d A h n f e = delta A n (f e) := rfl

 

def Allowed {h n : ℕ} (e : Fin h → ℤ) (a : Fin n → Fin h) : Prop :=
  ∀ i, e i < 0 → i ∈ Set.range a

def homogeneous (h n : ℕ) (t : ℤ) : Submodule A (Cochains A h n) where
  carrier := {f | ∀ e a, (∑ i, e i) ≠ t ∨ ¬ Allowed e a → f e a=0}
  zero_mem' := by intro e a he; rfl
  add_mem' := by intro f g hf hg e a he; change f e a + g e a=0; rw [hf e a he,hg e a he,add_zero]
  smul_mem' := by intro r f hf e a he; change r * f e a = 0; rw [hf e a he,mul_zero]

lemma d_mem {h n : ℕ} {t : ℤ} {f : Cochains A h n} (hf : f ∈ homogeneous A h n t) :
    d A h n f ∈ homogeneous A h (n+1) t := by
  intro e a he
  change (∑ i : Fin (n+1), (-1 : A)^i.val * f e (a ∘ i.succAbove))=0
  apply Finset.sum_eq_zero
  intro i _
  rw [hf e (a ∘ i.succAbove) ?_, mul_zero]
  rcases he with he | he
  · exact Or.inl he
  · right
    intro hg
    apply he
    intro j hj
    obtain ⟨k,hk⟩ := hg j hj
    exact ⟨i.succAbove k,hk⟩

lemma exists_nonneg {h : ℕ} (hh : 0<h) {e : Fin h → ℤ} (he : 0 ≤ ∑ i,e i) :
    ∃ j, 0 ≤ e j := by
  by_contra hn
  have hneg : ∀ j, e j < 0 := fun j => lt_of_not_ge (fun hj => hn ⟨j,hj⟩)
  have : (∑ j,e j) < 0 := Finset.sum_neg (fun j _ => hneg j)
    ⟨⟨0,hh⟩,Finset.mem_univ _⟩
  omega

 

def chosen {h : ℕ} (hh : 0<h) (e : Fin h → ℤ) : Fin h :=
  if he : 0≤∑ i,e i then (exists_nonneg hh he).choose else ⟨0,hh⟩
lemma chosen_nonneg {h : ℕ} (hh : 0<h) {e : Fin h → ℤ} (he : 0≤∑ i,e i) :
    0 ≤ e (chosen hh e) := by
  dsimp [chosen]
  rw [dite_eq_left he]
  exact (exists_nonneg hh he).choose_spec

def contraction {h : ℕ} (hh : 0<h) (n : ℕ) :
    Cochains A h (n+1) →ₗ[A] Cochains A h n :=
  Finsupp.lsum A (fun e => (Finsupp.lsingle e).comp (extra A (chosen hh e) n))
@[simp] lemma contraction_apply {h : ℕ} (hh : 0<h) (n : ℕ)
    (f : Cochains A h (n+1)) (e : Fin h → ℤ) :
    contraction A hh n f e = extra A (chosen hh e) n (f e) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha,hb]
  | single k r =>
    simp only [contraction,Finsupp.lsum_single,LinearMap.comp_apply,Finsupp.lsingle_apply]
    by_cases hk : k=e
    · subst k; simp
    · simp [hk]

lemma contraction_mem {h n : ℕ} (hh : 0<h) {t : ℤ} (ht : 0≤t)
    {f : Cochains A h (n+1)} (hf : f ∈ homogeneous A h (n+1) t) :
    contraction A hh n f ∈ homogeneous A h n t := by
  intro e a he
  rw [contraction_apply]
  change f e (Fin.cons (chosen hh e) a) = 0
  apply hf
  by_cases het : (∑ i,e i) = t
  · right
    have hj : 0 ≤ e (chosen hh e) := chosen_nonneg hh (het.symm ▸ ht)
    have hna : ¬ Allowed e a := he.resolve_left (not_not.mpr het)
    intro hall
    apply hna
    intro i hi
    obtain ⟨k,hk⟩ := hall i hi
    revert hk
    refine Fin.cases ?_ (fun k => ?_) k
    · intro hk
      have : chosen hh e = i := by simpa using hk
      exact (not_lt_of_ge hj (this.symm ▸ hi)).elim
    · intro hk
      exact ⟨k,by simpa using hk⟩

  · exact Or.inl het

lemma contraction_identity {h : ℕ} (hh : 0<h) (n : ℕ) (f : Cochains A h (n+1)) :
    contraction A hh (n+1) (d A h (n+1) f) +
      d A h n (contraction A hh n f) = f := by
  apply Finsupp.ext
  intro e
  simp only [Finsupp.add_apply,contraction_apply,d_apply]
  exact extra_delta A (chosen hh e) n (f e)

 

theorem exact_nonnegative {h : ℕ} (hh : 0<h) (n : ℕ) {t : ℤ} (ht : 0≤t)
    (f : Cochains A h (n+1)) (hf : f ∈ homogeneous A h (n+1) t)
    (hc : d A h (n+1) f=0) :
    ∃ g ∈ homogeneous A h n t, d A h n g=f := by
  refine ⟨contraction A hh n f, contraction_mem A hh ht hf, ?_⟩
  have he := contraction_identity A hh n f
  simpa only [hc,map_zero,zero_add] using he
end Lech.ActualCech
end
end

end OAI
