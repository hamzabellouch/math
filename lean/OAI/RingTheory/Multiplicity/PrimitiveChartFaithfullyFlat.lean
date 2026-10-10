import Mathlib
import OAI.RingTheory.Multiplicity.LechHomogeneousEval

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech.PrimitiveChart
open Polynomial
universe u
variable {A : Type u} [CommRing A]

 

theorem faithfullyFlat_away (f : A[X])
    (hf : Ideal.span (Set.range f.coeff)=⊤) :
    Module.FaithfullyFlat A (Localization.Away f) := by
  have : Module.Flat A[X] (Localization.Away f) :=
    IsLocalization.flat (Localization.Away f) (Submonoid.powers f)
  have : Module.Flat A (Localization.Away f) :=
    Module.Flat.trans A A[X] (Localization.Away f)
  apply Module.FaithfullyFlat.of_comap_surjective
  intro p
  let I : Ideal A[X] := Ideal.map C p.asIdeal
  have hI : I.IsPrime := Ideal.isPrime_map_C_iff_isPrime _ |>.mpr p.isPrime
  have hnot : f∉I := by
    intro h
    have hcoef : ∀ k, f.coeff k∈p.asIdeal := Ideal.mem_map_C_iff.mp h
    have he : (⊤ : Ideal A)≤p.asIdeal := by
      rw [← hf]
      exact Ideal.span_le.mpr (by rintro _ ⟨k,rfl⟩; exact hcoef k)
    exact p.isPrime.ne_top (top_le_iff.mp he)
  let : I.IsPrime := hI
  have hdis : Disjoint (Submonoid.powers f : Set A[X]) (I : Set A[X]) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hnot
  let J : Ideal (Localization.Away f) := I.map (algebraMap A[X] (Localization.Away f))
  have hJ : J.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers f) (Localization.Away f) I hI hdis
  have hu : J.under A[X]=I := IsLocalization.under_map_of_isPrime_disjoint
    (Submonoid.powers f) (Localization.Away f) hI hdis
  refine ⟨⟨J,hJ⟩,?_⟩
  apply PrimeSpectrum.ext
  ext a
  change algebraMap A (Localization.Away f) a∈J ↔ a∈p.asIdeal
  rw [IsScalarTower.algebraMap_apply A A[X] (Localization.Away f)]
  change C a∈J.under A[X] ↔ a∈p.asIdeal
  rw [hu]
  change C a∈Ideal.map C p.asIdeal ↔ a∈p.asIdeal
  rw [Ideal.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro h k
    by_cases hk : k=0
    · simpa [hk] using h
    · simp [coeff_C,hk]

end Lech.PrimitiveChart


namespace Lech.BinaryChange
open Polynomial
universe u
variable {B : Type u} [CommRing B]
abbrev Binary := MvPolynomial (Fin 2) B

def forward (t : B) : Binary (B := B) →ₐ[B] Binary (B := B) :=
  MvPolynomial.aeval ![MvPolynomial.C t*MvPolynomial.X 0+MvPolynomial.X 1,
    MvPolynomial.X 0]

def backward (t : B) : Binary (B := B) →ₐ[B] Binary (B := B) :=
  MvPolynomial.aeval ![MvPolynomial.X 1,
    MvPolynomial.X 0-MvPolynomial.C t*MvPolynomial.X 1]

lemma forward_backward (t : B) : (forward t).comp (backward t)=AlgHom.id B _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [forward,backward]

lemma backward_forward (t : B) : (backward t).comp (forward t)=AlgHom.id B _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [forward,backward]

def equiv (t : B) : Binary (B := B) ≃ₐ[B] Binary (B := B) :=
  AlgEquiv.ofAlgHom (forward t) (backward t) (forward_backward t) (backward_forward t)

lemma forward_homogeneous {p : Binary (B := B)} {n : ℕ}
    (hp : p.IsHomogeneous n) (t : B) : ((forward t) p).IsHomogeneous n := by
  have hx : ∀ i : Fin 2,
      (![MvPolynomial.C t*MvPolynomial.X 0+MvPolynomial.X 1,
        MvPolynomial.X 0] i : Binary (B := B)).IsHomogeneous 1 := by
    intro i
    fin_cases i
    · simpa using ((MvPolynomial.isHomogeneous_X (R := B) 0).C_mul t).add
        (MvPolynomial.isHomogeneous_X (R := B) 1)
    · exact MvPolynomial.isHomogeneous_X (R := B) 0
  simpa only [one_mul,forward] using hp.aeval _ hx

def transform (f : B[X]) (n : ℕ) (t : B) : B[X] :=
  ∑ k ∈ Finset.range (n+1), C (f.coeff k)*(C t*Polynomial.X+1)^k*Polynomial.X^(n-k)

lemma linear_degree (t : B) : (C t*Polynomial.X+1).natDegree≤1 := by
  apply natDegree_add_le_of_degree_le
  · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  · simp

lemma term_degree (t : B) (c : B) {k n : ℕ} (hk : k≤n) :
    (C c*(C t*Polynomial.X+1)^k*Polynomial.X^(n-k)).natDegree≤n := by
  apply natDegree_mul_le.trans
  have hpow : ((C t*Polynomial.X+1)^k).natDegree≤k := by
    exact natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left k (linear_degree t))
  have hleft := (natDegree_C_mul_le c _).trans hpow
  have hright : (Polynomial.X^(n-k) : B[X]).natDegree≤n-k := by
    exact natDegree_X_pow_le (n-k)
  omega

lemma transform_degree (f : B[X]) (n : ℕ) (t : B) :
    (transform f n t).natDegree≤n := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact term_degree t _ (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

lemma term_coeff (t c : B) {k n : ℕ} (hk : k≤n) :
    (C c*(C t*Polynomial.X+1)^k*Polynomial.X^(n-k)).coeff n=c*t^k := by
  have hpow : ((C t*Polynomial.X+1)^k).natDegree≤k :=
    natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left k (linear_degree t))
  have hp := coeff_mul_add_eq_of_natDegree_le hpow (natDegree_X_pow_le (R := B) (n-k))
  rw [Nat.add_sub_of_le hk] at hp
  rw [mul_assoc,coeff_C_mul,hp]
  have he := coeff_pow_of_natDegree_le (m := k) (linear_degree t)
  simp only [mul_one] at he
  rw [he]
  simp [coeff_one]

lemma transform_top (f : B[X]) (n : ℕ) (t : B) (hn : f.natDegree≤n) :
    (transform f n t).coeff n=f.eval t := by
  rw [transform,finsetSum_coeff,eval_eq_sum_range' (Nat.lt_succ_iff.mpr hn)]
  apply Finset.sum_congr rfl
  intro k hk
  exact term_coeff t _ (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

lemma transform_eq_aeval (f : B[X]) (n : ℕ) (t : B) :
    transform f n t = MvPolynomial.aeval ![C t*Polynomial.X+1,Polynomial.X] (f.homogenize n) := by
  classical
  rw [Polynomial.homogenize, map_sum,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k _
  simp [MvPolynomial.aeval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two,
    mul_assoc]

lemma homogenize_transform (f : B[X]) (n : ℕ) (t : B) :
    (transform f n t).homogenize n=(forward t) (f.homogenize n) := by
  apply homogenize_eq_of_isHomogeneous (forward_homogeneous (isHomogeneous_homogenize f) t)
  have he : (MvPolynomial.aeval ![Polynomial.X,1]).comp (forward t) =
      MvPolynomial.aeval ![C t*Polynomial.X+1,Polynomial.X] := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [forward]
  rw [transform_eq_aeval]
  exact DFunLike.congr_fun he (f.homogenize n)

def normalized (f : B[X]) (n : ℕ) (t : B) (v : Bˣ) : B[X] :=
  C (↑v⁻¹ : B)*transform f n t

lemma normalized_top (f : B[X]) {n : ℕ} (t : B) (v : Bˣ)
    (hn : f.natDegree≤n) (hv : f.eval t=(v : B)) :
    (normalized f n t v).coeff n=1 := by
  rw [normalized,coeff_C_mul,transform_top f n t hn,hv]
  exact v.inv_mul

lemma normalized_monic (f : B[X]) {n : ℕ} (t : B) (v : Bˣ)
    (hn : f.natDegree≤n) (hv : f.eval t=(v : B)) :
    (normalized f n t v).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one n
  · exact (natDegree_C_mul_le _ _).trans (transform_degree f n t)
  · exact normalized_top f t v hn hv

lemma normalized_degree [Nontrivial B] (f : B[X]) {n : ℕ} (t : B) (v : Bˣ)
    (hn : f.natDegree≤n) (hv : f.eval t=(v : B)) :
    (normalized f n t v).natDegree=n := by
  apply le_antisymm ((natDegree_C_mul_le _ _).trans (transform_degree f n t))
  apply le_natDegree_of_ne_zero
  change (normalized f n t v).coeff n≠0
  rw [normalized_top f t v hn hv]
  exact one_ne_zero

 

lemma binary_factorization (f : B[X]) (n : ℕ) (t : B) (v : Bˣ) (rs : Fin n → B)
    (hs : normalized f n t v=∏ i, (Polynomial.X-C (rs i))) :
    f.homogenize n=MvPolynomial.C (v : B)*∏ i,
      (MvPolynomial.C (-rs i)*MvPolynomial.X 0+
        MvPolynomial.C (1+t*rs i)*MvPolynomial.X 1) := by
  classical
  have hh : (normalized f n t v).homogenize n=
      ∏ i : Fin n, (MvPolynomial.X 0-MvPolynomial.C (rs i)*MvPolynomial.X 1) := by
    rw [hs]
    have hp := homogenize_finsetProd (s := Finset.univ) (p := fun i : Fin n => Polynomial.X-C (rs i))
      (n := fun _ => 1) (fun _ _ => natDegree_X_sub_C_le _)
    simpa using hp
  have hmul : C (v : B)*normalized f n t v=transform f n t := by
    simp [normalized,← mul_assoc,← C_mul]
  have hc := congrArg (fun p : B[X] => p.homogenize n) hmul
  rw [homogenize_C_mul,hh,homogenize_transform] at hc
  have hb := congrArg (backward t) hc
  have hinv : (backward t) ((forward t) (f.homogenize n))=f.homogenize n :=
    DFunLike.congr_fun (backward_forward t) (f.homogenize n)
  rw [hinv] at hb
  rw [← hb]
  simp only [map_mul,map_prod]
  congr 1
  · simp [backward]
  · apply Finset.prod_congr rfl
    intro i _
    simp only [map_sub,map_mul,backward,MvPolynomial.aeval_X,MvPolynomial.aeval_C,
      Matrix.cons_val_zero,Matrix.cons_val_one,
      MvPolynomial.C_neg,MvPolynomial.C_add,map_one,MvPolynomial.algebraMap_eq]
    ring

lemma factor_pair_unimodular (t r : B) :
    Ideal.span ({-r,1+t*r} : Set B)=⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h₁ : -r∈Ideal.span ({-r,1+t*r} : Set B) := Ideal.subset_span (by simp)
  have h₂ : 1+t*r∈Ideal.span ({-r,1+t*r} : Set B) := Ideal.subset_span (by simp)
  have h := Ideal.add_mem _ h₂ (Ideal.mul_mem_left _ t h₁)
  simpa using h

end Lech.BinaryChange


namespace Lech.BinaryCover
open Polynomial
universe u

lemma ordered_splitting_of_top (R : Type u) [CommRing R] (n : ℕ) (g : R[X])
    (hn : g.natDegree≤n) (ht : g.coeff n=1) :
    Nonempty (UniversalSplitting.Data R n g) := by
  cases subsingleton_or_nontrivial R with
  | inr h =>
    apply UniversalSplitting.exists_data n R g
    · exact monic_of_natDegree_le_of_coeff_eq_one n hn ht
    · apply le_antisymm hn
      apply le_natDegree_of_ne_zero
      rw [ht]
      exact one_ne_zero
  | inl h =>
    refine ⟨{
      S := R
      basis := Module.Basis.ofRepr (LinearEquiv.ofSubsingleton R (Fin n.factorial →₀ R))
      roots := fun _ => 0
      factorization := Subsingleton.elim _ _
      universal := ?_ }⟩
    intro T _ _ xs _
    have : Subsingleton T := Module.subsingleton R T
    refine ⟨Algebra.ofId R T,fun _ => Subsingleton.elim _ _,?_⟩
    intro φ _
    exact Subsingleton.elim _ _

lemma map_transform {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (f : A[X]) (n : ℕ) (t : A) :
    (BinaryChange.transform f n t).map φ=
      BinaryChange.transform (f.map φ) n (φ t) := by
  simp [BinaryChange.transform,Polynomial.map_sum]

lemma map_normalized {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (f : A[X]) (n : ℕ) (t : A) (v : Aˣ) :
    (BinaryChange.normalized f n t v).map φ=
      BinaryChange.normalized (f.map φ) n (φ t) (Units.map φ v) := by
  simp [BinaryChange.normalized,map_transform]

 

structure Data (A : Type u) [CommRing A] (n : ℕ) (f : A[X]) where
  S : Type u
  [ring : CommRing S]
  [algebra : Algebra A S]
  [chartAlgebra : Algebra (Localization.Away f) S]
  [tower : IsScalarTower A (Localization.Away f) S]
  basis : Module.Basis (Fin n.factorial) (Localization.Away f) S
  faithfullyFlat : Module.FaithfullyFlat A S
  unit : Sˣ
  p : Fin n → S
  q : Fin n → S
  factorization : MvPolynomial.map (algebraMap A S) (f.homogenize n)=
    MvPolynomial.C (unit : S)*∏ i,
      (MvPolynomial.C (p i)*MvPolynomial.X 0+MvPolynomial.C (q i)*MvPolynomial.X 1)
  unimodular : ∀ i, Ideal.span ({p i,q i} : Set S)=⊤
attribute [instance] Data.ring Data.algebra Data.chartAlgebra Data.tower

theorem exists_data (A : Type u) [CommRing A] (n : ℕ) (f : A[X])
    (hn : f.natDegree≤n) (hf : Ideal.span (Set.range f.coeff)=⊤) :
    Nonempty (Data A n f) := by
  let B := Localization.Away f
  let : Module.FaithfullyFlat A B := PrimitiveChart.faithfullyFlat_away f hf
  let t : B := algebraMap A[X] B Polynomial.X
  let fB : B[X] := f.map (algebraMap A B)
  have heval : fB.eval t=algebraMap A[X] B f := by
    rw [Polynomial.eval_map]
    have he : eval₂RingHom (algebraMap A B) t=algebraMap A[X] B := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [coe_eval₂RingHom,eval₂_C]
        exact IsScalarTower.algebraMap_apply A A[X] B a
      · simp [t]
    exact DFunLike.congr_fun he f
  obtain ⟨v,hv⟩ := IsLocalization.Away.algebraMap_isUnit (S := B) f
  have hval : fB.eval t=(v : B) := heval.trans hv.symm
  have hdeg : fB.natDegree≤n := natDegree_map_le.trans hn
  let g := BinaryChange.normalized fB n t v
  have hgn : g.natDegree≤n :=
    (natDegree_C_mul_le _ _).trans (BinaryChange.transform_degree fB n t)
  have hgt : g.coeff n=1 := BinaryChange.normalized_top fB t v hdeg hval
  obtain ⟨d⟩ := ordered_splitting_of_top B n g hgn hgt
  let : Algebra A d.S := ((algebraMap B d.S).comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun a => rfl
  let : Nonempty (Fin n.factorial) := ⟨⟨0,Nat.factorial_pos n⟩⟩
  let : Module.FaithfullyFlat B d.S := Module.FaithfullyFlat.of_linearEquiv _ _ d.basis.repr
  have hflat : Module.FaithfullyFlat A d.S := Module.FaithfullyFlat.trans A B d.S
  let w : d.Sˣ := Units.map (algebraMap B d.S) v
  let u : d.S := algebraMap B d.S t
  have hroots : BinaryChange.normalized (f.map (algebraMap A d.S)) n u w=
      ∏ i, (Polynomial.X-C (d.roots i)) := by
    have hh := d.factorization
    change (BinaryChange.normalized fB n t v).map (algebraMap B d.S)=_ at hh
    rw [map_normalized] at hh
    simpa only [fB,Polynomial.map_map,← IsScalarTower.algebraMap_eq A B d.S] using hh
  refine ⟨{
    S := d.S
    basis := d.basis
    faithfullyFlat := hflat
    unit := w
    p := fun i => -d.roots i
    q := fun i => 1+u*d.roots i
    factorization := ?_
    unimodular := fun i => BinaryChange.factor_pair_unimodular u (d.roots i) }⟩
  rw [← Polynomial.homogenize_map]
  exact BinaryChange.binary_factorization _ n u w d.roots hroots

end Lech.BinaryCover


namespace Lech.RootTransitions
open Polynomial
universe u
variable {B : Type u} [CommRing B]

lemma value_product (f : B[X]) {n : ℕ} (hn : f.natDegree≤n)
    (t u : B) (v : Bˣ) (rs : Fin n → B)
    (hs : BinaryChange.normalized f n t v=∏ i, (Polynomial.X-C (rs i))) :
    f.eval u=(v:B)*∏ i, (1+(t-u)*rs i) := by
  classical
  have h := congrArg (MvPolynomial.aeval ![u,1])
    (BinaryChange.binary_factorization f n t v rs hs)
  rw [aeval_homogenize_of_eq_one hn ![u,1] (by simp)] at h
  have h' : f.eval u=(v:B)*∏ i, (-rs i*u+(1+t*rs i)) := by
    simpa using h
  rw [h']
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring

lemma denominator_isUnit (f : B[X]) {n : ℕ} (hn : f.natDegree≤n)
    (t u : B) (v w : Bˣ) (rs : Fin n → B)
    (hs : BinaryChange.normalized f n t v=∏ i, (Polynomial.X-C (rs i)))
    (hw : f.eval u=(w:B)) (i : Fin n) : IsUnit (1+(t-u)*rs i) := by
  have h := value_product f hn t u v rs hs
  rw [hw] at h
  have hp : IsUnit ((v:B)*∏ i, (1+(t-u)*rs i)) := h ▸ w.isUnit
  exact IsUnit.prod_univ_iff.mp (isUnit_of_mul_isUnit_right hp) i

lemma linear_shift (t u r : B) (d : Bˣ) (hd : (d:B)=1+(t-u)*r) :
    C (-r)*(C u*Polynomial.X+1)+C (1+t*r)*Polynomial.X=
      C (d:B)*(Polynomial.X-C (r*(↑d⁻¹:B))) := by
  have hc : (d:B)*(r*(↑d⁻¹:B))=r := by
    rw [mul_left_comm,d.mul_inv,mul_one]
  rw [mul_sub,← C_mul,hc,hd]
  simp only [map_neg,map_add,map_sub,map_mul,map_one]
  ring

lemma normalized_shift (f : B[X]) {n : ℕ} (hn : f.natDegree≤n)
    (t u : B) (v w : Bˣ) (rs : Fin n → B) (ds : Fin n → Bˣ)
    (hd : ∀ i, (ds i:B)=1+(t-u)*rs i)
    (hs : BinaryChange.normalized f n t v=∏ i, (Polynomial.X-C (rs i)))
    (hw : f.eval u=(w:B)) :
    BinaryChange.normalized f n u w=
      ∏ i, (Polynomial.X-C (rs i*(↑(ds i)⁻¹:B))) := by
  have hprod : (w:B)=(v:B)*∏ i, (ds i:B) := by
    rw [← hw,value_product f hn t u v rs hs]
    simp only [hd]
  have h := congrArg (MvPolynomial.aeval ![C u*Polynomial.X+1,Polynomial.X])
    (BinaryChange.binary_factorization f n t v rs hs)
  rw [← BinaryChange.transform_eq_aeval] at h
  have htrans : BinaryChange.transform f n u=
      C (v:B)*∏ i, (C (-rs i)*(C u*Polynomial.X+1)+C (1+t*rs i)*Polynomial.X) := by
    simpa using h
  rw [BinaryChange.normalized,htrans]
  simp_rw [linear_shift t u _ _ (hd _)]
  rw [Finset.prod_mul_distrib,← map_prod,← mul_assoc,← mul_assoc,← C_mul,← C_mul]
  rw [mul_assoc,← hprod,w.inv_mul,C_1,one_mul]

end Lech.RootTransitions


namespace Lech.RootGluing
open Polynomial
universe u
variable {B : Type u} [CommRing B]

def rootShift (a x : B) : B := x*Ring.inverse (1+a*x)

lemma map_inverse {C : Type u} [CommRing C] (φ : B →+* C) (x : B) (hx : IsUnit x) :
    φ (Ring.inverse x)=Ring.inverse (φ x) := by
  obtain ⟨v,rfl⟩ := hx
  rw [Ring.inverse_unit]
  change (((Units.map φ.toMonoidHom v)⁻¹ : Cˣ) : C)=Ring.inverse (↑(Units.map φ.toMonoidHom v))
  exact (Ring.inverse_unit _).symm

lemma map_rootShift {C : Type u} [CommRing C] (φ : B →+* C) (a x : B)
    (hx : IsUnit (1+a*x)) :
    φ (rootShift a x)=rootShift (φ a) (φ x) := by
  rw [rootShift,map_mul,map_inverse φ _ hx]
  simp only [map_add,map_one,map_mul,rootShift]

lemma reverse_denominator (a x : B) (d : Bˣ) (hd : (d:B)=1+a*x) :
    1-a*(x*(↑d⁻¹:B))=(↑d⁻¹:B) := by
  calc
    1-a*(x*(↑d⁻¹:B))=((d:B)-a*x)*(↑d⁻¹:B) := by
      rw [sub_mul,d.mul_inv]
      ring
    _ = (↑d⁻¹:B) := by rw [hd]; ring

lemma rootShift_reverse (a x : B) (hx : IsUnit (1+a*x)) :
    rootShift (-a) (rootShift a x)=x := by
  obtain ⟨d,hd⟩ := hx
  have he := reverse_denominator a x d hd
  simp only [rootShift,← hd,Ring.inverse_unit]
  rw [show 1+ -a*(x*(↑d⁻¹:B))=(↑d⁻¹:B) by simpa only [neg_mul,← sub_eq_add_neg] using he,
    Ring.inverse_unit,inv_inv,mul_assoc,d.inv_mul,mul_one]

lemma normalized_shift (f : B[X]) {n : ℕ} (hn : f.natDegree≤n)
    (t u : B) (v w : Bˣ) (rs : Fin n → B)
    (hs : BinaryChange.normalized f n t v=∏ i, (Polynomial.X-C (rs i)))
    (hw : f.eval u=(w:B)) :
    BinaryChange.normalized f n u w=∏ i, (Polynomial.X-C (rootShift (t-u) (rs i))) := by
  let ds : Fin n → Bˣ := fun i =>
    (RootTransitions.denominator_isUnit f hn t u v w rs hs hw i).unit
  have hd (i) : (ds i:B)=1+(t-u)*rs i := IsUnit.unit_spec _
  have hh := RootTransitions.normalized_shift f hn t u v w rs ds hd hs hw
  simpa only [rootShift,← Ring.inverse_unit,hd] using hh

lemma denominator_comp (a b x : B) (d : Bˣ) (hd : (d:B)=1+a*x) :
    1+b*(x*(↑d⁻¹:B))=(1+(a+b)*x)*(↑d⁻¹:B) := by
  calc
    1+b*(x*(↑d⁻¹:B))=((d:B)+b*x)*(↑d⁻¹:B) := by rw [add_mul,d.mul_inv]; ring
    _ = (1+(a+b)*x)*(↑d⁻¹:B) := by rw [hd]; ring
lemma rootShift_comp (a b x : B) (ha : IsUnit (1+a*x))
    (hab : IsUnit (1+(a+b)*x)) :
    rootShift b (rootShift a x)=rootShift (a+b) x := by
  obtain ⟨d,hd⟩ := ha
  obtain ⟨e,he⟩ := hab
  have hden := denominator_comp a b x d hd
  simp only [rootShift,← hd,Ring.inverse_unit]
  rw [hden,← he]
  change x*(↑d⁻¹:B)*Ring.inverse ((e*d⁻¹:Bˣ):B)=x*Ring.inverse (e:B)
  rw [Ring.inverse_unit,Ring.inverse_unit]
  simp only [mul_inv_rev,inv_inv,Units.val_mul]
  calc
    x*(↑d⁻¹:B)*((d:B)*(↑e⁻¹:B))=x*((↑d⁻¹:B)*(d:B))*(↑e⁻¹:B) := by ring
    _ = x*(↑e⁻¹:B) := by rw [d.inv_mul,mul_one]
lemma denominator_comp_isUnit (a b x : B) (ha : IsUnit (1+a*x))
    (hab : IsUnit (1+(a+b)*x)) : IsUnit (1+b*rootShift a x) := by
  obtain ⟨d,hd⟩ := ha
  simp only [rootShift,← hd,Ring.inverse_unit]
  rw [denominator_comp a b x d hd]
  exact hab.mul d⁻¹.isUnit

variable (f : B[X]) (n : ℕ) (hn : f.natDegree≤n)
  (t u : B) (v w : Bˣ) (hv : f.eval t=(v:B)) (hw : f.eval u=(w:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized f n t v))
  (e : UniversalSplitting.Data B n (BinaryChange.normalized f n u w))

lemma mapped_factorization :
    BinaryChange.normalized (f.map (algebraMap B d.S)) n (algebraMap B d.S t)
      (Units.map (algebraMap B d.S) v)=∏ i, (Polynomial.X-C (d.roots i)) := by
  rw [← BinaryCover.map_normalized]
  exact d.factorization

include hw in
lemma mapped_value : (f.map (algebraMap B d.S)).eval (algebraMap B d.S u)=
    ((Units.map (algebraMap B d.S) w : d.Sˣ) : d.S) := by
  rw [Polynomial.eval_map,eval₂_at_apply,hw]
  rfl

include hn w hw in
lemma denominator_unit (i : Fin n) :
    IsUnit (1+(algebraMap B d.S (t-u))*d.roots i) := by
  simpa only [map_sub] using RootTransitions.denominator_isUnit
    (f.map (algebraMap B d.S)) (natDegree_map_le.trans hn)
    (algebraMap B d.S t) (algebraMap B d.S u)
    (Units.map (algebraMap B d.S) v) (Units.map (algebraMap B d.S) w)
    d.roots (mapped_factorization f n t v d) (mapped_value f n t u v w hw d) i

include hn hw in
lemma shifted_factorization :
    (BinaryChange.normalized f n u w).map (algebraMap B d.S)=
      ∏ i, (Polynomial.X-C (rootShift (algebraMap B d.S (t-u)) (d.roots i))) := by
  rw [BinaryCover.map_normalized]
  simpa only [map_sub] using normalized_shift (f.map (algebraMap B d.S))
    (natDegree_map_le.trans hn) (algebraMap B d.S t) (algebraMap B d.S u)
    (Units.map (algebraMap B d.S) v) (Units.map (algebraMap B d.S) w)
    d.roots (mapped_factorization f n t v d) (mapped_value f n t u v w hw d)

 

def hom : e.S →ₐ[B] d.S :=
  (e.universal d.S (fun i => rootShift (algebraMap B d.S (t-u)) (d.roots i))
    (shifted_factorization f n hn t u v w hw d)).choose

lemma hom_root (i : Fin n) : hom f n hn t u v w hw d e (e.roots i)=
    rootShift (algebraMap B d.S (t-u)) (d.roots i) :=
  (e.universal d.S (fun i => rootShift (algebraMap B d.S (t-u)) (d.roots i))
    (shifted_factorization f n hn t u v w hw d)).choose_spec.1 i

lemma hom_comp :
    (hom f n hn t u v w hw d e).comp (hom f n hn u t w v hv e d)=AlgHom.id B d.S := by
  apply d.hom_ext
  intro i
  rw [AlgHom.comp_apply,hom_root]
  change (hom f n hn t u v w hw d e).toRingHom
    (rootShift (algebraMap B e.S (u-t)) (e.roots i)) = d.roots i
  rw [map_rootShift (hom f n hn t u v w hw d e).toRingHom _ _
    (denominator_unit f n hn u t w v hv e i)]
  change rootShift ((hom f n hn t u v w hw d e) (algebraMap B e.S (u-t)))
    ((hom f n hn t u v w hw d e) (e.roots i))=d.roots i
  rw [AlgHom.commutes,hom_root]
  rw [show algebraMap B d.S (u-t) = -algebraMap B d.S (t-u) by rw [← map_neg]; congr 1; ring]
  exact rootShift_reverse _ _ (denominator_unit f n hn t u v w hw d i)

 

def equiv : e.S ≃ₐ[B] d.S :=
  AlgEquiv.ofAlgHom (hom f n hn t u v w hw d e) (hom f n hn u t w v hv e d)
    (hom_comp f n hn t u v w hv hw d e) (hom_comp f n hn u t w v hw hv e d)

 
lemma hom_cocycle (s : B) (z : Bˣ) (hz : f.eval s=(z:B))
    (c : UniversalSplitting.Data B n (BinaryChange.normalized f n s z)) :
    (hom f n hn t u v w hw d e).comp (hom f n hn u s w z hz e c)=
      hom f n hn t s v z hz d c := by
  apply c.hom_ext
  intro i
  rw [AlgHom.comp_apply,hom_root,hom_root]
  change (hom f n hn t u v w hw d e).toRingHom
    (rootShift (algebraMap B e.S (u-s)) (e.roots i)) = _
  rw [map_rootShift (hom f n hn t u v w hw d e).toRingHom _ _
    (denominator_unit f n hn u s w z hz e i)]
  change rootShift ((hom f n hn t u v w hw d e) (algebraMap B e.S (u-s)))
    ((hom f n hn t u v w hw d e) (e.roots i))=_
  rw [AlgHom.commutes,hom_root]
  have hab : algebraMap B d.S (t-u)+algebraMap B d.S (u-s)=
      algebraMap B d.S (t-s) := by rw [← map_add]; congr 1; ring
  rw [rootShift_comp _ _ _ (denominator_unit f n hn t u v w hw d i)
    (by rw [hab]; exact denominator_unit f n hn t s v z hz d i),hab]

end Lech.RootGluing
end

end OAI
