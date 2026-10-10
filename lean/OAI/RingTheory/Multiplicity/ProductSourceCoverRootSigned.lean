import Mathlib
import OAI.RingTheory.Multiplicity.LechQuotientScalar

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
namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open scoped BigOperators
universe u
variable {C : Type u} [CommRing C] (I : Ideal C) (ℓ : TorsionLength I)
variable (n : ℕ) [LinearOrder (Chart n)]
omit [LinearOrder (Chart n)] in
lemma root_signedRank_real (r : Fin n → ℤ) (a : ℤ) :
    (-1:ℝ)^rootDegree n r a*(signedRank (fun j => a-1-r j):ℝ)=∏ j,((a-r j:ℤ):ℝ) := by
  have he := congrArg (fun z : ℤ => (z:ℝ)) (signedRank_euler n (fun j => a-1-r j))
  push_cast at he
  simp only [negativeCount_root] at he
  change (-1:ℝ)^rootDegree n r a*(signedRank (fun j => a-1-r j):ℝ)=_ at he
  convert he using 1
  apply Finset.prod_congr rfl
  intro j _
  push_cast
  ring
lemma rootLayerTerm_euler_polynomial (r : Fin n → ℤ) (s : ℕ) (l : ℤ) (b : ℕ → ℕ)
    (hμ : ℓ.value (ModuleCat.of C (C ⧸ I))≠⊤) (k : ℕ) (hk : k≤n+1) :
    finiteHomologyEuler (quotientLength I ℓ)
      (rootLayerTerm (C ⧸ I) n r s l b (-(n+1:ℤ)+k)) (-(k:ℤ)) (2*n+1)=
    (-1:ℝ)^k*(b (n+1-k):ℝ)*(ℓ.value (ModuleCat.of C (C ⧸ I))).toReal*
      ∏ j,((l-(n+1-k:ℕ)*(s:ℤ)-r j:ℤ):ℝ) := by
  have hj : -(n+1:ℤ)≤-(n+1:ℤ)+k ∧ -(n+1:ℤ)+k≤0 := by omega
  have hi : (-(-(n+1:ℤ)+k)).toNat=n+1-k := by omega
  rw [rootLayerTerm,ite_eq_left hj,hi]
  let a : ℤ := l-(n+1-k:ℕ)*(s:ℤ)
  have hd := rootDegree_le n r a
  have hfl (q : ℤ) : (quotientLength I ℓ).finiteClass ((rootTwistRow (C ⧸ I) n r a).homology q) :=
    (quotientLength_finite_iff I ℓ _).mpr (rootTwistRow_quotientFinite I ℓ n r a q hμ)
  rw [ComplexPi.copies_euler _ _ _ _ _ hfl
    (rootTwistRow_isZero (C ⧸ I) n r a _ (by omega))
    (rootTwistRow_isZero (C ⧸ I) n r a _ (by omega))]
  rw [rootTwistRow_euler I ℓ n r a (-(k:ℤ)) (2*n+1) (by omega) (by omega)]
  have he : ((rootDegree n r a:ℤ)-(-(k:ℤ))).toNat=rootDegree n r a+k := by omega
  rw [he,pow_add]
  calc
    _=(-1:ℝ)^k*(b (n+1-k):ℝ)*(ℓ.value (ModuleCat.of C (C ⧸ I))).toReal*
        ((-1:ℝ)^rootDegree n r a*(signedRank (fun j => a-1-r j):ℝ)) := by ring
    _=_ := by rw [root_signedRank_real]
variable (r : Fin n → ℤ) (s : ℕ) (l : ℤ) (b : ℕ → ℕ)
variable (d : ∀ j:ℤ,rootLayerTerm (C ⧸ I) n r s l b j ⟶ rootLayerTerm (C ⧸ I) n r s l b (j+1))
variable (hd : ∀ j:ℤ,d j ≫ d (j+1)=0)
 

theorem rootLayerTotal_euler_polynomial (hμ : ℓ.value (ModuleCat.of C (C ⧸ I))≠⊤) :
    (-1:ℝ)^(n+1)*finiteHomologyEuler (quotientLength I ℓ)
      (total (rootLayerDouble (C ⧸ I) n r s l b d hd) (.up ℤ)) (-(n+1:ℤ)) (2*n+1)=
    (ℓ.value (ModuleCat.of C (C ⧸ I))).toReal *
      ∑ i ∈ Finset.range (n+2),(-1:ℝ)^i*(b i:ℝ)*∏ j,((l-(i:ℤ)*(s:ℤ)-r j:ℤ):ℝ) := by
  rw [rootLayerTotal_euler_rows I ℓ n r s l b d hd hμ,Finset.mul_sum]
  calc
    _=∑ k ∈ Finset.range (n+2),(-1:ℝ)^(n+1)*
        ((-1:ℝ)^k*(b (n+1-k):ℝ)*(ℓ.value (ModuleCat.of C (C ⧸ I))).toReal*
          ∏ j,((l-(n+1-k:ℕ)*(s:ℤ)-r j:ℤ):ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [rootLayerTerm_euler_polynomial I ℓ n r s l b hμ k (by have:=Finset.mem_range.mp hk;omega)]
    _=_ := by
      rw [Finset.mul_sum]
      rw [←Finset.sum_range_reflect (fun i => (ℓ.value (ModuleCat.of C (C ⧸ I))).toReal*
        ((-1:ℝ)^i*(b i:ℝ)*∏ j,((l-(i:ℤ)*(s:ℤ)-r j:ℤ):ℝ))) (n+2)]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k≤n+1 := by have:=Finset.mem_range.mp hk;omega
      have he : n+2-1-k=n+1-k := by omega
      rw [he]
      have hs : (-1:ℝ)^(n+1)*(-1:ℝ)^k=(-1:ℝ)^(n+1-k) := by
        conv_lhs => rw [show n+1=(n+1-k)+k by omega,pow_add]
        have hsq : (-1:ℝ)^k*(-1:ℝ)^k=1 := by rw [←mul_pow];norm_num
        rw [mul_assoc,hsq,mul_one]
      calc
        _=((-1:ℝ)^(n+1)*(-1:ℝ)^k)*(b (n+1-k):ℝ)*
            (ℓ.value (ModuleCat.of C (C ⧸ I))).toReal*∏ j,((l-(n+1-k:ℕ)*(s:ℤ)-r j:ℤ):ℝ) := by ring
        _=_ := by rw [hs];ring
end Lech.ProductSourceCover


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators ZeroObject
universe u
variable {R : Type u} [CommRing R]
lemma biprod_homology_property (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ)
    (hK : P (K.homology q)) (hL : P (L.homology q)) :
    P ((K ⊞ L).homology q) := by
  exact P.prop_X₂_of_shortExact
    ((ShortComplex.Splitting.ofHasBinaryBiproduct K L).map
      (homologyFunctor (ModuleCat.{u} R) (.up ℤ) q)).shortExact hK hL
lemma biprod_homology_euler {I : Ideal R} (ℓ : TorsionLength I)
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (z : ℤ) (w : ℕ)
    (hK : ∀ q,ℓ.finiteClass (K.homology q)) (hL : ∀ q,ℓ.finiteClass (L.homology q)) :
    finiteHomologyEuler ℓ (K ⊞ L) z w=
      finiteHomologyEuler ℓ K z w+finiteHomologyEuler ℓ L z w := by
  unfold finiteHomologyEuler
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have he := ℓ.additive_real
    ((ShortComplex.Splitting.ofHasBinaryBiproduct K L).map
      (homologyFunctor (ModuleCat.{u} R) (.up ℤ) (z+i))).shortExact
    (biprod_homology_property ℓ.finiteClass K L (z+i) (hK _) (hL _))
  change ℓ.realValue ((K ⊞ L).homology (z+i))=
    ℓ.realValue (K.homology (z+i))+ℓ.realValue (L.homology (z+i)) at he
  rw [he,mul_add]
end Lech


namespace Lech.ProductSourceCover

section

section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators ZeroObject
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
 

def rootIntervalRow (r : Fin n → ℤ) (a : ℤ) : ℕ → BicomplexTotal.Row (R:=R)
  | 0 => 0
  | t+1 => rootIntervalRow r a t ⊞ rootTwistRow R n r (a+t)
omit [LinearOrder (Chart n)] in
lemma rootIntervalRow_property (r : Fin n → ℤ) (a : ℤ) (t : ℕ)
    (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass] (q : ℤ)
    (h : ∀ k<t,P ((rootTwistRow R n r (a+k)).homology q)) :
    P ((rootIntervalRow R n r a t).homology q) := by
  induction t with
  | zero =>
    exact P.prop_of_isZero
      ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).map_isZero (isZero_zero _))
  | succ t ih =>
    exact biprod_homology_property P _ _ q (ih (fun k hk => h k (by omega))) (h t (by omega))
lemma rootIntervalRow_isZero (r : Fin n → ℤ) (a : ℤ) (t : ℕ) (q : ℤ)
    (hq : q < 0 ∨ (n:ℤ)<q) : IsZero ((rootIntervalRow R n r a t).homology q) := by
  apply rootIntervalRow_property R n r a t (IsZero (C:=ModuleCat.{u} R)) q
  intro k _
  apply rootTwistRow_isZero
  have := rootDegree_le n r (a+k)
  omega
variable {C : Type u} [CommRing C] (I : Ideal C) (ℓ : TorsionLength I)
lemma rootIntervalRow_finite (r : Fin n → ℤ) (a : ℤ) (t : ℕ) (q : ℤ)
    (hμ : ℓ.value (ModuleCat.of C (C ⧸ I))≠⊤) :
    (quotientLength I ℓ).finiteClass ((rootIntervalRow (C ⧸ I) n r a t).homology q) := by
  apply rootIntervalRow_property (C ⧸ I) n r a t (quotientLength I ℓ).finiteClass q
  intro k _
  exact (quotientLength_finite_iff I ℓ _).mpr (rootTwistRow_quotientFinite I ℓ n r (a+k) q hμ)
lemma rootTwistRow_euler_natShift (r : Fin n → ℤ) (a : ℤ) (k w : ℕ) (hw : n+k≤w) :
    finiteHomologyEuler (quotientLength I ℓ) (rootTwistRow (C ⧸ I) n r a) (-(k:ℤ)) w=
      (-1:ℝ)^k*(ℓ.value (ModuleCat.of C (C ⧸ I))).toReal*∏ j,((a-r j:ℤ):ℝ) := by
  have hd := rootDegree_le n r a
  rw [rootTwistRow_euler I ℓ n r a (-(k:ℤ)) w (by omega) (by omega)]
  have he : ((rootDegree n r a:ℤ)-(-(k:ℤ))).toNat=rootDegree n r a+k := by omega
  rw [he,pow_add]
  calc
    _=(-1:ℝ)^k*(ℓ.value (ModuleCat.of C (C ⧸ I))).toReal*
        ((-1:ℝ)^rootDegree n r a*(signedRank (fun j => a-1-r j):ℝ)) := by ring
    _=_ := by rw [root_signedRank_real]
lemma rootIntervalRow_euler (r : Fin n → ℤ) (a : ℤ) (t k w : ℕ) (hw : n+k≤w)
    (hμ : ℓ.value (ModuleCat.of C (C ⧸ I))≠⊤) :
    finiteHomologyEuler (quotientLength I ℓ) (rootIntervalRow (C ⧸ I) n r a t) (-(k:ℤ)) w=
      (-1:ℝ)^k*(ℓ.value (ModuleCat.of C (C ⧸ I))).toReal*
        ∑ l ∈ Finset.range t,∏ j,((a+(l:ℤ)-r j:ℤ):ℝ) := by
  induction t with
  | zero =>
    simp only [Finset.range_zero,Finset.sum_empty,mul_zero]
    apply finiteHomologyEuler_zero
    intro q
    exact (homologyFunctor (ModuleCat.{u} (C ⧸ I)) (.up ℤ) q).map_isZero (isZero_zero _)
  | succ t ih =>
    rw [rootIntervalRow,biprod_homology_euler _ _ _ _ _
      (fun q => rootIntervalRow_finite n I ℓ r a t q hμ)
      (fun q => (quotientLength_finite_iff I ℓ _).mpr
        (rootTwistRow_quotientFinite I ℓ n r (a+t) q hμ)),ih,
      rootTwistRow_euler_natShift n I ℓ r (a+t) k w hw,Finset.sum_range_succ,mul_add]
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open scoped BigOperators Classical ZeroObject
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
 

def rootStripTerm (r : Fin n → ℤ) (s : ℕ) (b : ℕ → ℕ)
    (j : ℤ) : BicomplexTotal.Row (R:=R) :=
  if -(n+1:ℤ) ≤ j ∧ j ≤ 0 then
    ComplexPi.copies (Fin (b (-j).toNat))
      (rootIntervalRow R n r (-((-j).toNat*(s:ℤ))) ((-j).toNat*s))
  else 0
variable (r : Fin n → ℤ) (s : ℕ) (b : ℕ → ℕ)
variable (d : ∀ j:ℤ,rootStripTerm R n r s b j ⟶ rootStripTerm R n r s b (j+1))
variable (hd : ∀ j:ℤ,d j ≫ d (j+1)=0)
def rootStripDouble : BicomplexTotal.Double (R:=R) :=
  CochainComplex.of (rootStripTerm R n r s b) d hd
omit [LinearOrder (Chart n)] in
lemma rootStripDouble_bounded (j : ℤ) (hj : j < -(n+1:ℤ) ∨ 1 ≤ j) :
    IsZero ((rootStripDouble R n r s b d hd).X j) := by
  change IsZero (rootStripTerm R n r s b j)
  simp only [rootStripTerm,show ¬ (-(n+1:ℤ) ≤ j ∧ j≤0) by omega,ite_false]
  exact isZero_zero _
lemma rootStripTerm_isZero (j q : ℤ) (hq : q < 0 ∨ (n:ℤ)<q) :
    IsZero ((rootStripTerm R n r s b j).homology q) := by
  by_cases hj : -(n+1:ℤ)≤j ∧ j≤0
  · simp only [rootStripTerm,hj]
    apply ComplexPi.copies_homology_isZero
    exact rootIntervalRow_isZero R n r _ _ q hq
  · simp only [rootStripTerm,hj,ite_false]
    exact (homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).map_isZero (isZero_zero _)
variable {C : Type u} [CommRing C] (I : Ideal C) (ℓ : TorsionLength I)
lemma rootStripTerm_finite
    (hμ : ℓ.value (ModuleCat.of C (C ⧸ I))≠⊤) (j q : ℤ) :
    (quotientLength I ℓ).finiteClass ((rootStripTerm (C ⧸ I) n r s b j).homology q) := by
  by_cases hj : -(n+1:ℤ)≤j ∧ j≤0
  · simp only [rootStripTerm,hj]
    apply ComplexPi.copies_homology_property
    exact rootIntervalRow_finite n I ℓ r _ _ q hμ
  · simp only [rootStripTerm,hj,ite_false]
    exact (quotientLength I ℓ).finiteClass.prop_of_isZero
      ((homologyFunctor (ModuleCat.{u} (C ⧸ I)) (.up ℤ) q).map_isZero (isZero_zero _))
variable (δ : ∀ j:ℤ,rootStripTerm (C ⧸ I) n r s b j ⟶ rootStripTerm (C ⧸ I) n r s b (j+1))
variable (hδ : ∀ j:ℤ,δ j ≫ δ (j+1)=0)
 
theorem rootStripTotal_finite
    (hμ : ℓ.value (ModuleCat.of C (C ⧸ I))≠⊤) (k : ℤ) :
    (quotientLength I ℓ).finiteClass
      ((total (rootStripDouble (C ⧸ I) n r s b δ hδ) (.up ℤ)).homology k) := by
  apply BicomplexTotal.devissage (quotientLength I ℓ).finiteClass
    (-(n+1:ℤ)) (n+2) (rootStripDouble (C ⧸ I) n r s b δ hδ) k
  · intro j hj
    exact rootStripDouble_bounded (C ⧸ I) n r s b δ hδ j (by omega)
  intro j
  apply (quotientLength I ℓ).finiteClass.prop_of_iso (BicomplexTotal.singleHomologyIso
    ((rootStripDouble (C ⧸ I) n r s b δ hδ).X j) j k).symm
  exact rootStripTerm_finite n r s b I ℓ hμ j (-j+k)
 

theorem rootStripTotal_euler_rows (hμ : ℓ.value (ModuleCat.of C (C ⧸ I))≠⊤) :
    finiteHomologyEuler (quotientLength I ℓ)
      (total (rootStripDouble (C ⧸ I) n r s b δ hδ) (.up ℤ)) (-(n+1:ℤ)) (2*n+1)=
    ∑ k ∈ Finset.range (n+2),finiteHomologyEuler (quotientLength I ℓ)
      (rootStripTerm (C ⧸ I) n r s b (-(n+1:ℤ)+k)) (-(k:ℤ)) (2*n+1) := by
  have he := FiniteComplex.euler_devissage (quotientLength I ℓ) BicomplexTotal.functor
    BicomplexTotal.splitting (-(n+1:ℤ)) (2*n+1) (-(n+1:ℤ)) (n+2)
    (rootStripDouble (C ⧸ I) n r s b δ hδ)
    (by intro j hj;exact rootStripDouble_bounded (C ⧸ I) n r s b δ hδ j (by omega))
    (by
      intro j q
      exact (quotientLength I ℓ).finiteClass.prop_of_iso
        (BicomplexTotal.singleHomologyIso _ j q).symm
        (rootStripTerm_finite n r s b I ℓ hμ j (-j+q)))
    (by
      intro j
      apply IsZero.of_iso _ (BicomplexTotal.singleHomologyIso _ j _)
      by_cases hj : -(n+1:ℤ)≤j ∧ j≤0
      · exact rootStripTerm_isZero (C ⧸ I) n r s b j _ (by omega)
      · change IsZero ((rootStripTerm (C ⧸ I) n r s b j).homology _)
        simp only [rootStripTerm,hj,ite_false]
        exact (homologyFunctor (ModuleCat.{u} (C ⧸ I)) (.up ℤ) _).map_isZero (isZero_zero _))
    (by
      intro j
      apply IsZero.of_iso _ (BicomplexTotal.singleHomologyIso _ j _)
      by_cases hj : -(n+1:ℤ)≤j ∧ j≤0
      · exact rootStripTerm_isZero (C ⧸ I) n r s b j _ (by omega)
      · change IsZero ((rootStripTerm (C ⧸ I) n r s b j).homology _)
        simp only [rootStripTerm,hj,ite_false]
        exact (homologyFunctor (ModuleCat.{u} (C ⧸ I)) (.up ℤ) _).map_isZero (isZero_zero _))
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro k _
  change finiteHomologyEuler (quotientLength I ℓ)
    (total ((single (BicomplexTotal.Row (R:=C ⧸ I)) (.up ℤ) (-(n+1:ℤ)+k)).obj
      (rootStripTerm (C ⧸ I) n r s b (-(n+1:ℤ)+k))) (.up ℤ)) (-(n+1:ℤ)) (2*n+1)=_
  rw [single_euler]
  congr 1
  ring
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open scoped BigOperators
universe u
variable {C : Type u} [CommRing C] (I : Ideal C) (ℓ : TorsionLength I)
variable (n : ℕ) [LinearOrder (Chart n)]
 
def rootStripPolynomial (r : Fin n → ℤ) (i s : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (i*s),∏ j,((l:ℝ)-(i:ℝ)*(s:ℝ)-(r j:ℝ))
lemma rootStripTerm_euler_polynomial (r : Fin n → ℤ) (s : ℕ) (b : ℕ → ℕ)
    (hμ : ℓ.value (ModuleCat.of C (C ⧸ I))≠⊤) (k : ℕ) (hk : k≤n+1) :
    finiteHomologyEuler (quotientLength I ℓ)
      (rootStripTerm (C ⧸ I) n r s b (-(n+1:ℤ)+k)) (-(k:ℤ)) (2*n+1)=
    (-1:ℝ)^k*(b (n+1-k):ℝ)*(ℓ.value (ModuleCat.of C (C ⧸ I))).toReal*
      rootStripPolynomial n r (n+1-k) s := by
  have hj : -(n+1:ℤ)≤-(n+1:ℤ)+k ∧ -(n+1:ℤ)+k≤0 := by omega
  have hi : (-(-(n+1:ℤ)+k)).toNat=n+1-k := by omega
  rw [rootStripTerm,ite_eq_left hj,hi]
  let a : ℤ := -((n+1-k:ℕ)*(s:ℤ))
  let t : ℕ := (n+1-k)*s
  have hfl (q : ℤ) : (quotientLength I ℓ).finiteClass
      ((rootIntervalRow (C ⧸ I) n r a t).homology q) :=
    rootIntervalRow_finite n I ℓ r a t q hμ
  rw [ComplexPi.copies_euler _ _ _ _ _ hfl
    (rootIntervalRow_isZero (C ⧸ I) n r a t _ (by omega))
    (rootIntervalRow_isZero (C ⧸ I) n r a t _ (by omega))]
  rw [rootIntervalRow_euler n I ℓ r a t k (2*n+1) (by omega) hμ]
  have hp : (∑ z ∈ Finset.range t,∏ j,((a+(z:ℤ)-r j:ℤ):ℝ))=
      rootStripPolynomial n r (n+1-k) s := by
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.prod_congr rfl
    intro j _
    dsimp [a]
    push_cast
    ring
  rw [hp]
  ring
variable (r : Fin n → ℤ) (s : ℕ) (b : ℕ → ℕ)
variable (d : ∀ j:ℤ,rootStripTerm (C ⧸ I) n r s b j ⟶ rootStripTerm (C ⧸ I) n r s b (j+1))
variable (hd : ∀ j:ℤ,d j ≫ d (j+1)=0)
 

theorem rootStripTotal_euler_polynomial (hμ : ℓ.value (ModuleCat.of C (C ⧸ I))≠⊤) :
    (-1:ℝ)^(n+1)*finiteHomologyEuler (quotientLength I ℓ)
      (total (rootStripDouble (C ⧸ I) n r s b d hd) (.up ℤ)) (-(n+1:ℤ)) (2*n+1)=
    (ℓ.value (ModuleCat.of C (C ⧸ I))).toReal *
      ∑ i ∈ Finset.range (n+2),(-1:ℝ)^i*(b i:ℝ)*rootStripPolynomial n r i s := by
  rw [rootStripTotal_euler_rows n r s b I ℓ d hd hμ,Finset.mul_sum]
  calc
    _=∑ k ∈ Finset.range (n+2),(-1:ℝ)^(n+1)*
        ((-1:ℝ)^k*(b (n+1-k):ℝ)*(ℓ.value (ModuleCat.of C (C ⧸ I))).toReal*
          rootStripPolynomial n r (n+1-k) s) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [rootStripTerm_euler_polynomial I ℓ n r s b hμ k (by have:=Finset.mem_range.mp hk;omega)]
    _=_ := by
      rw [Finset.mul_sum]
      rw [←Finset.sum_range_reflect (fun i => (ℓ.value (ModuleCat.of C (C ⧸ I))).toReal*
        ((-1:ℝ)^i*(b i:ℝ)*rootStripPolynomial n r i s)) (n+2)]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k≤n+1 := by have:=Finset.mem_range.mp hk;omega
      have he : n+2-1-k=n+1-k := by omega
      rw [he]
      have hs : (-1:ℝ)^(n+1)*(-1:ℝ)^k=(-1:ℝ)^(n+1-k) := by
        conv_lhs => rw [show n+1=(n+1-k)+k by omega,pow_add]
        have hsq : (-1:ℝ)^k*(-1:ℝ)^k=1 := by rw [←mul_pow];norm_num
        rw [mul_assoc,hsq,mul_one]
      calc
        _=((-1:ℝ)^(n+1)*(-1:ℝ)^k)*(b (n+1-k):ℝ)*
            (ℓ.value (ModuleCat.of C (C ⧸ I))).toReal*rootStripPolynomial n r (n+1-k) s := by ring
        _=_ := by rw [hs];ring
end Lech.ProductSourceCover


namespace Lech.Homogeneous
open HomogeneousLocalization
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (G : ℕ → Submodule R A) [GradedAlgebra G]


instance algebra (U : Submonoid A) : Algebra R (HomogeneousLocalization G U) :=
  Algebra.ofModule
    (fun r x y => by
      apply val_injective U
      simp only [val_mul,val_smul]
      exact smul_mul_assoc r x.val y.val)
    (fun r x y => by
      apply val_injective U
      simp only [val_mul,val_smul]
      exact mul_smul_comm r x.val y.val)

@[simp] lemma val_algebraMap (U : Submonoid A) (r : R) :
    (algebraMap R (HomogeneousLocalization G U) r).val =
      algebraMap R (Localization U) r := by
  change (r • (1 : HomogeneousLocalization G U)).val = _
  rw [val_smul,val_one,Algebra.smul_def,mul_one]

instance scalarTower (U : Submonoid A) :
    IsScalarTower R (HomogeneousLocalization G U) (Localization U) :=
  IsScalarTower.of_algebraMap_eq' (R := R) (S := HomogeneousLocalization G U)
    (A := Localization U) (by ext r; exact (val_algebraMap G U r).symm)

end Lech.Homogeneous


namespace Lech.ProjectiveCoefficientChart
open MvPolynomial HomogeneousLocalization
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
attribute [local instance] MvPolynomial.gradedAlgebra
abbrev grading := homogeneousSubmodule (Fin (n+1)) R
abbrev Chart := Away (grading R n) (X k)
abbrev Ambient := Localization.Away (X (R:=R) k)
def coordinate (j : Fin (n+1)) : Chart R n k :=
  Away.mk (grading R n) (isHomogeneous_X R k) 1 (X j) (by simpa using isHomogeneous_X R j)
def forward : UniversalCoefficientChart.Ring R n k →ₐ[R] Chart R n k :=
  MvPolynomial.aeval (fun j => coordinate R n k j)
def evaluate : MvPolynomial (Fin (n+1)) R →ₐ[R] UniversalCoefficientChart.Ring R n k :=
  MvPolynomial.aeval (UniversalCoefficientChart.coefficient R n k)
def dehomogenize : Ambient R n k →ₐ[R] UniversalCoefficientChart.Ring R n k :=
  IsLocalization.Away.liftAlgHom (X k) (f:=evaluate R n k)
    (by simp [evaluate,UniversalCoefficientChart.coefficient_self])
def inclusion : Chart R n k →ₐ[R] Ambient R n k where
  toRingHom := algebraMap _ _
  commutes' r := Homogeneous.val_algebraMap (grading R n) (Submonoid.powers (X k)) r
def backward : Chart R n k →ₐ[R] UniversalCoefficientChart.Ring R n k :=
  (dehomogenize R n k).comp (inclusion R n k)
lemma coordinate_val (j : Fin (n+1)) :
    (coordinate R n k j).val=Localization.mk (X j) ⟨X k,by exact ⟨1,by simp⟩⟩ := by
  change Localization.mk (X j) ⟨X k ^ 1,by exact ⟨1,rfl⟩⟩ = _
  simp only [pow_one]
lemma backward_mk (d : ℕ) (p : MvPolynomial (Fin (n+1)) R)
    (hp : p∈grading R n (d • 1)) :
    backward R n k (Away.mk (grading R n) (isHomogeneous_X R k) d p hp)=evaluate R n k p := by
  change dehomogenize R n k (Localization.mk p ⟨X k ^ d,⟨d,rfl⟩⟩)=_
  have h : evaluate R n k (X k)*1=1 := by
    simp [evaluate,UniversalCoefficientChart.coefficient_self]
  convert (Localization.awayLift_mk (evaluate R n k).toRingHom (X k) p 1 h d) using 1
  · rfl
  · simp
lemma backward_coordinate (j : Fin (n+1)) :
    backward R n k (coordinate R n k j)=UniversalCoefficientChart.coefficient R n k j := by
  rw [coordinate,backward_mk]
  simp [evaluate]
lemma backward_forward (x : UniversalCoefficientChart.Ring R n k) :
    backward R n k (forward R n k x)=x := by
  have he : (backward R n k).comp (forward R n k)=AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa [forward] using (backward_coordinate R n k j).trans
      (UniversalCoefficientChart.coefficient_other R n k j)
  exact DFunLike.congr_fun he x
end Lech.ProjectiveCoefficientChart

end

end OAI
