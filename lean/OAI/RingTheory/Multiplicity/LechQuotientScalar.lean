import Mathlib
import OAI.RingTheory.Multiplicity.ProductSourceCoverCechNat

namespace OAI

section
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
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable {C : Type u} [CommRing C] (I : Ideal C) (ℓ : TorsionLength I)
abbrev quotientScalar (M : ModuleCat.{u} (C ⧸ I)) : ModuleCat.{u} C :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M
 

lemma basis_quotient_length (M : ModuleCat.{u} (C ⧸ I)) (r : ℕ)
    (b : Module.Basis (Fin r) (C ⧸ I) M) :
    ℓ.value (quotientScalar I M)=r • ℓ.value (ModuleCat.of C (C ⧸ I)) := by
  let e₀ : M ≃ₗ[C ⧸ I] (Fin r → C ⧸ I) :=
    b.repr.trans (Finsupp.linearEquivFunOnFinite (C ⧸ I) (C ⧸ I) (Fin r))
  let e := (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).mapIso e₀.toModuleIso
  have ht : powerTorsion I (quotientScalar I (ModuleCat.of (C ⧸ I) (Fin r → C ⧸ I))) := by
    change powerTorsion I (ModuleCat.of C (Fin r → C ⧸ I))
    exact powerTorsion_fin r powerTorsion_quotient
  exact (ℓ.eq_of_iso e ((powerTorsion I).prop_of_iso e.symm ht) ht).trans
    (ℓ.value_fin powerTorsion_quotient r)
 
def finiteTorsionCechEuler (K : CochainComplex (ModuleCat.{u} (C ⧸ I)) ℕ) (N : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (N+1), (-1:ℝ)^q * (ℓ.value (quotientScalar I (K.homology (q+1)))).toReal
lemma pureCohomology_length (K : CochainComplex (ModuleCat.{u} (C ⧸ I)) ℕ)
    (d r : ℕ) (h : PureCohomology (C ⧸ I) K d r) :
    ℓ.value (quotientScalar I (K.homology d))=r • ℓ.value (ModuleCat.of C (C ⧸ I)) := by
  obtain ⟨b⟩ := h.2
  exact basis_quotient_length I ℓ (K.homology d) r b
lemma pureCohomology_length_zero (K : CochainComplex (ModuleCat.{u} (C ⧸ I)) ℕ)
    (d r q : ℕ) (h : PureCohomology (C ⧸ I) K d r) (hq : q≠d) :
    ℓ.value (quotientScalar I (K.homology q))=0 :=
  ℓ.zero ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).map_isZero (h.1 q hq))
lemma pureCohomology_length_finite (K : CochainComplex (ModuleCat.{u} (C ⧸ I)) ℕ)
    (d r : ℕ) (h : PureCohomology (C ⧸ I) K d r)
    (hμ : ℓ.value (ModuleCat.of C (C ⧸ I))≠⊤) (q : ℕ) :
    ℓ.value (quotientScalar I (K.homology q))≠⊤ := by
  by_cases hq : q=d
  · subst q
    rw [pureCohomology_length I ℓ K d r h]
    rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top (by simp) hμ
  · rw [pureCohomology_length_zero I ℓ K d r q h hq]
    exact ENNReal.zero_ne_top
lemma pureCohomology_torsionEuler (K : CochainComplex (ModuleCat.{u} (C ⧸ I)) ℕ)
    (N d r : ℕ) (hd : d≤N) (h : PureCohomology (C ⧸ I) K (d+1) r) :
    finiteTorsionCechEuler I ℓ K N=(-1:ℝ)^d*(r:ℝ)*(ℓ.value (ModuleCat.of C (C ⧸ I))).toReal := by
  unfold finiteTorsionCechEuler
  rw [Finset.sum_eq_single d]
  · rw [pureCohomology_length I ℓ K (d+1) r h,ENNReal.toReal_nsmul]
    simp only [nsmul_eq_mul]
    ring
  · intro q _ hq
    rw [pureCohomology_length_zero I ℓ K (d+1) r (q+1) h (by omega)]
    simp
  · intro hd'
    exact (hd' (Finset.mem_range.mpr (by omega))).elim
end Lech


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable {C : Type u} [CommRing C] (I : Ideal C) (ℓ : TorsionLength I)
variable (n : ℕ) [LinearOrder (Chart n)]
 

theorem rootTarget_length_finite (r : Fin n → ℤ) (a : ℤ)
    (hμ : ℓ.value (ModuleCat.of C (C ⧸ I))≠⊤) (q : ℕ) :
    ℓ.value (quotientScalar I ((targetCech (C ⧸ I) n (fun j => a-1-r j)).homology (q+1)))≠⊤ :=
  pureCohomology_length_finite I ℓ _ _ _ (rootTarget_pure (C ⧸ I) n r a) hμ _
 

theorem rootTarget_torsionEuler (r : Fin n → ℤ) (a : ℤ) :
    finiteTorsionCechEuler I ℓ (targetCech (C ⧸ I) n (fun j => a-1-r j)) n=
      (ℓ.value (ModuleCat.of C (C ⧸ I))).toReal * ∏ j,((a-r j:ℤ):ℝ) := by
  rw [pureCohomology_torsionEuler I ℓ _ n (negativeCount (fun j => a-1-r j))
    (signedRank (fun j => a-1-r j)) (negativeCount_le _) (targetSigned_pure (C ⧸ I) n _)]
  have he := signedRank_euler n (fun j => a-1-r j)
  have he' : (-1:ℝ)^negativeCount (fun j => a-1-r j)*(signedRank (fun j => a-1-r j):ℝ)=
      ∏ j,((a-r j:ℤ):ℝ) := by
    have hc := congrArg (fun z : ℤ => (z:ℝ)) he
    push_cast at hc
    convert hc using 1
    apply Finset.prod_congr rfl
    intro j _
    push_cast
    ring
  rw [he']
  ring
end Lech.ProductSourceCover


namespace Lech.ComplexPi
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R]
variable (C : CochainComplex (ModuleCat.{u} R) ℤ)
def tailMap (n : ℕ) : copies (Fin (n+1)) C ⟶ copies (Fin n) C where
  f _q := ModuleCat.ofHom
    { toFun := fun x a => x a.succ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  comm' _ _ _ := rfl
def headMap (n : ℕ) : copies (Fin (n+1)) C ⟶ C where
  f _q := ModuleCat.ofHom
    { toFun := fun x => x 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  comm' _ _ _ := rfl
def consZeroMap (n : ℕ) : copies (Fin n) C ⟶ copies (Fin (n+1)) C where
  f q := ModuleCat.ofHom
    { toFun := fun x => Fin.cons 0 x
      map_add' := by intro x y;ext a;refine Fin.cases ?_ (fun a => ?_) a <;> simp
      map_smul' := by intro r x;ext a;refine Fin.cases ?_ (fun a => ?_) a <;> simp }
  comm' q t _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext a
    refine Fin.cases ?_ (fun a => ?_) a
    · exact (C.d q t).hom.map_zero
    · rfl
def consHeadMap (n : ℕ) : C ⟶ copies (Fin (n+1)) C where
  f q := ModuleCat.ofHom
    { toFun := fun x => Fin.cons x (fun _ => 0)
      map_add' := by intro x y;ext a;refine Fin.cases ?_ (fun a => ?_) a <;> simp
      map_smul' := by intro r x;ext a;refine Fin.cases ?_ (fun a => ?_) a <;> simp }
  comm' q t _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext a
    refine Fin.cases ?_ (fun a => ?_) a
    · rfl
    · exact (C.d q t).hom.map_zero

def copiesShortComplex (n : ℕ) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (consZeroMap C n) (headMap C n) (by
    apply Hom.ext;funext q;apply ModuleCat.hom_ext;apply LinearMap.ext;intro x;rfl)
def copiesSplitting (n : ℕ) : (copiesShortComplex C n).Splitting where
  r := tailMap C n
  s := consHeadMap C n
  f_r := by apply Hom.ext;funext q;apply ModuleCat.hom_ext;apply LinearMap.ext;intro x;rfl
  s_g := by apply Hom.ext;funext q;apply ModuleCat.hom_ext;apply LinearMap.ext;intro x;rfl
  id := by
    apply Hom.ext;funext q;apply ModuleCat.hom_ext;apply LinearMap.ext;intro x;funext a
    change Fin.cons (α := fun _ => C.X q) (0 : C.X q) (fun a : Fin n => (x a.succ : C.X q)) a+Fin.cons (α := fun _ => C.X q) (x 0 : C.X q) (fun _ : Fin n => (0 : C.X q)) a=x a
    refine Fin.cases ?_ (fun a => ?_) a <;> simp
lemma copies_zero_isZero : IsZero (copies (Fin 0) C) := by
  rw [IsZero.iff_id_eq_zero]
  apply Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change x=(0 : Fin 0 → C.X q)
  funext a
  exact Fin.elim0 a
 

lemma copies_homology_property (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (n : ℕ) (q : ℤ) (h : P (C.homology q)) : P ((copies (Fin n) C).homology q) := by
  induction n with
  | zero => exact P.prop_of_isZero ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).map_isZero
      (copies_zero_isZero C))
  | succ n ih => exact P.prop_X₂_of_exact ((copiesSplitting C n).shortExact.homology_exact₂ q) ih h
end Lech.ComplexPi


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {C : Type u} [CommRing C] (I : Ideal C) (ℓ : TorsionLength I)
 
lemma quotientScalar_powerTorsion (M : ModuleCat.{u} (C ⧸ I)) :
    powerTorsion I (quotientScalar I M) := by
  refine ⟨1,?_⟩
  rw [pow_one]
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  change (Ideal.Quotient.mk I r) • x=0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr,zero_smul]
def quotientFiniteClass : ObjectProperty (ModuleCat.{u} (C ⧸ I)) :=
  ℓ.finiteClass.inverseImage (ModuleCat.restrictScalars (Ideal.Quotient.mk I))
instance : (quotientFiniteClass I ℓ).IsSerreClass := inferInstanceAs
  ((ℓ.finiteClass).inverseImage (ModuleCat.restrictScalars (Ideal.Quotient.mk I))).IsSerreClass
end Lech


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open scoped BigOperators Classical ZeroObject
universe u
variable {C : Type u} [CommRing C] (I : Ideal C) (ℓ : TorsionLength I)
variable (n : ℕ) [LinearOrder (Chart n)]
lemma rootTwistRow_quotientFinite (r : Fin n → ℤ) (a q : ℤ)
    (hμ : ℓ.value (ModuleCat.of C (C ⧸ I))≠⊤) :
    quotientFiniteClass I ℓ ((rootTwistRow (C ⧸ I) n r a).homology q) := by
  apply (quotientFiniteClass I ℓ).prop_of_iso (rootTwistRowHomologyIso (C ⧸ I) n r a q).symm
  by_cases hp : 0 ≤ 1+q
  · obtain ⟨p,hp⟩ := Int.eq_ofNat_of_zero_le hp
    apply (quotientFiniteClass I ℓ).prop_of_iso
      ((targetCech (C ⧸ I) n (fun j => a-1-r j)).extendHomologyIso
      ComplexShape.embeddingUpNat (j:=p) (by exact hp.symm)).symm
    exact ⟨quotientScalar_powerTorsion I _,pureCohomology_length_finite I ℓ _ _ _
      (rootTarget_pure (C ⧸ I) n r a) hμ p⟩
  · apply (quotientFiniteClass I ℓ).prop_of_isZero
    apply HomologicalComplex.ExactAt.isZero_homology
    apply HomologicalComplex.extend_exactAt
    intro p hp'
    change (p:ℤ)=1+q at hp'
    omega
variable (r : Fin n → ℤ) (s : ℕ) (l : ℤ) (b : ℕ → ℕ)
variable (d : ∀ j:ℤ,rootLayerTerm (C ⧸ I) n r s l b j ⟶ rootLayerTerm (C ⧸ I) n r s l b (j+1))
variable (hd : ∀ j:ℤ,d j ≫ d (j+1)=0)
 

theorem rootLayerTotal_quotientFinite
    (hμ : ℓ.value (ModuleCat.of C (C ⧸ I))≠⊤) (k : ℤ) :
    quotientFiniteClass I ℓ
      ((total (rootLayerDouble (C ⧸ I) n r s l b d hd) (.up ℤ)).homology k) := by
  apply BicomplexTotal.devissage (quotientFiniteClass I ℓ)
    (-(n+1:ℤ)) (n+2) (rootLayerDouble (C ⧸ I) n r s l b d hd) k
  · intro j hj
    exact rootLayerDouble_bounded (C ⧸ I) n r s l b d hd j (by omega)
  intro j
  apply (quotientFiniteClass I ℓ).prop_of_iso (BicomplexTotal.singleHomologyIso
    ((rootLayerDouble (C ⧸ I) n r s l b d hd).X j) j k).symm
  change quotientFiniteClass I ℓ ((rootLayerTerm (C ⧸ I) n r s l b j).homology (-j+k))
  by_cases hj : -(n+1:ℤ) ≤ j ∧ j≤0
  · simp only [rootLayerTerm,hj]
    apply ComplexPi.copies_homology_property
    exact rootTwistRow_quotientFinite I ℓ n r _ _ hμ
  · simp only [rootLayerTerm,hj,ite_false]
    exact (quotientFiniteClass I ℓ).prop_of_isZero
      ((homologyFunctor (ModuleCat.{u} (C ⧸ I)) (.up ℤ) (-j+k)).map_isZero (isZero_zero _))
end Lech.ProductSourceCover


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {C : Type u} [CommRing C] (I : Ideal C) (ℓ : TorsionLength I)
 

def quotientLength : TorsionLength (⊥ : Ideal (C ⧸ I)) where
  value M := ℓ.value (quotientScalar I M)
  zero hM := ℓ.zero ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).map_isZero hM)
  additive {S} hS _ := ℓ.additive
    (hS.map_of_exact (ModuleCat.restrictScalars (Ideal.Quotient.mk I)))
    (quotientScalar_powerTorsion I S.X₂)
lemma quotientLength_finite_iff (M : ModuleCat.{u} (C ⧸ I)) :
    (quotientLength I ℓ).finiteClass M ↔ quotientFiniteClass I ℓ M := by
  constructor
  · intro h
    exact ⟨quotientScalar_powerTorsion I M,h.2⟩
  · intro h
    refine ⟨⟨1,?_⟩,h.2⟩
    simp
end Lech


namespace Lech.ComplexPi
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] {I : Ideal R} (ℓ : TorsionLength I)
variable (C : CochainComplex (ModuleCat.{u} R) ℤ)
 
lemma copies_euler (a : ℤ) (w n : ℕ)
    (hf : ∀ q,ℓ.finiteClass (C.homology q))
    (hl : IsZero (C.homology (a-1))) (hr : IsZero (C.homology (a+w+1))) :
    finiteHomologyEuler ℓ (copies (Fin n) C) a w=(n:ℝ)*finiteHomologyEuler ℓ C a w := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero,zero_mul]
    apply finiteHomologyEuler_zero
    intro q
    exact (homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).map_isZero (copies_zero_isZero C)
  | succ n ih =>
    have he := finiteHomologyEuler_additive ℓ (copiesShortComplex C n)
      (copiesSplitting C n).shortExact a w
      (fun q => copies_homology_property C ℓ.finiteClass n q (hf q))
      (fun q => copies_homology_property C ℓ.finiteClass (n+1) q (hf q)) hf hl
      (copies_homology_isZero (Fin n) C _ hr)
    change finiteHomologyEuler ℓ (copies (Fin (n+1)) C) a w =
      finiteHomologyEuler ℓ (copies (Fin n) C) a w+finiteHomologyEuler ℓ C a w at he
    rw [he,ih,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
end Lech.ComplexPi


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open scoped BigOperators
universe u
variable {C : Type u} [CommRing C] (I : Ideal C) (ℓ : TorsionLength I)
variable (n : ℕ) [LinearOrder (Chart n)]
lemma rootTwistRow_length (r : Fin n → ℤ) (a : ℤ) :
    (quotientLength I ℓ).realValue ((rootTwistRow (C ⧸ I) n r a).homology (rootDegree n r a))=
      (signedRank (fun j => a-1-r j):ℝ)*(ℓ.value (ModuleCat.of C (C ⧸ I))).toReal := by
  let e := rootTwistRowHomologyIso (C ⧸ I) n r a (rootDegree n r a) ≪≫
    (targetCech (C ⧸ I) n (fun j => a-1-r j)).extendHomologyIso
      ComplexShape.embeddingUpNat (j:=rootDegree n r a+1) (by change ((rootDegree n r a+1:ℕ):ℤ)=1+(rootDegree n r a:ℤ);push_cast;omega)
  have ht (M : ModuleCat.{u} (C ⧸ I)) : powerTorsion (⊥:Ideal (C ⧸ I)) M := by
    refine ⟨1,?_⟩;simp
  have he := (quotientLength I ℓ).eq_of_iso e (ht _) (ht _)
  change (ℓ.value (quotientScalar I _)).toReal=_
  change ℓ.value (quotientScalar I _)=ℓ.value (quotientScalar I _) at he
  have hp : PureCohomology (C ⧸ I) (targetCech (C ⧸ I) n (fun j => a-1-r j))
      (rootDegree n r a+1) (signedRank (fun j => a-1-r j)) := by
    simpa only [rootDegree,negativeCount_root] using targetSigned_pure (C ⧸ I) n (fun j => a-1-r j)
  rw [he,pureCohomology_length I ℓ _ _ _ hp,ENNReal.toReal_nsmul]
  simp only [nsmul_eq_mul]
lemma rootTwistRow_euler (r : Fin n → ℤ) (a z : ℤ) (w : ℕ)
    (hz : z ≤ (rootDegree n r a:ℤ)) (hw : (rootDegree n r a:ℤ)≤z+w) :
    finiteHomologyEuler (quotientLength I ℓ) (rootTwistRow (C ⧸ I) n r a) z w=
      (-1:ℝ)^((rootDegree n r a:ℤ)-z).toNat*
        (signedRank (fun j => a-1-r j):ℝ)*(ℓ.value (ModuleCat.of C (C ⧸ I))).toReal := by
  have hd : (((rootDegree n r a:ℤ)-z).toNat:ℤ)=(rootDegree n r a:ℤ)-z :=
    Int.toNat_of_nonneg (by omega)
  unfold finiteHomologyEuler
  rw [Finset.sum_eq_single (((rootDegree n r a:ℤ)-z).toNat)]
  · have he : z+(((rootDegree n r a:ℤ)-z).toNat:ℤ)=(rootDegree n r a:ℤ) := by omega
    simp only [he,rootTwistRow_length I ℓ,mul_assoc]
  · intro q _ hq
    rw [(quotientLength I ℓ).realValue_zero (rootTwistRow_isZero (C ⧸ I) n r a _ (by omega)),mul_zero]
  · intro he
    exact (he (Finset.mem_range.mpr (by omega))).elim
lemma single_euler (K : BicomplexTotal.Row (R:=C ⧸ I)) (j z : ℤ) (w : ℕ) :
    finiteHomologyEuler (quotientLength I ℓ)
      (total ((single (BicomplexTotal.Row (R:=C ⧸ I)) (.up ℤ) j).obj K) (.up ℤ)) z w=
      finiteHomologyEuler (quotientLength I ℓ) K (z-j) w := by
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  have ht (M : ModuleCat.{u} (C ⧸ I)) : powerTorsion (⊥:Ideal (C ⧸ I)) M := by
    refine ⟨1,?_⟩;simp
  have he := (quotientLength I ℓ).eq_of_iso (BicomplexTotal.singleHomologyIso K j (z+k)) (ht _) (ht _)
  change ((quotientLength I ℓ).value _).toReal=((quotientLength I ℓ).value _).toReal
  rw [he]
  have hi : -j+(z+(k:ℤ))=z-j+k := by ring
  rw [hi]
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open scoped BigOperators ZeroObject
universe u
variable {C : Type u} [CommRing C] (I : Ideal C) (ℓ : TorsionLength I)
variable (n : ℕ) [LinearOrder (Chart n)]
omit [LinearOrder (Chart n)] in
lemma rootDegree_le (r : Fin n → ℤ) (a : ℤ) : rootDegree n r a ≤ n := by
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun j => a<r j)
  simpa only [rootDegree,Finset.card_univ,Fintype.card_fin] using h
lemma rootLayerTerm_finite (r : Fin n → ℤ) (s : ℕ) (l : ℤ) (b : ℕ → ℕ)
    (hμ : ℓ.value (ModuleCat.of C (C ⧸ I))≠⊤) (j q : ℤ) :
    (quotientLength I ℓ).finiteClass ((rootLayerTerm (C ⧸ I) n r s l b j).homology q) := by
  by_cases hj : -(n+1:ℤ)≤j ∧ j≤0
  · simp only [rootLayerTerm,hj]
    apply ComplexPi.copies_homology_property
    exact (quotientLength_finite_iff I ℓ _).mpr (rootTwistRow_quotientFinite I ℓ n r _ q hμ)
  · simp only [rootLayerTerm,hj,ite_false]
    exact (quotientLength I ℓ).finiteClass.prop_of_isZero
      ((homologyFunctor (ModuleCat.{u} (C ⧸ I)) (.up ℤ) q).map_isZero (isZero_zero _))
lemma rootLayerTerm_isZero (r : Fin n → ℤ) (s : ℕ) (l : ℤ) (b : ℕ → ℕ)
    (j q : ℤ) (hq : q < 0 ∨ (n:ℤ)<q) :
    IsZero ((rootLayerTerm (C ⧸ I) n r s l b j).homology q) := by
  by_cases hj : -(n+1:ℤ)≤j ∧ j≤0
  · simp only [rootLayerTerm,hj]
    apply ComplexPi.copies_homology_isZero
    apply rootTwistRow_isZero
    have := rootDegree_le n r (l-((-j).toNat:ℤ)*(s:ℤ))
    omega
  · simp only [rootLayerTerm,hj,ite_false]
    exact (homologyFunctor (ModuleCat.{u} (C ⧸ I)) (.up ℤ) q).map_isZero (isZero_zero _)
variable (r : Fin n → ℤ) (s : ℕ) (l : ℤ) (b : ℕ → ℕ)
variable (d : ∀ j:ℤ,rootLayerTerm (C ⧸ I) n r s l b j ⟶ rootLayerTerm (C ⧸ I) n r s l b (j+1))
variable (hd : ∀ j:ℤ,d j ≫ d (j+1)=0)
 

theorem rootLayerTotal_euler_rows (hμ : ℓ.value (ModuleCat.of C (C ⧸ I))≠⊤) :
    finiteHomologyEuler (quotientLength I ℓ)
      (total (rootLayerDouble (C ⧸ I) n r s l b d hd) (.up ℤ)) (-(n+1:ℤ)) (2*n+1)=
    ∑ k ∈ Finset.range (n+2),finiteHomologyEuler (quotientLength I ℓ)
      (rootLayerTerm (C ⧸ I) n r s l b (-(n+1:ℤ)+k)) (-(k:ℤ)) (2*n+1) := by
  have he := FiniteComplex.euler_devissage (quotientLength I ℓ) BicomplexTotal.functor
    BicomplexTotal.splitting (-(n+1:ℤ)) (2*n+1) (-(n+1:ℤ)) (n+2)
    (rootLayerDouble (C ⧸ I) n r s l b d hd)
    (by intro j hj;exact rootLayerDouble_bounded (C ⧸ I) n r s l b d hd j (by omega))
    (by
      intro j q
      exact (quotientLength I ℓ).finiteClass.prop_of_iso
        (BicomplexTotal.singleHomologyIso _ j q).symm
        (rootLayerTerm_finite I ℓ n r s l b hμ j (-j+q)))
    (by
      intro j
      apply IsZero.of_iso _ (BicomplexTotal.singleHomologyIso _ j _)
      by_cases hj : -(n+1:ℤ)≤j ∧ j≤0
      · exact rootLayerTerm_isZero I n r s l b j _ (by omega)
      · change IsZero ((rootLayerTerm (C ⧸ I) n r s l b j).homology _)
        simp only [rootLayerTerm,hj,ite_false]
        exact (homologyFunctor (ModuleCat.{u} (C ⧸ I)) (.up ℤ) _).map_isZero (isZero_zero _))
    (by
      intro j
      apply IsZero.of_iso _ (BicomplexTotal.singleHomologyIso _ j _)
      by_cases hj : -(n+1:ℤ)≤j ∧ j≤0
      · exact rootLayerTerm_isZero I n r s l b j _ (by omega)
      · change IsZero ((rootLayerTerm (C ⧸ I) n r s l b j).homology _)
        simp only [rootLayerTerm,hj,ite_false]
        exact (homologyFunctor (ModuleCat.{u} (C ⧸ I)) (.up ℤ) _).map_isZero (isZero_zero _))
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro k _
  change finiteHomologyEuler (quotientLength I ℓ)
    (total ((single (BicomplexTotal.Row (R:=C ⧸ I)) (.up ℤ) (-(n+1:ℤ)+k)).obj
      (rootLayerTerm (C ⧸ I) n r s l b (-(n+1:ℤ)+k))) (.up ℤ)) (-(n+1:ℤ)) (2*n+1)=_
  rw [single_euler]
  congr 1
  ring
end Lech.ProductSourceCover
end
end

end OAI
