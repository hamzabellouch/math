import Mathlib
import OAI.RingTheory.Multiplicity.KoszulTensorSingle

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject

private lemma component_iso_square {C : Type*} [Category C]
    {X Y A B D E : C} (eA : A ≅ B) (eD : D ≅ E)
    (a : X ⟶ A) (b : Y ⟶ D) (h : X ⟶ Y) (f : B ⟶ E) (g : A ⟶ D)
    (hg : g = eA.hom ≫ f ≫ eD.inv) (ha : h ≫ b = a ≫ g) :
    (a ≫ eA.hom) ≫ f = h ≫ (b ≫ eD.hom) := by
  rw [← Category.assoc h b, ha, Category.assoc, hg]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] [Nontrivial R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
  (ell : AllModuleLength R) (F : CochainComplex (ModuleCat.{u} R) ℤ)

 

theorem cech_homology_value
    (hh : 0<h) (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ, 0<a → ell.value (ModuleCat.of R
      (R ⧸ Ideal.span (Set.range (fun j => z j^a))))=a^h • ell.value (ModuleCat.of R (R ⧸ I)))
    (hK : ∀ a : ℕ, 1≤a → ∀ i : ℤ, i<0 →
      ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
    (hf : ∀ j, Module.Free R (F.X j)) (hfin : ∀ j, Module.Finite R (F.X j))
    (n : ℤ) (d : ℕ) (hb : ∀ j, j<n ∨ n+d≤j → IsZero (F.X j))
    (hacyc : ∀ j, ((baseChangeFunctor R (Localization.Away (z j))).mapHomologicalComplex _ |>.obj F).Acyclic)
    (i : ℤ) :
    ell.value (F.homology i)=ell.value (((TensorTotal.Right.functor F).obj
      (FilteredCech.positive I z (coordinate_mem I z hz) 0)).homology (i+1)) := by
  subst I
  let : ∀ j, Module.Free R (F.X j) := hf
  let : ∀ j, Module.Finite R (F.X j) := hfin
  have hp : ∀ j, Module.Projective R (F.X j) := fun j => by have := hf j; infer_instance
  have hbound : ∀ j, j<n ∨ n+d-1<j → IsZero (F.X j) := by
    intro j hj
    apply hb
    omega
  obtain ⟨m,hm⟩ := uniform_nullhomotopy_of_projective_acyclic_away z F n (n+d-1) hp hfin hbound hacyc
  let t := m+1
  have ht : 1≤t := by dsimp [t]; omega
  have H : ∀ j, Homotopy (z j^t • 𝟙 F) 0 := fun j =>
    Koszul.scalarPowerHomotopy F (z j) m t (by dsimp [t]; omega) (hm j).some
  let ℓ := ell.torsionLength ⊥
  let P := ℓ.zeroClass
  have hKos : ∀ a : ℕ, 1≤a → ∀ k : ℤ, k<0 → P ((Koszul.unit (List.ofFn fun j => z j^a)).homology k) := by
    intro a ha k hk
    exact ell.mem_zeroClass _ (hK a ha k hk)
  obtain ⟨M₀,hM₀⟩ := ordinaryPower_stableImage_isoMod P F n d hb h z t ht H hKos
  obtain ⟨MD,hMD⟩ := exists_uniform_geometric_stableImage (Ideal.span (Set.range z)) z rfl F
    n (n+d-1) hp hfin hbound hacyc
  let M := max M₀ MD
  obtain ⟨N₀,hMN₀,hN₀⟩ := hM₀ M (le_max_left _ _)
  let N := max N₀ (M+MD)
  have hNN : N₀≤N := le_max_left _ _
  have hMN : M≤N := hMN₀.trans hNN
  have hgap : MD≤N-M := by have := le_max_right N₀ (M+MD); dsimp [N]; omega
  let f := homologyMap ((complexQuotientMap (show Ideal.span (Set.range z)^N ≤ Ideal.span (Set.range z)^M from Ideal.pow_le_pow_right hMN) (.up ℤ)).app F) i
  let g := homologyMap ((TensorTotal.Right.functor F).map
    (thickeningCechTransition (Ideal.span (Set.range z)) z rfl hMN)) (i+1)
  let s : Arrow.mk f ⟶ Arrow.mk g := Arrow.homMk
    (thickeningComparison (Ideal.span (Set.range z)) z rfl F N i)
    (thickeningComparison (Ideal.span (Set.range z)) z rfl F M i)
    (thickeningComparison_transition (Ideal.span (Set.range z)) z rfl F hMN i).symm
  have hs₁ : P.isoModSerre s.left :=
    thickeningComparison_isoModSerre (Ideal.span (Set.range z)) z rfl F ell hh hmu ha hf hfin n d hb N i
  have hs₂ : P.isoModSerre s.right :=
    thickeningComparison_isoModSerre (Ideal.span (Set.range z)) z rfl F ell hh hmu ha hf hfin n d hb M i
  have hab : ℓ.value (F.homology i)=ℓ.value (Limits.image f) :=
    ℓ.eq_of_isoModSerre _ ⟨1,by simp⟩ ⟨1,by simp⟩ (hN₀ N hNN i)
  have hbc : ℓ.value (Limits.image f)=ℓ.value (Limits.image g) :=
    ℓ.image_value_eq s hs₁ hs₂ ⟨1,by simp⟩ ⟨1,by simp⟩
  have hg := hMD M N hMN (le_max_right _ _) hgap (i+1)
  have hdc : ℓ.value (((TensorTotal.Right.functor F).obj
      (FilteredCech.positive (Ideal.span (Set.range z)) z (coordinate_mem _ z rfl) 0)).homology (i+1))=
      ℓ.value (Limits.image g) :=
    ℓ.eq_of_iso (asIso (homologyMap (geometricStructureMap (Ideal.span (Set.range z)) z rfl F N) (i+1) ≫
      factorThruImage g)) ⟨1,by simp⟩ ⟨1,by simp⟩
  exact hab.trans (hbc.trans hdc.symm)
end Lech.SourceGraded


namespace Lech.SignedFraction
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) (w : R) (d : ℕ)

 
def order (t : ℤ) (n : ℕ) : ℕ := ((n*d:ℕ)+t).toNat

@[simp] lemma order_nat (t n : ℕ) : order d (t:ℤ) n=n*d+t := by
  simp only [order, ←Nat.cast_add, Int.toNat_natCast]

lemma order_add_le (t : ℤ) (n k : ℕ) : order d t (k+n) ≤ k*d+order d t n := by
  dsimp only [order]
  push_cast
  have he : ((k:ℤ)+(n:ℤ))*(d:ℤ)+t=(k*d:ℕ)+(n*d:ℕ)+t := by push_cast; ring
  rw [he]
  omega

 
def fraction (t : ℤ) (n : ℕ) : ↥(I^(order d t n)) →ₗ[R] Localization.Away w where
  toFun a := Localization.mk (a:R) (⟨w^n,n,rfl⟩ : Submonoid.powers w)
  map_add' _ _ := (Localization.add_mk_self _ _ _).symm
  map_smul' _ _ := (Localization.smul_mk _ _ _).symm

def piece (t : ℤ) : Submodule R (Localization.Away w) :=
  ⨆ n : ℕ, LinearMap.range (fraction I w d t n)

lemma fraction_mem (t : ℤ) (n : ℕ) (a : ↥(I^(order d t n))) :
    fraction I w d t n a ∈ piece I w d t :=
  Submodule.mem_iSup_of_mem n ⟨a,rfl⟩

variable (hw : w∈I^d)
include hw
lemma raise_fraction (t : ℤ) (n k : ℕ) (a : ↥(I^(order d t n))) :
    ∃ b : ↥(I^(order d t (k+n))), fraction I w d t (k+n) b=fraction I w d t n a := by
  have hp : w^k∈I^(k*d) := by
    simpa only [pow_mul,mul_comm k d] using Ideal.pow_mem_pow hw k
  have hb : w^k*(a:R)∈I^(order d t (k+n)) := by
    apply Ideal.pow_le_pow_right (order_add_le d t n k)
    rw [pow_add]
    exact Ideal.mul_mem_mul hp a.property
  refine ⟨⟨w^k*(a:R),hb⟩,?_⟩
  dsimp only [fraction,LinearMap.coe_mk,AddHom.coe_mk]
  rw [Localization.mk_eq_mk_iff,Localization.r_iff_exists]
  refine ⟨1,?_⟩
  simp only [Submonoid.coe_one,one_mul,pow_add]
  ring

lemma range_mono (t : ℤ) : Monotone (fun n : ℕ => LinearMap.range (fraction I w d t n)) := by
  intro n m hnm x hx
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le' hnm
  exact raise_fraction I w d hw t n k a

lemma exists_fraction (t : ℤ) (x : piece I w d t) :
    ∃ (n : ℕ) (a : ↥(I^(order d t n))), fraction I w d t n a=(x:Localization.Away w) := by
  have hx := x.property
  change x.val∈(⨆ n,LinearMap.range (fraction I w d t n)) at hx
  rw [Submodule.mem_iSup_of_directed _ (range_mono I w d hw t).directed_le] at hx
  exact hx
omit hw

lemma antitone : Antitone (piece I w d) := by
  intro s t hst
  apply iSup_le
  intro n
  rintro _ ⟨a,rfl⟩
  have he : order d s n≤order d t n := by unfold order; omega
  exact fraction_mem I w d s n ⟨a.val,Ideal.pow_le_pow_right he a.property⟩
end Lech.SignedFraction


namespace Lech.SignedFraction
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

 

lemma piece_nat (w : R) (d t : ℕ) : piece I w d (t:ℤ)=FilteredFraction.piece I w d t := by
  apply iSup_congr
  intro n
  ext x
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨⟨a.val,by simpa only [order_nat] using a.property⟩,ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨⟨a.val,by simpa only [order_nat] using a.property⟩,ha⟩

variable {w z c : R} {d k : ℕ}
  (hw : w∈I^d) (hc : c∈I^k) (hwc : z*c=w) (hdk : k+1=d)

include hdk in
lemma order_divide_le (t : ℤ) (m n : ℕ) :
    order d t (n+m) ≤ m*k+order d (t+(m:ℤ)) n := by
  dsimp only [order]
  have he : ((n+m)*d:ℕ)+t=(m*k:ℕ)+((n*d:ℕ)+(t+(m:ℤ))) := by
    rw [←hdk]
    push_cast
    ring
  rw [he]
  omega

include hc hdk in
lemma inverseFactor_fraction (t : ℤ) (m n : ℕ) (a : ↥(I^(order d (t+(m:ℤ)) n))) :
    ∃ b : ↥(I^(order d t (n+m))),
      FilteredFraction.inverseFactor (w := w) (c := c) m * fraction I w d (t+(m:ℤ)) n a =
        fraction I w d t (n+m) b := by
  have hc' : c^m∈I^(m*k) := by
    simpa only [pow_mul,mul_comm m k] using Ideal.pow_mem_pow hc m
  have hb : c^m*(a:R)∈I^(order d t (n+m)) := by
    apply Ideal.pow_le_pow_right (order_divide_le hdk t m n)
    rw [pow_add]
    exact Ideal.mul_mem_mul hc' a.property
  refine ⟨⟨c^m*(a:R),hb⟩,?_⟩
  change Localization.mk (c^m) (⟨w^m,m,rfl⟩ : Submonoid.powers w) *
    Localization.mk (a:R) (⟨w^n,n,rfl⟩ : Submonoid.powers w) =
      Localization.mk (c^m*(a:R)) (⟨w^(n+m),n+m,rfl⟩ : Submonoid.powers w)
  rw [Localization.mk_mul,Localization.mk_eq_mk_iff,Localization.r_iff_exists]
  refine ⟨1,?_⟩
  simp only [Submonoid.coe_one,one_mul,Submonoid.coe_mul,pow_add]
  ring

include hw hc hdk in
lemma inverseFactor_mem (t : ℤ) (m : ℕ) (x : piece I w d (t+(m:ℤ))) :
    FilteredFraction.inverseFactor (w := w) (c := c) m*x.val∈piece I w d t := by
  obtain ⟨n,a,ha⟩ := exists_fraction I w d hw (t+(m:ℤ)) x
  rw [←ha]
  obtain ⟨b,hb⟩ := inverseFactor_fraction I hc hdk t m n a
  rw [hb]
  exact fraction_mem I w d t (n+m) b

 
def divide (t : ℤ) (m : ℕ) : piece I w d (t+(m:ℤ)) →ₗ[R] piece I w d t where
  toFun x := ⟨FilteredFraction.inverseFactor (w := w) (c := c) m*x.val,
    inverseFactor_mem I hw hc hdk t m x⟩
  map_add' _ _ := Subtype.ext (mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (mul_smul_comm _ _ _)

include hwc in
lemma smul_divide (t : ℤ) (m : ℕ) (x : piece I w d (t+(m:ℤ))) :
    z^m • divide I hw hc hdk t m x =
      Submodule.inclusion (antitone I w d (by omega : t≤t+(m:ℤ))) x := by
  apply Subtype.ext
  change z^m • (FilteredFraction.inverseFactor (w := w) (c := c) m*x.val)=x.val
  rw [Algebra.smul_def,←mul_assoc,FilteredFraction.inverseFactor_mul hwc,one_mul]
end Lech.SignedFraction


namespace Lech.SignedFraction
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  {w v c : R} {d e k : ℕ} (hw : w ∈ I^d) (hc : c ∈ I^k)
  (hwc : w*c=v) (hdeg : d+k=e)

include hdeg in
lemma order_restrict_le (t : ℤ) (n : ℕ) : order e t n ≤ order d t n+n*k := by
  dsimp only [order]
  have he : ((n*e:ℕ):ℤ)+t=((n*d:ℕ):ℤ)+t+((n*k:ℕ):ℤ) := by
    rw [←hdeg]
    push_cast
    ring
  rw [he]
  omega

include hc hdeg in
lemma restriction_fraction (t : ℤ) (n : ℕ) (a : ↥(I^(order d t n))) :
    ∃ b : ↥(I^(order e t n)),
      TwistedLocalization.ambientTo (R := R) (show w ∣ v from ⟨c,hwc.symm⟩)
        (fraction I w d t n a) = fraction I v e t n b := by
  have hp : c^n ∈ I^(n*k) := by
    simpa only [pow_mul,mul_comm n k] using Ideal.pow_mem_pow hc n
  have hb : (a:R)*c^n ∈ I^(order e t n) := by
    apply Ideal.pow_le_pow_right (order_restrict_le hdeg t n)
    rw [pow_add]
    exact Ideal.mul_mem_mul a.property hp
  exact ⟨⟨(a:R)*c^n,hb⟩,TwistedLocalization.ambientTo_mk hwc a n⟩

include hw hc hdeg in
lemma restriction_mem (t : ℤ) (x : piece I w d t) :
    TwistedLocalization.ambientTo (R := R) (show w ∣ v from ⟨c,hwc.symm⟩) x ∈
      piece I v e t := by
  obtain ⟨n,a,ha⟩ := exists_fraction I w d hw t x
  obtain ⟨b,hb⟩ := restriction_fraction I hc hwc hdeg t n a
  rw [←ha,hb]
  exact fraction_mem I v e t n b
end Lech.SignedFraction


namespace Lech.SignedCech
section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

abbrev term (t : ℤ) (s : Finset (Fin h)) :
    Submodule R (LocalizationCech.ambient z s) :=
  SignedFraction.piece I (GradedChart.denominator z s) s.card t

include hz in
lemma restriction_mem (t : ℤ) {s v : Finset (Fin h)} (hsv : s ⊆ v) (x : term I z t s) :
    TwistedLocalization.ambientTo (R := R) (GradedChart.denominator_dvd z hsv) x ∈ term I z t v :=
  SignedFraction.restriction_mem I (FilteredCech.denominator_mem I z hz s)
    (FilteredCech.denominator_mem I z hz (v\s)) (GradedChart.denominator_mul_sdiff z hsv)
    (by rw [Nat.add_comm,Finset.card_sdiff_add_card_eq_card hsv]) t x

def complex (t : ℤ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  LocalizationCech.complex z (term I z t) (restriction_mem I z hz t)

def inclusion {s t : ℤ} (hst : s ≤ t) : complex I z hz t ⟶ complex I z hz s :=
  LocalizationCech.inclusion z _ _ _ _ (fun _ => SignedFraction.antitone I _ _ hst)

lemma inclusion_refl (t : ℤ) : inclusion I z hz (le_refl t)=𝟙 (complex I z hz t) := by
  ext n x
  rfl

lemma inclusion_comp {r s t : ℤ} (hrs : r ≤ s) (hst : s ≤ t) :
    inclusion I z hz hst ≫ inclusion I z hz hrs = inclusion I z hz (hrs.trans hst) := by
  ext n x
  rfl

instance inclusion_mono {s t : ℤ} (hst : s ≤ t) : Mono (inclusion I z hz hst) := by
  apply mono_of_mono_f
  intro n
  apply (ModuleCat.mono_iff_injective _).mpr
  exact LocalizationCech.inclusionLinear_injective z (term I z t) (term I z s)
    (fun _ => SignedFraction.antitone I _ _ hst) n

lemma term_nat (t : ℕ) (s : Finset (Fin h)) : term I z (t:ℤ) s=FilteredCech.term I z t s :=
  SignedFraction.piece_nat I _ _ _
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

def augmented (t : ℤ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (complex I z hz t).extend ComplexShape.embeddingUpNat

lemma augmented_boundedBelow (t : ℤ) :
    ∀ i, i < (0 : ℤ) → IsZero ((augmented I z hz t).X i) := by
  intro i hi
  apply (complex I z hz t).isZero_extend_X
  intro n hn
  change (n : ℤ)=i at hn
  omega

 

def positive (t : ℤ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  FiniteComplex.dropBottom (augmented I z hz t) 0 (augmented_boundedBelow I z hz t)

lemma positive_boundedBelow (t : ℤ) :
    ∀ q, q≤(0 : ℤ) → IsZero ((positive I z hz t).X q) := by
  intro q hq
  exact FiniteComplex.dropBottom_boundedBelow _ _ _ q (by omega)

def positiveInclusion {s t : ℤ} (hst : s ≤ t) : positive I z hz t ⟶ positive I z hz s :=
  FiniteComplex.dropBottomMap (augmented I z hz t) 0 (augmented_boundedBelow I z hz t)
    (augmented_boundedBelow I z hz s) (extendMap (inclusion I z hz hst) ComplexShape.embeddingUpNat)

def positiveXIso (t : ℤ) (n : ℕ) (hn : 0<n) :
    (positive I z hz t).X (n : ℤ) ≅ (complex I z hz t).X n :=
  FiniteComplex.dropBottomXIso _ _ _ (n : ℤ) (by omega) ≪≫
    (complex I z hz t).extendXIso ComplexShape.embeddingUpNat (i := n) rfl

@[reassoc] lemma positiveXIso_inclusion {s t : ℤ} (hst : s ≤ t) (n : ℕ) (hn : 0<n) :
    (positiveXIso I z hz t n hn).hom ≫ (inclusion I z hz hst).f n =
      (positiveInclusion I z hz hst).f (n : ℤ) ≫ (positiveXIso I z hz s n hn).hom := by
  have he := congrArg (fun f => f.f (n : ℤ))
    (FiniteComplex.dropBottomMap_ι (augmented I z hz t) 0 (augmented_boundedBelow I z hz t)
      (augmented_boundedBelow I z hz s) (extendMap (inclusion I z hz hst) ComplexShape.embeddingUpNat))
  dsimp only [positiveXIso,Iso.trans_hom,FiniteComplex.dropBottomXIso,asIso_hom,positiveInclusion]
  exact component_iso_square
    ((complex I z hz t).extendXIso ComplexShape.embeddingUpNat (i := n) rfl)
    ((complex I z hz s).extendXIso ComplexShape.embeddingUpNat (i := n) rfl)
    _ _ _ _ _
    (extendMap_f (inclusion I z hz hst) ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)) he

lemma positiveInclusion_refl (t : ℤ) : positiveInclusion I z hz (le_refl t)=𝟙 _ := by
  apply (cancel_mono (kernel.ι (FiniteComplex.bottomProjection (augmented I z hz t) 0
    (augmented_boundedBelow I z hz t)))).mp
  refine (FiniteComplex.dropBottomMap_ι (augmented I z hz t) 0
    (augmented_boundedBelow I z hz t) (augmented_boundedBelow I z hz t)
    (extendMap (inclusion I z hz (le_refl t)) ComplexShape.embeddingUpNat)).trans ?_
  have he : extendMap (inclusion I z hz (le_refl t)) ComplexShape.embeddingUpNat =
      𝟙 (augmented I z hz t) := by
    rw [inclusion_refl, extendMap_id]
    rfl
  exact (congrArg (kernel.ι (FiniteComplex.bottomProjection (augmented I z hz t) 0
    (augmented_boundedBelow I z hz t)) ≫ ·) he).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)

lemma positiveInclusion_comp {r s t : ℤ} (hrs : r ≤ s) (hst : s ≤ t) :
    positiveInclusion I z hz hst ≫ positiveInclusion I z hz hrs =
      positiveInclusion I z hz (hrs.trans hst) := by
  apply (cancel_mono (kernel.ι (FiniteComplex.bottomProjection (augmented I z hz r) 0
    (augmented_boundedBelow I z hz r)))).mp
  let ι (j : ℤ) := kernel.ι (FiniteComplex.bottomProjection (augmented I z hz j) 0
    (augmented_boundedBelow I z hz j))
  have hι {a b : ℤ} (hab : a ≤ b) : positiveInclusion I z hz hab ≫ ι a =
      ι b ≫ extendMap (inclusion I z hz hab) ComplexShape.embeddingUpNat :=
    FiniteComplex.dropBottomMap_ι (augmented I z hz b) 0
      (augmented_boundedBelow I z hz b) (augmented_boundedBelow I z hz a) _
  have he : extendMap (inclusion I z hz hst) ComplexShape.embeddingUpNat ≫
      extendMap (inclusion I z hz hrs) ComplexShape.embeddingUpNat =
        extendMap (inclusion I z hz (hrs.trans hst)) ComplexShape.embeddingUpNat := by
    rw [← extendMap_comp, inclusion_comp]
  exact (Category.assoc _ _ _).trans
    ((congrArg (positiveInclusion I z hz hst ≫ ·) (hι hrs)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ extendMap (inclusion I z hz hrs) ComplexShape.embeddingUpNat) (hι hst)).trans
          ((Category.assoc _ _ _).trans ((congrArg (ι t ≫ ·) he).trans (hι _).symm)))))
end Lech.SignedCech


namespace Lech.SignedCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

 
def divide {s : Finset (Fin h)} (i : Fin h) (hi : i∈s) (t : ℤ) (m : ℕ) :
    term I z (t+(m:ℤ)) s →ₗ[R] term I z t s := by
  classical
  exact SignedFraction.divide I (FilteredCech.denominator_mem I z hz s)
    (FilteredCech.denominator_mem I z hz (s.erase i)) (Finset.card_erase_add_one hi) t m

lemma smul_divide {s : Finset (Fin h)} (i : Fin h) (hi : i∈s) (t : ℤ) (m : ℕ)
    (x : term I z (t+(m:ℤ)) s) :
    z i ^ m • divide I z hz i hi t m x =
      Submodule.inclusion (SignedFraction.antitone I _ _ (by omega : t ≤ t+(m:ℤ))) x := by
  classical
  apply SignedFraction.smul_divide
  exact Finset.mul_prod_erase s z hi
end Lech.SignedCech


namespace Lech.SignedCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Lech.TensorTotal
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℕ)
  (H : ∀ i, Homotopy (z i ^ m • 𝟙 F) 0)

 

def intersectionHomotopy (t : ℤ) (n : ℕ) (hn : 0<n) (a : Fin n → Fin h) :
    Homotopy (termTensorMap F (ModuleCat.of R (term I z (t+(m:ℤ)) (ActualCech.intersection a)))
      (ModuleCat.ofHom (Submodule.inclusion (SignedFraction.antitone I _ _ (by omega : t ≤ t+(m:ℤ)))))) 0 := by
  let i : Fin h := a ⟨0,hn⟩
  have hi : i ∈ ActualCech.intersection a := (ActualCech.mem_intersection a i).mpr ⟨⟨0,hn⟩,rfl⟩
  apply tensorDivisionHomotopy F (z i ^ m)
    (ModuleCat.ofHom (divide I z hz i hi t m)) _ _ (H i)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact smul_divide I z hz i hi t m x

def cochainPiIso (t : ℤ) (n : ℕ) :
    (complex I z hz t).X n ≅ TensorPi.modulePi (fun a : Fin n → Fin h =>
      ModuleCat.of R (term I z t (ActualCech.intersection a))) := Iso.refl _

lemma cochainPiIso_inclusion {s t : ℤ} (hst : s≤t) (n : ℕ) :
    (cochainPiIso I z hz t n).hom ≫ TensorPi.piMap (fun a : Fin n → Fin h =>
      ModuleCat.ofHom (Submodule.inclusion (SignedFraction.antitone I
        (GradedChart.denominator z (ActualCech.intersection a))
        (ActualCech.intersection a).card hst))) =
      (inclusion I z hz hst).f n ≫ (cochainPiIso I z hz s n).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

def cochainHomotopy (t : ℤ) (n : ℕ) (hn : 0<n) :
    Homotopy (termTensorMap F ((complex I z hz (t+(m:ℤ))).X n)
      ((inclusion I z hz (by omega : t ≤ t+(m:ℤ))).f n)) 0 := by
  let Q : (Fin n → Fin h) → ModuleCat.{u} R := fun a =>
    ModuleCat.of R (term I z (t+(m:ℤ)) (ActualCech.intersection a))
  let Q' : (Fin n → Fin h) → ModuleCat.{u} R := fun a =>
    ModuleCat.of R (term I z t (ActualCech.intersection a))
  let inc : ∀ a, Q a ⟶ Q' a := fun _ =>
    ModuleCat.ofHom (Submodule.inclusion (SignedFraction.antitone I _ _ (by omega : t ≤ t+(m:ℤ))))
  have HH := TensorPi.homotopy (Q := Q) (Q' := Q') F inc
    (intersectionHomotopy I z hz F m H t n hn)
  exact coefficientHomotopyOfIso F (cochainPiIso I z hz (t+(m:ℤ)) n) (cochainPiIso I z hz t n)
    _ _ (cochainPiIso_inclusion I z hz (by omega : t ≤ t+(m:ℤ)) n) HH

 

def positiveRowHomotopy (t : ℤ) (q : ℤ) :
    Homotopy (termTensorMap F ((positive I z hz (t+(m:ℤ))).X q)
      ((positiveInclusion I z hz (by omega : t ≤ t+(m:ℤ))).f q)) 0 := by
  by_cases hq : q ≤ 0
  · have hf : (positiveInclusion I z hz (by omega : t ≤ t+(m:ℤ))).f q=0 :=
      (positive_boundedBelow I z hz (t+(m:ℤ)) q hq).eq_of_src _ _
    rw [hf,termTensorMap_zero]
  · have hn : 0<q.toNat := by omega
    have heq : (q.toNat:ℤ)=q := by omega
    have HH := coefficientHomotopyOfIso F (positiveXIso I z hz (t+(m:ℤ)) q.toNat hn)
      (positiveXIso I z hz t q.toNat hn) _ _ (positiveXIso_inclusion I z hz _ q.toNat hn)
      (cochainHomotopy I z hz F m H t q.toNat hn)
    rw [heq] at HH
    exact HH
end Lech.SignedCech
end

end OAI
