import Mathlib
import OAI.RingTheory.Multiplicity.ReesRegular
import OAI.RingTheory.Multiplicity.SignedCechBicRow

namespace OAI

noncomputable section
namespace Lech.Homogeneous
open HomogeneousLocalization
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (G : ℕ → Submodule R A) (H : ℕ → Submodule R B)
  [GradedAlgebra G] [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A),g (r • a)=r • g a)
  {f : A} {d : ℕ} (hf : f ∈ G d)
attribute [local instance] awayAddCommGroup

lemma zeroPieceEquiv_val (x : Away G f) : (zeroPieceEquiv G hf x).val=x.val := rfl

lemma zeroPieceEquiv_symm_val (x : TwistedLocalization.piece G (f:=f) (d:=d) 0) :
    ((zeroPieceEquiv G hf).symm x).val=x.val := by
  have h := congrArg Subtype.val ((zeroPieceEquiv G hf).apply_symm_apply x)
  exact h

lemma zeroPiece_natural (x : Away G f) :
    zeroPieceEquiv H (Graded.map_mem g hf) (awayMap G H g hg f x) =
      TwistedLocalization.pieceMap G hf H g hg 0 (zeroPieceEquiv G hf x) := by
  apply Subtype.ext
  obtain ⟨j,a,ha,rfl⟩ := Away.mk_surjective G hf x
  change (Away.map g f (Away.mk G hf j a ha)).val =
    TwistedLocalization.ambientMap G H g hg (Away.mk G hf j a ha).val
  rw [Away.map_mk]
  simp only [Away.val_mk]
  let b : G (j*d+0) := ⟨a,by simpa only [Nat.add_zero,nsmul_eq_mul,Nat.cast_id] using ha⟩
  change _ = TwistedLocalization.ambientMap G H g hg (TwistedLocalization.fraction G (f:=f) 0 j b)
  rw [TwistedLocalization.ambientMap_fraction]
  unfold TwistedLocalization.gradedMap
  rfl
end Lech.Homogeneous

namespace Lech.FilteredFraction
open HomogeneousLocalization IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {w : R} {d : ℕ} (hw : w ∈ I^d)
attribute [local instance] Homogeneous.awayAddCommGroup
attribute [local irreducible] quotientGraded Homogeneous.awayMap TwistedLocalization.piece TwistedLocalization.pieceMap TwistedLocalization.gradedMap

abbrev ReesChart := Away (reesGrade I) (reesDenominator I hw)
abbrev ExceptionalChart := Away (SourceGraded.targetGrade I) (quotientGraded I (reesDenominator I hw))
private local instance reesChartCommRing : CommRing (ReesChart I hw) := inferInstance
private local instance reesChartModule : Module R (ReesChart I hw) :=
  Homogeneous.module (reesGrade I) (Submonoid.powers (reesDenominator I hw))
private local instance reesChartTower : IsScalarTower R R (ReesChart I hw) :=
  ⟨fun a b c => mul_smul a b c⟩

def chartEquiv : ReesChart I hw ≃ₗ[R] piece I w d 0 :=
  (Homogeneous.zeroPieceEquiv (reesGrade I) (reesDenominator_mem I hw)).trans (reesEquiv I hw 0)

def exceptionalChartEquiv : ExceptionalChart I hw ≃ₗ[R] exceptionalPiece I hw 0 :=
  Homogeneous.zeroPieceEquiv (R:=R) (A:=IdealGraded.Ring I) (SourceGraded.targetGrade I)
    (quotientDenominator_mem I hw)

lemma exceptionalChartEquiv_symm_val (x : exceptionalPiece I hw 0) :
    ((exceptionalChartEquiv I hw).symm x).val=x.val :=
  congrArg Subtype.val ((exceptionalChartEquiv I hw).apply_symm_apply x)

 
def chartReduction : ReesChart I hw →ₗ[R] ExceptionalChart I hw :=
  (exceptionalChartEquiv I hw).symm.toLinearMap.comp
    ((quotientTwist I hw 0).comp
      (Homogeneous.zeroPieceEquiv (reesGrade I) (reesDenominator_mem I hw)).toLinearMap)

lemma chartReduction_surjective : Function.Surjective (chartReduction I hw) :=
  (exceptionalChartEquiv I hw).symm.surjective.comp ((quotientTwist_surjective I hw 0).comp
    (Homogeneous.zeroPieceEquiv (reesGrade I) (reesDenominator_mem I hw)).surjective)

lemma chartReduction_layerMap (x : ReesChart I hw) :
    exceptionalChartEquiv I hw (chartReduction I hw x) =
        layerMap I hw 0 (chartEquiv I hw x) := by
  change _ = quotientTwist I hw 0 ((reesEquiv I hw 0).symm
    ((reesEquiv I hw 0) (Homogeneous.zeroPieceEquiv (reesGrade I) (reesDenominator_mem I hw) x)))
  rw [LinearEquiv.symm_apply_apply]
  unfold chartReduction
  exact LinearEquiv.apply_symm_apply _ _

attribute [local irreducible] TwistedLocalization.ambientMap
def chartAmbient :=
  TwistedLocalization.ambientMap (R:=R) (A:=reesAlgebra I) (B:=IdealGraded.Ring I)
    (reesGrade I) (SourceGraded.targetGrade I) (quotientGraded I)
    (quotientGraded_smul I) (f:=reesDenominator I hw)

lemma chartReduction_val (x : ReesChart I hw) :
    (chartReduction I hw x).val = chartAmbient I hw x.val := by
  change ((exceptionalChartEquiv I hw).symm
    (quotientTwist I hw 0 (Homogeneous.zeroPieceEquiv (reesGrade I)
      (reesDenominator_mem I hw) x))).val = _
  rw [exceptionalChartEquiv_symm_val]
  unfold quotientTwist TwistedLocalization.pieceMap chartAmbient
  rfl

lemma chartReduction_mk (j : ℕ) (a : reesAlgebra I) (ha : a ∈ reesGrade I (j • d)) :
    chartReduction I hw (Away.mk (reesGrade I) (reesDenominator_mem I hw) j a ha) =
      Away.mk (SourceGraded.targetGrade I) (quotientDenominator_mem I hw) j
        (quotientGraded I a) (Graded.map_mem (quotientGraded I) ha) := by
  apply HomogeneousLocalization.val_injective
  rw [chartReduction_val,Away.val_mk,Away.val_mk]
  let b : reesGrade I (j*d+0) := ⟨a,by simpa only [nsmul_eq_mul,Nat.cast_id,Nat.add_zero] using ha⟩
  change chartAmbient I hw (TwistedLocalization.fraction (reesGrade I) (f:=reesDenominator I hw) 0 j b)=_
  unfold chartAmbient
  rw [TwistedLocalization.ambientMap_fraction]
  unfold TwistedLocalization.gradedMap
  rfl

private local instance reesChartAlgebra : Algebra R (ReesChart I hw) :=
  Homogeneous.algebra (reesGrade I) (Submonoid.powers (reesDenominator I hw))
private local instance exceptionalChartAlgebra : Algebra R (ExceptionalChart I hw) :=
  Homogeneous.algebra (SourceGraded.targetGrade I)
    (Submonoid.powers (quotientGraded I (reesDenominator I hw)))

 
def chartReductionAlg : ReesChart I hw →ₐ[R] ExceptionalChart I hw where
  toFun := chartReduction I hw
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    apply HomogeneousLocalization.val_injective
    rw [chartReduction_val,HomogeneousLocalization.val_one,map_one,HomogeneousLocalization.val_one]
  map_mul' x y := by
    apply HomogeneousLocalization.val_injective
    rw [chartReduction_val,HomogeneousLocalization.val_mul,map_mul,
      HomogeneousLocalization.val_mul,chartReduction_val,chartReduction_val]
  commutes' r := by
    apply HomogeneousLocalization.val_injective
    rw [chartReduction_val,Homogeneous.val_algebraMap,
      AlgHom.commutes,Homogeneous.val_algebraMap]

lemma chartReduction_eq_zero_iff (x : ReesChart I hw) :
    chartReduction I hw x=0 ↔ chartFraction I hw x ∈ piece I w d 1 := by
  have he : chartReduction I hw x=0 ↔ layerMap I hw 0 (chartEquiv I hw x)=0 := by
    rw [←chartReduction_layerMap]
    exact (LinearEquiv.map_eq_zero_iff _).symm
  rw [he,←LinearMap.mem_ker,layerMap_kernel]
  rfl

include hw in
lemma scalar_mem_next {r : R} (hr : r ∈ I) (x : piece I w d 0) :
    r • x.val ∈ piece I w d 1 := by
  obtain ⟨j,b,hb⟩ := exists_fraction I w d hw 0 x
  have hmem : r*b.val ∈ I^(j*d+1) := by
    rw [pow_succ']
    exact Ideal.mul_mem_mul hr (by simpa only [Nat.add_zero] using b.property)
  have he : r • fraction I w d 0 j b = fraction I w d 1 j ⟨r*b.val,hmem⟩ := by
    change r • Localization.mk b.val (⟨w^j,j,rfl⟩ : Submonoid.powers w) =
      Localization.mk (r*b.val) (⟨w^j,j,rfl⟩ : Submonoid.powers w)
    simpa only [smul_eq_mul] using (Localization.smul_mk r b.val (⟨w^j,j,rfl⟩ : Submonoid.powers w))
  rw [←hb,he]
  exact fraction_mem I w d 1 j _

 

lemma chartReduction_kernel {z c : R} {k : ℕ} (hz : z∈I) (hc : c∈I^k)
    (hwc : z*c=w) (hdk : k+1=d) :
    (chartReduction I hw).ker=I • (⊤ : Submodule R (ReesChart I hw)) := by
  apply le_antisymm
  · intro x hx
    have hx1 := (chartReduction_eq_zero_iff I hw x).mp (LinearMap.mem_ker.mp hx)
    let y : piece I w d 1 := ⟨chartFraction I hw x,hx1⟩
    let v := divide I hw hc hdk 0 1 y
    have hv : z • v = chartEquiv I hw x := by
      have hh := smul_divide I hw hc hwc hdk 0 1 y
      apply Subtype.ext
      change z • (divide I hw hc hdk 0 1 y).val = chartFraction I hw x
      simpa only [pow_one,Submodule.coe_smul,Submodule.coe_inclusion] using congrArg Subtype.val hh
    have he : z • (chartEquiv I hw).symm v=x := by
      apply (chartEquiv I hw).injective
      rw [map_smul,LinearEquiv.apply_symm_apply]
      exact hv
    rw [←he]
    exact Submodule.smul_mem_smul hz Submodule.mem_top
  · apply Submodule.smul_le.mpr
    intro r hr x _
    rw [LinearMap.mem_ker,chartReduction_eq_zero_iff,map_smul]
    exact scalar_mem_next I hw hr (chartEquiv I hw x)

 

def exceptionalQuotientEquiv :
    (ReesChart I hw ⧸ (chartReduction I hw).ker) ≃ₗ[R] ExceptionalChart I hw :=
  LinearMap.quotKerEquivOfSurjective (chartReduction I hw) (chartReduction_surjective I hw)

end Lech.FilteredFraction

end

end OAI
