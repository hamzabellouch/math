import Mathlib
import OAI.RingTheory.Multiplicity.BicomplexEuler

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ MonoidalCategory
universe u
variable {R : Type u} [CommRing R] {I : Ideal R} (ell : TorsionLength I)
  {ι : Type} [Fintype ι] [LinearOrder ι]
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p))
  (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
  (D : Diagram R ι) (hf : ∀ q,ell.finiteClass ((positiveZ D).homology q))

include B hflat hf in
 
lemma tensor_row_euler (p : ℤ) :
    finiteHomologyEuler ell
      ((((curriedTensor (ModuleCat.{u} R)).obj (F.X p)).mapHomologicalComplex (.up ℤ)).obj (positiveZ D))
      0 (Fintype.card ι) = (b p:ℝ)*finiteHomologyEuler ell (positiveZ D) 0 (Fintype.card ι) := by
  let := hflat p
  unfold finiteHomologyEuler
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have he := TensorIdeal.tensorHomology_length (F.X p) (b p) (B p) (positiveZ D) I ell (0+k) (hf _).1
  change (-1:ℝ)^k*(ell.value _).toReal=_
  rw [he,nsmul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_natCast]
  dsimp only [TorsionLength.realValue]
  ring

include B hflat hb hf in
 
lemma tensor_euler_rank :
    finiteHomologyEuler ell (tensorCech F D) (-(h:ℤ)) (h+Fintype.card ι)=
      (∑ k∈Finset.range (h+1),(-1:ℝ)^k*(b (-(h:ℤ)+k):ℝ))*
        finiteHomologyEuler ell (positiveZ D) 0 (Fintype.card ι) := by
  let K : BicomplexTotal.Double (R:=R) :=
    (((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj F).obj (positiveZ D)
  have hK (p : ℤ) (hp : p < -(h:ℤ) ∨ 0<p) : IsZero (K.X p) := by
    apply FiniteComplex.isZero_of_X
    intro q
    exact (tensorRight ((positiveZ D).X q)).map_isZero (hb p hp)
  have hq (p q : ℤ) (hq : q<0 ∨ (Fintype.card ι:ℤ)<q) : IsZero ((K.X p).homology q) := by
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact (tensorLeft (F.X p)).map_isZero (positiveZ_bounded D q (by omega))
  have hfin (p q : ℤ) : ell.finiteClass ((K.X p).homology q) := by
    let := hflat p
    exact ⟨TensorIdeal.tensorHomology_torsion (F.X p) (b p) (B p) (positiveZ D) I q (hf q).1,
      TensorIdeal.tensorHomology_length_finite (F.X p) (b p) (B p) (positiveZ D) I ell q (hf q).1 (hf q).2⟩
  have he := BicomplexTotal.euler_rows ell K h (Fintype.card ι) (h+Fintype.card ι) le_rfl hK hq hfin
  change finiteHomologyEuler ell (tensorCech F D) _ _=_ at he
  rw [he,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  change (-1:ℝ)^k*finiteHomologyEuler ell
    ((((curriedTensor (ModuleCat.{u} R)).obj (F.X (-(h:ℤ)+k))).mapHomologicalComplex (.up ℤ)).obj (positiveZ D)) _ _=_
  rw [tensor_row_euler ell F b B hflat D hf]
  ring

include B hflat hb hf in
lemma tensorCech_finite_of_positive (i : ℤ) : ell.finiteClass ((tensorCech F D).homology i) := by
  apply BicomplexTotal.devissage ell.finiteClass (-(h:ℤ)) (h+1) _ i
  · intro p hp
    apply FiniteComplex.isZero_of_X
    intro q
    exact (tensorRight ((positiveZ D).X q)).map_isZero (hb p (by omega))
  intro p
  apply ell.finiteClass.prop_of_iso (BicomplexTotal.singleHomologyIso _ p i).symm
  let := hflat p
  exact ⟨TensorIdeal.tensorHomology_torsion (F.X p) (b p) (B p) (positiveZ D) I _ (hf _).1,
    TensorIdeal.tensorHomology_length_finite (F.X p) (b p) (B p) (positiveZ D) I ell _ (hf _).1 (hf _).2⟩

include B hflat hb hf in
lemma tensor_euler_rank_zero
    (hbr : ∑ k∈Finset.range (h+1),(-1:ℝ)^k*(b (-(h:ℤ)+k):ℝ)=0) :
    tensorEuler ell F h D=0 := by
  unfold tensorEuler
  rw [tensor_euler_rank ell F h b B hflat hb D hf,hbr,zero_mul,mul_zero]
end Lech.FiniteModuleCech

end

end OAI
