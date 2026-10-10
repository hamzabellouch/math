import Mathlib
import OAI.RingTheory.Multiplicity.DuttaData

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex HomComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R]
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
variable (t : F.X (i+1) ⟶ F.X i)

def elementaryBackward (a b : ℤ) (h : (ComplexShape.up ℤ).Rel b a) : F.X a ⟶ F.X b :=
  (Cochain.single t (-1)).v a b (by change b+1=a at h; omega)

def elementaryProjector : F ⟶ F := Homotopy.nullHomotopicMap' (elementaryBackward F i t)

def elementaryProjectorNull : Homotopy (elementaryProjector F i t) 0 :=
  Homotopy.nullHomotopy' (elementaryBackward F i t)

lemma elementaryProjector_f_left :
    (elementaryProjector F i t).f i = F.d i (i+1) ≫ t := by
  rw [elementaryProjector,Homotopy.nullHomotopicMap'_f
    (show (ComplexShape.up ℤ).Rel (i-1) i by simp)
    (show (ComplexShape.up ℤ).Rel i (i+1) by simp)]
  simp only [elementaryBackward,Cochain.single_v]
  rw [Cochain.single_v_eq_zero _ _ _ _ _ (by omega),zero_comp,add_zero]

lemma elementaryProjector_f_right :
    (elementaryProjector F i t).f (i+1) = t ≫ F.d i (i+1) := by
  rw [elementaryProjector,Homotopy.nullHomotopicMap'_f
    (show (ComplexShape.up ℤ).Rel i (i+1) by simp)
    (show (ComplexShape.up ℤ).Rel (i+1) (i+1+1) by simp)]
  simp only [elementaryBackward,Cochain.single_v]
  rw [Cochain.single_v_eq_zero _ _ _ _ _ (by omega),comp_zero,zero_add]

lemma elementaryProjector_f_other (j : ℤ) (hj : j ≠ i) (hj' : j ≠ i+1) :
    (elementaryProjector F i t).f j = 0 := by
  rw [elementaryProjector,Homotopy.nullHomotopicMap'_f
    (show (ComplexShape.up ℤ).Rel (j-1) j by simp)
    (show (ComplexShape.up ℤ).Rel j (j+1) by simp)]
  simp only [elementaryBackward]
  rw [Cochain.single_v_eq_zero _ _ _ _ _ (by omega),
    Cochain.single_v_eq_zero _ _ _ _ _ hj',comp_zero,zero_comp,add_zero]

lemma elementaryProjector_idempotent (ht : t ≫ F.d i (i+1) ≫ t = t) :
    elementaryProjector F i t ≫ elementaryProjector F i t = elementaryProjector F i t := by
  apply HomologicalComplex.hom_ext
  intro j
  simp only [comp_f]
  by_cases hj : j=i
  · subst j
    rw [elementaryProjector_f_left,Category.assoc,ht]
  · by_cases hj' : j=i+1
    · subst j
      rw [elementaryProjector_f_right,← Category.assoc,Category.assoc t,ht]
    · rw [elementaryProjector_f_other F i t j hj hj',zero_comp]
end Lech

end

end OAI
