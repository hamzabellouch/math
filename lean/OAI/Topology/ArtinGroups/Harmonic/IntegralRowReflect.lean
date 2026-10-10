import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.RowReflect
import OAI.Topology.ArtinGroups.Harmonic.IntegralQuadratic

namespace OAI

namespace HarmonicArtin
open Matrix
open scoped Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V:Type*} [Fintype V] [DecidableEq V]

def integralRowReflect (C:Matrix V V ℤ) (i:V) (x:V → ℤ) : V → ℤ :=
  x-(C *ᵥ x) i • Pi.single i 1

omit [DecidableEq V] in
lemma integralQuadratic_dot (C:Matrix V V ℤ) (x:V → ℤ) :
    integralQuadratic C x=x ⬝ᵥ (C *ᵥ x) := by
  simp only [integralQuadratic,Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma integralRowReflect_norm (C:Matrix V V ℤ) (hs:∀ i j,C i j=C j i)
    (hd:∀ i,C i i=2) (i:V) (x:V → ℤ) :
    integralQuadratic C (integralRowReflect C i x)=integralQuadratic C x := by
  rw [integralQuadratic_dot,integralQuadratic_dot]
  unfold integralRowReflect
  simp only [Matrix.mulVec_sub,Matrix.mulVec_smul,sub_dotProduct,dotProduct_sub,
    smul_dotProduct,dotProduct_smul,smul_eq_mul,Matrix.mulVec_single,single_dotProduct,
    Matrix.col,Matrix.transpose_apply,hd]
  have he : x ⬝ᵥ (fun j=>C j i)=(C *ᵥ x) i := by
    simp only [dotProduct,Matrix.mulVec]
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i,mul_comm]
  simp only [MulOpposite.op_one,one_smul,one_mul]
  change x ⬝ᵥ (C *ᵥ x) - (C *ᵥ x) i * (C *ᵥ x) i -
    (C *ᵥ x) i * (x ⬝ᵥ (fun j=>C j i) - (C *ᵥ x) i * 2)=x ⬝ᵥ (C *ᵥ x)
  rw [he]
  ring

def integralReflectWord (C:Matrix V V ℤ) (w:List V) (x:V → ℤ) : V → ℤ :=
  w.foldr (integralRowReflect C) x

lemma integralReflectWord_norm (C:Matrix V V ℤ) (hs:∀ i j,C i j=C j i)
    (hd:∀ i,C i i=2) (w:List V) (i:V) :
    integralQuadratic C (integralReflectWord C w (Pi.single i 1))=2 := by
  induction w with
  | nil => simp [integralReflectWord,integralQuadratic,Pi.single_apply,hd]
  | cons j w ih =>
    change integralQuadratic C (integralRowReflect C j
      (integralReflectWord C w (Pi.single i 1)))=2
    rw [integralRowReflect_norm C hs hd,ih]

theorem integralReflectWord_sign (C:Matrix V V ℤ) (hs:∀ i j,C i j=C j i)
    (hd:∀ i,C i i=2) (hoff:∀ i j,i≠j → C i j≤0)
    (hp:(C.map (Int.cast:ℤ → ℝ)).PosDef) (w:List V) (i:V) :
    (∀ j,0 ≤ integralReflectWord C w (Pi.single i 1) j) ∨
    (∀ j,integralReflectWord C w (Pi.single i 1) j≤0) :=
  integral_root_sign C hs hd hoff hp _ (integralReflectWord_norm C hs hd w i)

lemma integralRowReflect_cast (C:Matrix V V ℤ) (i:V) (x:V → ℤ) :
    (fun j=>(integralRowReflect C i x j:ℝ))=
      rowReflect (C.map (Int.cast:ℤ → ℝ)) i (fun j=>(x j:ℝ)) := by
  ext j
  simp [integralRowReflect,rowReflect,Matrix.mulVec,dotProduct,Pi.single_apply]

lemma integralReflectWord_cast (C:Matrix V V ℤ) (w:List V) (x:V → ℤ) :
    (fun j=>(integralReflectWord C w x j:ℝ))=
      rowReflectWord (C.map (Int.cast:ℤ → ℝ)) w (fun j=>(x j:ℝ)) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (fun j=>(integralRowReflect C i (integralReflectWord C w x) j:ℝ))=_
    rw [integralRowReflect_cast,ih]
    rfl

end HarmonicArtin

end OAI
