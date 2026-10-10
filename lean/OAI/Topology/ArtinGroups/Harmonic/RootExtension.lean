import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedMatrix

namespace OAI

namespace HarmonicArtin
open Matrix Geometric CoxeterExchange
open scoped Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I:Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

noncomputable def rootExtension (f:I→V) (x:I→ℝ) : V→ℝ := ∑ i,x i • Pi.single (f i) 1

omit [Fintype V] in
lemma rootExtension_apply (f:I→V) (hf:Function.Injective f) (x:I→ℝ) (i:I) :
    rootExtension f x (f i)=x i := by
  simp only [rootExtension,Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
  simp_rw [hf.eq_iff]
  simp

omit [Fintype V] [DecidableEq I] in
lemma rootExtension_outside (f:I→V) (x:I→ℝ) (v:V) (hv:v∉Set.range f) :
    rootExtension f x v=0 := by
  simp only [rootExtension,Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  have hi:v≠f i:=fun h=>hv ⟨i,h.symm⟩
  simp only [ite_eq_right hi,mul_zero]

omit [Fintype V] in
lemma rootExtension_restrict (f:I→V) (hf:Function.Injective f) (x:V→ℝ)
    (hx:∀ v,v∉Set.range f→x v=0) : rootExtension f (x∘f)=x := by
  ext v
  by_cases hv:v∈Set.range f
  · obtain ⟨i,rfl⟩:=hv
    exact rootExtension_apply f hf _ i
  · rw [rootExtension_outside f _ v hv,hx v hv]

omit [Fintype V] [DecidableEq I] in
lemma rootExtension_sub (f:I→V) (x y:I→ℝ) :
    rootExtension f (x-y)=rootExtension f x-rootExtension f y := by
  simp only [rootExtension,Pi.sub_apply,sub_smul,Finset.sum_sub_distrib]

omit [Fintype V] [DecidableEq I] in
lemma rootExtension_smul (f:I→V) (r:ℝ) (x:I→ℝ) :
    rootExtension f (r • x)=r • rootExtension f x := by
  simp only [rootExtension,Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]

omit [Fintype V] in
lemma rootExtension_single (f:I→V) (i:I) :
    rootExtension f (Pi.single i 1)=Pi.single (f i) 1 := by
  simp [rootExtension,Pi.single_apply]

omit [DecidableEq I] in
lemma rootExtension_mulVec (C:Matrix V V ℝ) (f:I→V) (x:I→ℝ) (i:I) :
    (C *ᵥ rootExtension f x) (f i)=(C.submatrix f f *ᵥ x) i := by
  unfold rootExtension
  rw [Matrix.mulVec_sum]
  simp only [Finset.sum_apply,Matrix.mulVec_smul,Pi.smul_apply,Matrix.mulVec_single,
    Matrix.col,Matrix.transpose_apply,Matrix.mulVec,dotProduct,
    Matrix.submatrix_apply,smul_eq_mul]
  simp [MulOpposite.op_one,one_smul,mul_comm]

lemma rowReflect_rootExtension (C:Matrix V V ℝ) (f:I→V) (i:I) (x:I→ℝ) :
    rowReflect C (f i) (rootExtension f x)=rootExtension f (rowReflect (C.submatrix f f) i x) := by
  simp only [rowReflect,rootExtension_mulVec,rootExtension_sub,rootExtension_smul,rootExtension_single]

lemma rowReflectWord_rootExtension (C:Matrix V V ℝ) (f:I→V) (w:List I) (x:I→ℝ) :
    rowReflectWord C (w.map f) (rootExtension f x)=
      rootExtension f (rowReflectWord (C.submatrix f f) w x) := by
  induction w with
  | nil=>rfl
  | cons i w ih=>
    change rowReflect C (f i) (rowReflectWord C (w.map f) (rootExtension f x))=_
    rw [ih,rowReflect_rootExtension]
    rfl

lemma rowReflectWord_harmonic (C:Matrix V V ℝ) (w:List V) (p:V→ℝ)
    (hp:∀ i∈w,(C *ᵥ p) i=0) : rowReflectWord C w p=p := by
  induction w with
  | nil=>rfl
  | cons i w ih=>
    change rowReflect C i (rowReflectWord C w p)=p
    rw [ih (fun j hj=>hp j (by simp [hj]))]
    simp only [rowReflect,hp i (by simp),zero_smul,sub_zero]

variable {S:Type*} [Fintype S] [LinearOrder S]

noncomputable def sourceRootInclusion (J:Set S) (j:J) : S⊕Unit := .inl (j:S)

omit [Fintype S] [LinearOrder S] in
lemma sourceRootInclusion_injective (J:Set S) : Function.Injective (sourceRootInclusion J) :=
  fun _ _ h=>Subtype.ext (Sum.inl.inj h)

omit [Fintype S] in
lemma source_folded_submatrix (M:CoxeterMatrix S) (J:Set S) :
    (fusionFoldedCartan (fusionLabelSize M) (coxeterFusionEdge M)).submatrix
      (sourceRootInclusion J) (sourceRootInclusion J)=cartan (restrictedMatrix M J) := by
  have hC : fusionFoldedCartan (fusionLabelSize M) (coxeterFusionEdge M)=framedCartan M := by
    convert fusionFoldedCartan_eq_framedCartan M using 1
    congr 1
    exact Subsingleton.elim _ _
  rw [hC]
  ext i j
  simp only [Matrix.submatrix_apply,sourceRootInclusion,framedCartan,cartan,restrictedMatrix_apply,
    Subtype.ext_iff]
  congr 1

lemma sourceRoot_word_representation (M:CoxeterMatrix S) (J:Set S) (w:List J) (x:J→ℝ) :
    rowReflectWord (fusionFoldedCartan (fusionLabelSize M) (coxeterFusionEdge M))
      (w.map (sourceRootInclusion J)) (rootExtension (sourceRootInclusion J) x)=
    rootExtension (sourceRootInclusion J)
      (representation (restrictedMatrix M J).toCoxeterSystem
        ((restrictedMatrix M J).toCoxeterSystem.wordProd w) x) := by
  rw [rowReflectWord_rootExtension,source_folded_submatrix,
    rowReflectWord_representation (restrictedMatrix M J).toCoxeterSystem]

end HarmonicArtin

end OAI
