import OAI.RingTheory.BassTrace.MatrixK0

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.RightProjective

section

open scoped Classical BigOperators

open MulOpposite

variable {R : Type*} [Ring R]

lemma unopTranspose_mul {l m n : Type*} [Fintype m]
    (a : Matrix l m Rᵐᵒᵖ) (b : Matrix m n Rᵐᵒᵖ) :
    unopTranspose (a*b)=unopTranspose b*unopTranspose a := by
  ext i j
  simp only [unopTranspose,Matrix.mul_apply]
  change (opAddEquiv.symm : Rᵐᵒᵖ≃+R) (∑k,a j k*b k i)=_
  rw [map_sum]
  rfl

lemma rightMatrix_comp {l m n : ℕ}
    (f : (Fin l →Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] (Fin m →Rᵐᵒᵖ))
    (g : (Fin m →Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] (Fin n →Rᵐᵒᵖ)) :
    rightMatrix (g.comp f)=rightMatrix g*rightMatrix f := by
  simp only [rightMatrix,LinearMap.toMatrixRight'_comp,unopTranspose_mul]

variable {M N : Type*} [AddCommGroup M] [Module Rᵐᵒᵖ M]
  [AddCommGroup N] [Module Rᵐᵒᵖ N]

lemma Retraction.exists_ [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    Nonempty (Retraction R M) := by
  obtain ⟨n,f,g,_,_,h⟩ := Module.Finite.exists_comp_eq_id_of_projective Rᵐᵒᵖ M
  exact ⟨⟨n,f,g,h⟩⟩

lemma classOf_eq_of_rectangular (e f : K0.Idempotent R)
    (a : Matrix (Fin e.size) (Fin f.size) R)
    (b : Matrix (Fin f.size) (Fin e.size) R) (hab : a*b=e.matrix) (hba : b*a=f.matrix) :
    K0.classOf e=K0.classOf f := by
  apply sub_eq_zero.mp
  change (QuotientAddGroup.mk' (K0.relations R)) (FreeAbelianGroup.of e)-
    (QuotientAddGroup.mk' (K0.relations R)) (FreeAbelianGroup.of f)=0
  rw [←map_sub]
  change (QuotientAddGroup.mk (FreeAbelianGroup.of e-FreeAbelianGroup.of f) : K0.Group R)=0
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact AddSubgroup.subset_closure (Or.inl ⟨e,f,a,b,hab,hba,rfl⟩)

lemma Retraction.class_eq (r s : Retraction R M) :
    K0.classOf r.idempotent=K0.classOf s.idempotent := by
  apply classOf_eq_of_rectangular _ _
    (rightMatrix (r.inc.comp s.proj)) (rightMatrix (s.inc.comp r.proj))
  · change rightMatrix (r.inc.comp s.proj)*rightMatrix (s.inc.comp r.proj)=
      rightMatrix (r.inc.comp r.proj)
    rw [←rightMatrix_comp]
    congr 1
    calc (r.inc.comp s.proj).comp (s.inc.comp r.proj) =
        r.inc.comp ((s.proj.comp s.inc).comp r.proj) := by simp only [LinearMap.comp_assoc]
      _ = r.inc.comp r.proj := by rw [s.split,LinearMap.id_comp]
  · change rightMatrix (s.inc.comp r.proj)*rightMatrix (r.inc.comp s.proj)=
      rightMatrix (s.inc.comp s.proj)
    rw [←rightMatrix_comp]
    congr 1
    calc (s.inc.comp r.proj).comp (r.inc.comp s.proj) =
        s.inc.comp ((r.proj.comp r.inc).comp s.proj) := by simp only [LinearMap.comp_assoc]
      _ = s.inc.comp s.proj := by rw [r.split,LinearMap.id_comp]

lemma Retraction.transport_idempotent (r : Retraction R M) (u : M≃ₗ[Rᵐᵒᵖ] N) :
    (r.transport u).idempotent=r.idempotent := by
  dsimp only [Retraction.idempotent]
  congr 1
  change rightMatrix ((r.inc.comp u.symm.toLinearMap).comp (u.toLinearMap.comp r.proj))=
    rightMatrix (r.inc.comp r.proj)
  congr 1
  apply LinearMap.ext
  intro x
  change r.inc (u.symm (u (r.proj x)))=r.inc (r.proj x)
  rw [u.symm_apply_apply]

end

open scoped Classical BigOperators

open MulOpposite

variable {R : Type*} [Ring R]

lemma freeSplit_apply_left (n m : ℕ) (v : Fin (n+m)→Rᵐᵒᵖ) (i : Fin n) :
    (freeSplit n m v).1 i=v (finSumFinEquiv (Sum.inl i)) := rfl

lemma freeSplit_apply_right (n m : ℕ) (v : Fin (n+m)→Rᵐᵒᵖ) (i : Fin m) :
    (freeSplit n m v).2 i=v (finSumFinEquiv (Sum.inr i)) := rfl

lemma freeSplit_symm_left (n m : ℕ) (v : Fin n→Rᵐᵒᵖ) (w : Fin m→Rᵐᵒᵖ) (i : Fin n) :
    (freeSplit n m).symm (v,w) (finSumFinEquiv (Sum.inl i))=v i := by
  have h := congrArg (fun x=>(x.1 : Fin n→Rᵐᵒᵖ) i) ((freeSplit (R := R) n m).apply_symm_apply (v,w))
  exact h

lemma freeSplit_symm_right (n m : ℕ) (v : Fin n→Rᵐᵒᵖ) (w : Fin m→Rᵐᵒᵖ) (i : Fin m) :
    (freeSplit n m).symm (v,w) (finSumFinEquiv (Sum.inr i))=w i := by
  have h := congrArg (fun x=>(x.2 : Fin m→Rᵐᵒᵖ) i) ((freeSplit (R := R) n m).apply_symm_apply (v,w))
  exact h

lemma freeSplit_single_left (n m : ℕ) (i : Fin n) :
    freeSplit (R := R) n m (Pi.single (finSumFinEquiv (Sum.inl i)) 1)=(Pi.single i 1,0) := by
  apply Prod.ext
  · ext j
    rw [freeSplit_apply_left]
    simp only [Pi.single_apply,Equiv.apply_eq_iff_eq,Sum.inl.injEq]
  · ext j
    rw [freeSplit_apply_right]
    simp only [Pi.single_apply,Equiv.apply_eq_iff_eq,Sum.inr_ne_inl,ite_false,Pi.zero_apply]

lemma freeSplit_single_right (n m : ℕ) (i : Fin m) :
    freeSplit (R := R) n m (Pi.single (finSumFinEquiv (Sum.inr i)) 1)=(0,Pi.single i 1) := by
  apply Prod.ext
  · ext j
    rw [freeSplit_apply_left]
    simp only [Pi.single_apply,Equiv.apply_eq_iff_eq,Sum.inl_ne_inr,ite_false,Pi.zero_apply]
  · ext j
    rw [freeSplit_apply_right]
    simp only [Pi.single_apply,Equiv.apply_eq_iff_eq,Sum.inr.injEq]

variable {M N : Type*} [AddCommGroup M] [Module Rᵐᵒᵖ M]
  [AddCommGroup N] [Module Rᵐᵒᵖ N]

lemma rightMatrix_apply {m n : ℕ}
    (f : (Fin m→Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] (Fin n→Rᵐᵒᵖ)) (i : Fin n) (j : Fin m) :
    rightMatrix f i j=unop (f (Pi.single j 1) i) := rfl

lemma Retraction.prod_matrix (r : Retraction R M) (s : Retraction R N) :
    (r.prod s).idempotent.matrix=(K0.directSum r.idempotent s.idempotent).matrix := by
  ext i j
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  change unop ((freeSplit r.size s.size).symm ((r.inc.prodMap s.inc)
    ((r.proj.prodMap s.proj) ((freeSplit r.size s.size)
      (Pi.single (finSumFinEquiv j) 1)))) (finSumFinEquiv i))=
    Matrix.fromBlocks (rightMatrix (r.inc.comp r.proj)) 0 0 (rightMatrix (s.inc.comp s.proj))
      (finSumFinEquiv.symm (finSumFinEquiv i)) (finSumFinEquiv.symm (finSumFinEquiv j))
  simp only [Equiv.symm_apply_apply]
  cases i with | inl i => ?_ | inr i => ?_
  all_goals cases j with | inl j => ?_ | inr j => ?_
  · rw [freeSplit_single_left]
    simp only [LinearMap.prodMap_apply,map_zero,freeSplit_symm_left,Matrix.fromBlocks_apply₁₁]
    rfl
  · rw [freeSplit_single_right]
    simp only [LinearMap.prodMap_apply,map_zero,freeSplit_symm_left,Matrix.fromBlocks_apply₁₂,
      Pi.zero_apply,unop_zero,Matrix.zero_apply]
  · rw [freeSplit_single_left]
    simp only [LinearMap.prodMap_apply,map_zero,freeSplit_symm_right,Matrix.fromBlocks_apply₂₁,
      Pi.zero_apply,unop_zero,Matrix.zero_apply]
  · rw [freeSplit_single_right]
    simp only [LinearMap.prodMap_apply,map_zero,freeSplit_symm_right,Matrix.fromBlocks_apply₂₂]
    rfl

lemma Retraction.prod_idempotent (r : Retraction R M) (s : Retraction R N) :
    (r.prod s).idempotent=K0.directSum r.idempotent s.idempotent := by
  dsimp only [Retraction.idempotent, K0.directSum]
  congr 1
  exact r.prod_matrix s

lemma classOf_directSum (e f : K0.Idempotent R) :
    K0.classOf (K0.directSum e f)=K0.classOf e+K0.classOf f := by
  apply sub_eq_zero.mp
  change QuotientAddGroup.mk' (K0.relations R) (FreeAbelianGroup.of (K0.directSum e f))-
    (QuotientAddGroup.mk' (K0.relations R) (FreeAbelianGroup.of e)+
    QuotientAddGroup.mk' (K0.relations R) (FreeAbelianGroup.of f))=0
  rw [←map_add,←map_sub]
  change (QuotientAddGroup.mk (FreeAbelianGroup.of (K0.directSum e f)-
    (FreeAbelianGroup.of e+FreeAbelianGroup.of f)) : K0.Group R)=0
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  rw [sub_add_eq_sub_sub]
  exact AddSubgroup.subset_closure (Or.inr ⟨e,f,rfl⟩)

end BassTrace.RightProjective

end

end OAI
