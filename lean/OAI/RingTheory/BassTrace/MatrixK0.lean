import OAI.RingTheory.BassTrace.MatrixVanishing
import OAI.RingTheory.BassTrace.Definitions

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.K0

section

open scoped Classical BigOperators

variable {R : Type*} [Ring R]

lemma trace_reindex {α β : Type*} [Fintype α] [Fintype β]
    (j : α≃β) (a : Matrix α α R) :
    Matrix.trace (Matrix.reindexRingEquiv R j a)=Matrix.trace a := by
  change (∑i, a (j.symm i) (j.symm i))=∑i,a i i
  exact Equiv.sum_comp j.symm (fun i=>a i i)

lemma trace_directSum (e f : Idempotent R) :
    Matrix.trace (directSum e f).matrix=Matrix.trace e.matrix+Matrix.trace f.matrix := by
  rw [directSum,trace_reindex]
  simp only [Matrix.trace,Matrix.diag,Fintype.sum_sum_type,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₂₂]

variable {G : Type*} [_root_.Group G]

lemma relations_in_kernel (g : G) : relations (MonoidAlgebra ℂ G)≤(rawCoefficient g).ker := by
  apply (AddSubgroup.closure_le _).mpr
  intro x hx
  rcases hx with ⟨e,f,a,b,hab,hba,rfl⟩|⟨e,f,rfl⟩
  · change rawCoefficient g (FreeAbelianGroup.of e-FreeAbelianGroup.of f)=0
    simp only [map_sub,rawCoefficient,FreeAbelianGroup.lift_apply_of]
    apply sub_eq_zero.mpr
    rw [←hab,←hba]
    exact classCoefficient_matrix_mul_comm g a b
  · change rawCoefficient g (FreeAbelianGroup.of (directSum e f)-FreeAbelianGroup.of e-FreeAbelianGroup.of f)=0
    simp only [map_sub,rawCoefficient,FreeAbelianGroup.lift_apply_of,trace_directSum,classCoefficient_add]
    abel

def hsCoefficient (g : G) : Group (MonoidAlgebra ℂ G) →+ ℂ :=
  QuotientAddGroup.lift (relations (MonoidAlgebra ℂ G)) (rawCoefficient g) (relations_in_kernel g)

lemma hsCoefficient_classOf (g : G) (e : Idempotent (MonoidAlgebra ℂ G)) :
    hsCoefficient g (classOf e)=classCoefficient g (Matrix.trace e.matrix) := by
  simp [hsCoefficient,classOf,rawCoefficient]

end

section

open scoped Classical BigOperators

variable {G : Type*} [_root_.Group G]

lemma classTrace_apply (a : MonoidAlgebra ℂ G) (g : G) :
    classTrace a (ConjClasses.mk g)=classCoefficient g a := by
  unfold classTrace classCoefficient
  simp only [Finsupp.mapDomain,Finsupp.sum_apply,Finsupp.single_apply,
    ConjClasses.mk_eq_mk_iff_isConj]

lemma rawTrace_apply (z : FreeAbelianGroup (Idempotent (MonoidAlgebra ℂ G))) (g : G) :
    rawTrace z (ConjClasses.mk g)=rawCoefficient g z := by
  induction z using FreeAbelianGroup.induction_on with
  | zero => simp only [map_zero,Finsupp.zero_apply]
  | of e =>
    simp only [rawTrace,rawCoefficient,FreeAbelianGroup.lift_apply_of]
    exact classTrace_apply _ g
  | neg e he => simp only [map_neg,Finsupp.neg_apply,he]
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy]

lemma relations_in_trace_kernel : relations (MonoidAlgebra ℂ G)≤(rawTrace (G := G)).ker := by
  intro z hz
  change rawTrace z=0
  ext c
  obtain ⟨g,rfl⟩ := ConjClasses.mk_surjective c
  rw [rawTrace_apply,Finsupp.zero_apply]
  exact relations_in_kernel g hz

lemma HattoriStallings_apply (x : Group (MonoidAlgebra ℂ G)) (g : G) :
    HattoriStallings x (ConjClasses.mk g)=hsCoefficient g x := by
  induction x using QuotientAddGroup.induction_on with | H z =>
    exact rawTrace_apply z g

lemma HattoriStallings_classOf (e : Idempotent (MonoidAlgebra ℂ G)) :
    HattoriStallings (classOf e)=classTrace (Matrix.trace e.matrix) := by
  ext c
  obtain ⟨g,rfl⟩ := ConjClasses.mk_surjective c
  rw [HattoriStallings_apply,hsCoefficient_classOf,classTrace_apply]

end

open scoped Classical

theorem bassTraceK0 {G : Type*} [_root_.Group G]
    (x : Group (MonoidAlgebra ℂ G)) (g : G) (hg : ¬IsOfFinOrder g) :
    HattoriStallings x (ConjClasses.mk g)=0 := by
  rw [HattoriStallings_apply]
  induction x using QuotientAddGroup.induction_on with | H z =>
    change rawCoefficient g z=0
    induction z using FreeAbelianGroup.induction_on with
    | zero => exact map_zero _
    | of e =>
      simp only [rawCoefficient,FreeAbelianGroup.lift_apply_of]
      exact BassTrace.bassTrace e.matrix e.idem g hg
    | neg z hz => rw [map_neg,hz,neg_zero]
    | add z w hz hw => rw [map_add,hz,hw,add_zero]

theorem bassTraceK0_support {G : Type*} [_root_.Group G]
    (x : Group (MonoidAlgebra ℂ G)) :
    ↑(HattoriStallings x).support ⊆
      {c : ConjClasses G | ∃g : G,IsOfFinOrder g ∧ ConjClasses.mk g=c} := by
  intro c hc
  obtain ⟨g,rfl⟩ := ConjClasses.mk_surjective c
  refine ⟨g,?_,rfl⟩
  by_contra hg
  exact (Finsupp.mem_support_iff.mp hc) (bassTraceK0 x g hg)

end BassTrace.K0

end

end OAI
