import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshPathSpaces

namespace OAI

/-! Evaluating complex path matrices in an arbitrary complex module. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I J K R : Type} [Fintype I] [Fintype J] [Fintype K]
variable [AddCommGroup R] [Module ℂ R]

noncomputable def meshApply (A : Matrix I J ℂ) (f : I → R) (q : J) : R :=
  ∑ p, A p q • f p

omit [Fintype J] [Fintype K] in
lemma meshApply_sub (A B : Matrix I J ℂ) (f : I → R) :
    meshApply (A-B) f=meshApply A f-meshApply B f := by
  funext q
  simp only [meshApply,Matrix.sub_apply,sub_smul,Finset.sum_sub_distrib,Pi.sub_apply]

omit [Fintype J] [Fintype K] in
lemma meshApply_smul (a : ℂ) (A : Matrix I J ℂ) (f : I → R) :
    meshApply (a • A) f=a • meshApply A f := by
  funext q
  simp only [meshApply,Matrix.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum,Pi.smul_apply]

omit [Fintype K] in
lemma meshApply_mul (A : Matrix I J ℂ) (B : Matrix J K ℂ) (f : I → R) :
    meshApply (A*B) f=meshApply B (meshApply A f) := by
  funext q
  simp only [meshApply,Matrix.mul_apply,Finset.sum_smul,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro p _
  rw [mul_comm]

omit [Fintype J] [Fintype K] in
lemma meshApply_one (f : I → R) : meshApply (1 : Matrix I I ℂ) f=f := by
  funext q
  simp [meshApply,Matrix.one_apply]

omit [Fintype J] [Fintype K] in
lemma meshApply_zero (f : I → R) : meshApply (0 : Matrix I J ℂ) f=0 := by
  funext q
  simp [meshApply]

omit [Fintype J] [Fintype K] in
lemma meshApply_zero_right (A : Matrix I J ℂ) : meshApply A (0 : I → R)=0 := by
  funext q
  simp [meshApply]

variable {V : Type} [Fintype V] (G : SimpleGraph V)

omit [Fintype I] [Fintype J] [Fintype K] in
/-- Extending a prefix matrix commutes with a linear last-edge operation. -/
lemma meshApply_extend {m n : ℕ}
    (A : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ)
    (f : ∀ v, MeshPaths G m v → R) (v : V)
    (L : ∀ _u : {u : V // G.Adj u v}, R →ₗ[ℂ] R) :
    meshApply (meshExtendMatrix G A v)
      (fun p : MeshPaths G (m+1) v => L p.1 (f p.1.val p.2)) =
      fun q : MeshPaths G (n+1) v => L q.1 (meshApply (A q.1.val) (f q.1.val) q.2) := by
  funext q
  obtain ⟨u,q⟩ := q
  change (∑ p : Σ w : {w : V // G.Adj w v}, MeshPaths G m w.val,
    Matrix.blockDiagonal' (fun w : {w : V // G.Adj w v} => A w.val) p ⟨u,q⟩ •
      L p.1 (f p.1.val p.2))=_
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single u]
  · simp only [Matrix.blockDiagonal'_apply_eq,meshApply,map_sum,map_smul]
  · intro w _ hwu
    apply Finset.sum_eq_zero
    intro p _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hwu,zero_smul]
  · simp

end HarmonicArtin.ParabolicIntersections

end OAI
