import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshPathSpaces
import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshInsertionMatrix

namespace OAI

/-! The path-space loop identity and extension functor. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} [Fintype V] (G : SimpleGraph V)

/-- Inserting and then contracting a final backtrack multiplies by the
Perron eigenvalue. This is proved for the actual path matrices. -/
theorem meshContraction_loop (μ : V → ℝ) (hμ : ∀ v, 0<μ v) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v)
    (n : ℕ) (v : V) :
    meshContractionMatrix G μ n v * (meshContractionMatrix G μ n v).conjTranspose =
      (δ : ℂ) • (1 : Matrix (MeshPaths G n v) (MeshPaths G n v) ℂ) := by
  have h := insertion_matrix_mul_conjTranspose
    (fun up : {u : V // G.Adj u v} × MeshPaths G n v => meshInsertBacktrack G up.1 up.2)
    (meshInsertBacktrack_injective G) (fun u => (Real.sqrt (μ u/μ v) : ℂ))
  have hweight : (∑ u : {u : V // G.Adj u v},
      (Real.sqrt (μ u/μ v) : ℂ)*star (Real.sqrt (μ u/μ v) : ℂ))=(δ : ℂ) := by
    have hs : ∀ u : {u : V // G.Adj u v},
        (Real.sqrt (μ u/μ v) : ℂ)*star (Real.sqrt (μ u/μ v) : ℂ)=(μ u/μ v : ℝ) := by
      intro u
      rw [Complex.star_def,Complex.conj_ofReal,←Complex.ofReal_mul,
        Real.mul_self_sqrt (div_nonneg (hμ u).le (hμ v).le)]
    simp only [hs,←Complex.ofReal_sum]
    congr 1
    rw [←Finset.sum_div,heigen,mul_div_cancel_right₀ _ (ne_of_gt (hμ v))]
  rw [hweight] at h
  exact h

omit [Fintype V] in
lemma meshExtend_one (n : ℕ) (v : V) :
    meshExtendMatrix G (fun u => (1 : Matrix (MeshPaths G n u) (MeshPaths G n u) ℂ)) v=1 := by
  unfold meshExtendMatrix
  change Matrix.blockDiagonal'
    (1 : ∀ u : {u : V // G.Adj u v},
      Matrix (MeshPaths G n u.val) (MeshPaths G n u.val) ℂ) = _
  rw [Matrix.blockDiagonal'_one]
  ext p q
  simp only [Matrix.one_apply]
  change (if p=q then (1 : ℂ) else 0) =
    @ite ℂ (p=q) (Classical.propDecidable _) 1 0
  split_ifs <;> rfl

lemma meshExtend_mul {k m n : ℕ}
    (A : ∀ v, Matrix (MeshPaths G k v) (MeshPaths G m v) ℂ)
    (B : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ) (v : V) :
    meshExtendMatrix G (fun u => A u*B u) v=meshExtendMatrix G A v*meshExtendMatrix G B v :=
  Matrix.blockDiagonal'_mul _ _

omit [Fintype V] in
lemma meshExtend_adjoint {m n : ℕ}
    (A : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ) (v : V) :
    (meshExtendMatrix G A v).conjTranspose=meshExtendMatrix G (fun u => (A u).conjTranspose) v :=
  Matrix.blockDiagonal'_conjTranspose _

omit [Fintype V] in
lemma meshExtend_sub {m n : ℕ}
    (A B : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ) (v : V) :
    meshExtendMatrix G (fun u => A u-B u) v=meshExtendMatrix G A v-meshExtendMatrix G B v :=
  Matrix.blockDiagonal'_sub _ _

omit [Fintype V] in
lemma meshExtend_smul {m n : ℕ} (a : ℂ)
    (A : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ) (v : V) :
    meshExtendMatrix G (fun u => a • A u) v=a • meshExtendMatrix G A v :=
  Matrix.blockDiagonal'_smul a (fun u : {u : V // G.Adj u v} => A u.val)

end HarmonicArtin.ParabolicIntersections

end OAI
