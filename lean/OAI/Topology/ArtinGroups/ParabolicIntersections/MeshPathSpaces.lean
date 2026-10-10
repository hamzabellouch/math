import Mathlib

namespace OAI

/-! The actual finite path spaces and weighted last-backtrack contractions. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (G : SimpleGraph V)

/-- Paths of length `n`, indexed by their final vertex. The recursive
presentation makes extension of prefix operators a block-diagonal map. -/
def MeshPaths : ℕ → V → Type
  | 0, _ => PUnit
  | n+1, v => Σ u : {u : V // G.Adj u v}, MeshPaths n u.val

noncomputable instance meshPathsFintype [Fintype V] (n : ℕ) (v : V) : Fintype (MeshPaths G n v) := by
  induction n generalizing v with
  | zero => change Fintype PUnit; infer_instance
  | succ n ih =>
    change Fintype (Σ u : {u : V // G.Adj u v}, MeshPaths G n u.val)
    let (u : V) : Fintype (MeshPaths G n u) := ih u
    infer_instance

/-- Attach the last two edges `v,u,v` to a path ending at `v`. -/
def meshInsertBacktrack {n : ℕ} {v : V} (u : {u : V // G.Adj u v})
    (p : MeshPaths G n v) : MeshPaths G (n+2) v :=
  ⟨u,⟨⟨v,u.property.symm⟩,p⟩⟩

lemma meshInsertBacktrack_injective {n : ℕ} {v : V} :
    Function.Injective (fun up : {u : V // G.Adj u v} × MeshPaths G n v =>
      meshInsertBacktrack G up.1 up.2) := by
  rintro ⟨u,p⟩ ⟨w,q⟩ h
  change (⟨u,⟨⟨v,u.property.symm⟩,p⟩⟩ : MeshPaths G (n+2) v)=
    ⟨w,⟨⟨v,w.property.symm⟩,q⟩⟩ at h
  obtain ⟨hu,hinner⟩ := Sigma.mk.inj_iff.mp h
  cases hu
  have hp := (Sigma.mk.inj_iff.mp (eq_of_heq hinner)).2
  exact Prod.ext rfl (eq_of_heq hp)

variable [Fintype V]

/-- The contraction coefficient is the positive square root used in the
essential-path representation of the mesh algebra. -/
noncomputable def meshContractionMatrix (μ : V → ℝ) (n : ℕ) (v : V) :
    Matrix (MeshPaths G n v) (MeshPaths G (n+2) v) ℂ :=
  fun p q => ∑ u : {u : V // G.Adj u v},
    if q=meshInsertBacktrack G u p then (Real.sqrt (μ u/μ v) : ℂ) else 0

/-- Extending a prefix operator by one edge, without changing that edge. -/
noncomputable def meshExtendMatrix {m n : ℕ}
    (T : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ) (v : V) :
    Matrix (MeshPaths G (m+1) v) (MeshPaths G (n+1) v) ℂ :=
  Matrix.blockDiagonal' (fun u : {u : V // G.Adj u v} => T u.val)

end HarmonicArtin.ParabolicIntersections

end OAI
