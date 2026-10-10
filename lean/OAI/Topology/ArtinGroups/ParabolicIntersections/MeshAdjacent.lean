import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshContraction

namespace OAI

/-! Adjacent contraction identities on the actual finite path spaces. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} [Fintype V] (G : SimpleGraph V)

lemma meshContraction_mul (μ : V → ℝ) (n : ℕ) (v : V) {R : Type} [Fintype R]
    (B : Matrix (MeshPaths G (n+2) v) R ℂ) (p : MeshPaths G n v) (r : R) :
    (meshContractionMatrix G μ n v * B) p r =
      ∑ u : {u : V // G.Adj u v},
        (Real.sqrt (μ u/μ v) : ℂ) * B (meshInsertBacktrack G u p) r := by
  change (∑ q, (∑ u : {u : V // G.Adj u v},
    if q=meshInsertBacktrack G u p then (Real.sqrt (μ u/μ v) : ℂ) else 0)*B q r)=_
  simp only [Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  simp

lemma meshContraction_head (μ : V → ℝ) (n : ℕ) (v : V)
    (p : MeshPaths G n v) (u : {u : V // G.Adj u v})
    (q : MeshPaths G (n+1) u.val) :
    meshContractionMatrix G μ n v p ⟨u,q⟩ =
      if q=⟨⟨v,u.property.symm⟩,p⟩ then (Real.sqrt (μ u/μ v) : ℂ) else 0 := by
  change (∑ w : {w : V // G.Adj w v},
    if (⟨u,q⟩ : MeshPaths G (n+2) v)=meshInsertBacktrack G w p
    then (Real.sqrt (μ w/μ v) : ℂ) else 0)=_
  rw [Finset.sum_eq_single u]
  · by_cases hq : q=⟨⟨v,u.property.symm⟩,p⟩
    · subst q
      simp only [meshInsertBacktrack,ite_true]
      exact (ite_eq_left rfl).symm
    · have hne : (⟨u,q⟩ : MeshPaths G (n+2) v)≠meshInsertBacktrack G u p := by
        intro h
        exact hq (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
      simp only [hne,hq,ite_false]
  · intro w _ hwu
    have hne : (⟨u,q⟩ : MeshPaths G (n+2) v)≠meshInsertBacktrack G w p := by
      intro h
      exact hwu (congrArg Sigma.fst h).symm
    simp [hne]
  · simp

lemma meshContraction_return (μ : V → ℝ) (n : ℕ) (v : V)
    (u : {u : V // G.Adj u v}) (p : MeshPaths G (n+1) v)
    (r : MeshPaths G n u.val) :
    meshContractionMatrix G μ n u.val r ⟨⟨v,u.property.symm⟩,p⟩ =
      if p=⟨u,r⟩ then (Real.sqrt (μ v/μ u) : ℂ) else 0 := by
  simpa only using meshContraction_head G μ n u.val r ⟨v,u.property.symm⟩ p

omit [Fintype V] in
lemma mesh_sqrt_reciprocal (μ : V → ℝ) (hμ : ∀ v, 0<μ v) (u v : V) :
    (Real.sqrt (μ u/μ v) : ℂ)*(Real.sqrt (μ v/μ u) : ℂ)=1 := by
  rw [←Complex.ofReal_mul,←Real.sqrt_mul (div_nonneg (hμ u).le (hμ v).le)]
  have hratio : μ u/μ v*(μ v/μ u)=1 := by
    field_simp [ne_of_gt (hμ u),ne_of_gt (hμ v)]
  rw [hratio,Real.sqrt_one,Complex.ofReal_one]

/-- Contracting after insertion at the preceding position is the identity.
The two weights are reciprocal positive square roots. -/
theorem meshContraction_adjacent (μ : V → ℝ) (hμ : ∀ v, 0<μ v)
    (n : ℕ) (v : V) :
    meshContractionMatrix G μ (n+1) v *
      meshExtendMatrix G (fun u => (meshContractionMatrix G μ n u).conjTranspose) v =
      (1 : Matrix (MeshPaths G (n+1) v) (MeshPaths G (n+1) v) ℂ) := by
  ext p r
  rw [meshContraction_mul]
  rw [Matrix.one_apply]
  obtain ⟨u,r⟩ := r
  let f (w : {w : V // G.Adj w v}) : MeshPaths G (n+2) w.val :=
    ⟨⟨v,w.property.symm⟩,p⟩
  change (∑ w : {w : V // G.Adj w v}, (Real.sqrt (μ w/μ v) : ℂ)*
    Matrix.blockDiagonal' (fun z : {z : V // G.Adj z v} =>
      (meshContractionMatrix G μ n z.val).conjTranspose)
      ⟨w,f w⟩ ⟨u,r⟩)=_
  rw [Finset.sum_eq_single u]
  · rw [Matrix.blockDiagonal'_apply_eq,Matrix.conjTranspose_apply,meshContraction_return]
    split_ifs with h
    · rw [Complex.star_def,Complex.conj_ofReal,mesh_sqrt_reciprocal μ hμ]
    · simp
  · intro w _ hwu
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hwu,mul_zero]
  · simp

end HarmonicArtin.ParabolicIntersections

end OAI
