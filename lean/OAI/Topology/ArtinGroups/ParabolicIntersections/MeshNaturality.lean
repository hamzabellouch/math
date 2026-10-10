import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshAdjacent

namespace OAI

/-! A prefix operator commutes with contraction of the final backtrack. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} [Fintype V] (G : SimpleGraph V)

lemma meshContraction_insert (μ : V → ℝ) (n : ℕ) (v : V)
    (p q : MeshPaths G n v) (u : {u : V // G.Adj u v}) :
    meshContractionMatrix G μ n v p (meshInsertBacktrack G u q)=
      if q=p then (Real.sqrt (μ u/μ v) : ℂ) else 0 := by
  calc
    _ = @ite ℂ ((⟨⟨v,u.property.symm⟩,q⟩ : MeshPaths G (n+1) u.val)=
        ⟨⟨v,u.property.symm⟩,p⟩) (Classical.propDecidable _)
        (Real.sqrt (μ u/μ v) : ℂ) 0 :=
      meshContraction_head G μ n v p u ⟨⟨v,u.property.symm⟩,q⟩
    _ = _ := by
      have he : (⟨⟨v,u.property.symm⟩,q⟩ : MeshPaths G (n+1) u.val)=
          ⟨⟨v,u.property.symm⟩,p⟩ ↔ q=p := by
        constructor
        · intro h
          exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
        · rintro rfl
          rfl
      simp only [he]

lemma meshContraction_no_return (μ : V → ℝ) (n : ℕ) (v : V)
    (p : MeshPaths G n v) (u : {u : V // G.Adj u v})
    (w : {w : V // G.Adj w u.val}) (q : MeshPaths G n w.val) (hw : w.val≠v) :
    meshContractionMatrix G μ n v p ⟨u,⟨w,q⟩⟩=0 := by
  calc
    _ = @ite ℂ ((⟨w,q⟩ : MeshPaths G (n+1) u.val)=⟨⟨v,u.property.symm⟩,p⟩)
      (Classical.propDecidable _) (Real.sqrt (μ u/μ v) : ℂ) 0 :=
        meshContraction_head G μ n v p u ⟨w,q⟩
    _ = 0 := by
      apply ite_eq_right
      intro he
      exact hw (congrArg (fun z => (Sigma.fst z).val) he)

omit [Fintype V] in
lemma meshExtend_twice_insert {m n : ℕ}
    (A : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ) (v : V)
    (p : MeshPaths G m v) (q : MeshPaths G n v)
    (u w : {u : V // G.Adj u v}) :
    meshExtendMatrix G (meshExtendMatrix G A) v
      (meshInsertBacktrack G u p) (meshInsertBacktrack G w q)=
        if u=w then A v p q else 0 := by
  let lp : MeshPaths G (m+1) u.val := ⟨⟨v,u.property.symm⟩,p⟩
  let rp : MeshPaths G (n+1) w.val := ⟨⟨v,w.property.symm⟩,q⟩
  change Matrix.blockDiagonal' (fun z : {z : V // G.Adj z v} =>
    meshExtendMatrix G A z.val) ⟨u,lp⟩ ⟨w,rp⟩=_
  by_cases h : u=w
  · subst w
    rw [Matrix.blockDiagonal'_apply_eq,ite_eq_left rfl]
    change Matrix.blockDiagonal' (fun z : {z : V // G.Adj z u.val} => A z.val)
      ⟨⟨v,u.property.symm⟩,p⟩ ⟨⟨v,u.property.symm⟩,q⟩=_
    exact Matrix.blockDiagonal'_apply_eq _ _ _ _
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,ite_eq_right h]

omit [Fintype V] in
lemma meshExtend_twice_no_return {m n : ℕ}
    (A : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ) (v : V)
    (p : MeshPaths G m v) (u w : {u : V // G.Adj u v})
    (x : {x : V // G.Adj x w.val}) (q : MeshPaths G n x.val) (hx : x.val≠v) :
    meshExtendMatrix G (meshExtendMatrix G A) v
      (meshInsertBacktrack G u p) ⟨w,⟨x,q⟩⟩=0 := by
  let lp : MeshPaths G (m+1) u.val := ⟨⟨v,u.property.symm⟩,p⟩
  let rp : MeshPaths G (n+1) w.val := ⟨x,q⟩
  change Matrix.blockDiagonal' (fun z : {z : V // G.Adj z v} =>
    meshExtendMatrix G A z.val) ⟨u,lp⟩ ⟨w,rp⟩=0
  by_cases h : u=w
  · subst w
    rw [Matrix.blockDiagonal'_apply_eq]
    change Matrix.blockDiagonal' (fun z : {z : V // G.Adj z u.val} => A z.val)
      ⟨⟨v,u.property.symm⟩,p⟩ ⟨x,q⟩=0
    apply Matrix.blockDiagonal'_apply_ne
    intro he
    exact hx (congrArg Subtype.val he).symm
  · exact Matrix.blockDiagonal'_apply_ne _ _ _ h

/-- No property of the prefix operator is needed: the final pair is
disjoint from it, so contraction is natural for every endpoint family. -/
theorem meshContraction_naturality (μ : V → ℝ) {m n : ℕ}
    (A : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ) (v : V) :
    meshContractionMatrix G μ m v * meshExtendMatrix G (meshExtendMatrix G A) v =
      A v * meshContractionMatrix G μ n v := by
  ext p r
  rw [meshContraction_mul]
  obtain ⟨u,w,q⟩ := r
  by_cases hw : w.val=v
  · have he : w=⟨v,u.property.symm⟩ := Subtype.ext hw
    subst w
    change (∑ x : {x : V // G.Adj x v}, (Real.sqrt (μ x/μ v) : ℂ)*
      meshExtendMatrix G (meshExtendMatrix G A) v
        (meshInsertBacktrack G x p) (meshInsertBacktrack G u q))=_
    simp only [meshExtend_twice_insert,mul_ite,mul_zero]
    rw [Finset.sum_ite_eq']
    change _ = ∑ t : MeshPaths G n v,
      A v p t * meshContractionMatrix G μ n v t (meshInsertBacktrack G u q)
    simp only [meshContraction_insert,mul_ite,mul_zero]
    simp [mul_comm]
  · change (∑ x : {x : V // G.Adj x v}, (Real.sqrt (μ x/μ v) : ℂ)*
      meshExtendMatrix G (meshExtendMatrix G A) v
        (meshInsertBacktrack G x p) ⟨u,⟨w,q⟩⟩)=_
    simp only [meshExtend_twice_no_return G A v p _ u w q hw,mul_zero,Finset.sum_const_zero]
    change 0 = ∑ t : MeshPaths G n v,
      A v p t * meshContractionMatrix G μ n v t ⟨u,⟨w,q⟩⟩
    simp only [meshContraction_no_return G μ n v _ u w q hw,mul_zero,Finset.sum_const_zero]

theorem meshContraction_adjacent_right (μ : V → ℝ) (hμ : ∀ v, 0<μ v)
    (n : ℕ) (v : V) :
    meshExtendMatrix G (meshContractionMatrix G μ n) v *
      (meshContractionMatrix G μ (n+1) v).conjTranspose=1 := by
  have h := congrArg Matrix.conjTranspose (meshContraction_adjacent G μ hμ n v)
  simpa only [Matrix.conjTranspose_mul,meshExtend_adjoint,
    Matrix.conjTranspose_conjTranspose,Matrix.conjTranspose_one] using h

theorem meshContraction_naturality_adjoint (μ : V → ℝ) {m n : ℕ}
    (A : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ) (v : V) :
    meshExtendMatrix G (meshExtendMatrix G A) v *
      (meshContractionMatrix G μ n v).conjTranspose=
        (meshContractionMatrix G μ m v).conjTranspose*A v := by
  have h := congrArg Matrix.conjTranspose
    (meshContraction_naturality G μ (fun v => (A v).conjTranspose) v)
  simpa only [Matrix.conjTranspose_mul,meshExtend_adjoint,
    Matrix.conjTranspose_conjTranspose] using h

end HarmonicArtin.ParabolicIntersections

end OAI
