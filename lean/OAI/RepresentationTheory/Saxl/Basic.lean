import OAI.RepresentationTheory.Saxl.Model

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV uW

namespace Saxl

/- The genuine finite-dimensional Hom criterion; no simplicity hypothesis. -/
theorem intertwining_finrank_pos_iff {G : Type uG} {V : Type uV} {W : Type uW} [Group G]
    [AddCommGroup V] [AddCommGroup W] [Module ℂ V] [Module ℂ W]
    [Module.Finite ℂ V] [Module.Finite ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    0 < Module.finrank ℂ (Representation.IntertwiningMap ρ σ) ↔
      ∃ f : Representation.IntertwiningMap ρ σ, f ≠ 0 :=
  Module.finrank_pos_iff_exists_ne_zero (R := ℂ) (M := Representation.IntertwiningMap ρ σ)

theorem kronecker_pos_iff {n : ℕ} {α β μ : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ) :
    0 < kronecker a b t ↔
      ∃ f : Representation.IntertwiningMap (spechtRep t)
        ((spechtRep a).tprod (spechtRep b)), f ≠ 0 := by
  exact @intertwining_finrank_pos_iff (Equiv.Perm (Fin n)) (Specht t)
    (Specht a ⊗[ℂ] Specht b) _ _ _ _ _ _ _
    (spechtRep t) ((spechtRep a).tprod (spechtRep b))

/- Column permutations cannot also fix the row word unless they are identity. -/
theorem column_perm_rowWord {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : columnGroup t) (hg : rowWord t ∘ (g : Equiv.Perm (Fin n)) = rowWord t) :
    g = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  apply t.injective
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Fin.val (congrFun hg i)
  · exact g.property i

/- The coefficient of the canonical row word in its polytabloid is one. -/
theorem polytabloid_rowWord {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    polytabloid t (rowWord t) = 1 := by
  classical
  unfold polytabloid
  simp only [Finset.sum_apply, Pi.smul_apply, wordRep, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
  rw [Finset.sum_eq_single (1 : columnGroup t)]
  · simp
  · intro b hb hb1
    have hn : rowWord t ∘ (b : Equiv.Perm (Fin n)) ≠ rowWord t :=
      fun h => hb1 (column_perm_rowWord t b h)
    simp [hn]
  · simp


@[simp] theorem mem_staircase {m i j : ℕ} :
    (i, j) ∈ staircase m ↔ i + j < m := by
  change (i, j) ∈ ((Finset.range m) ×ˢ (Finset.range m)).filter
    (fun x => x.1 + x.2 < m) ↔ _
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

theorem staircase_cells_succ (m : ℕ) :
    (staircase (m + 1)).cells = (staircase m).cells ∪ Finset.HasAntidiagonal.antidiagonal m := by
  ext x
  rcases x with ⟨i, j⟩
  simp only [YoungDiagram.mem_cells, mem_staircase, Finset.mem_union,
    Finset.HasAntidiagonal.mem_antidiagonal]
  omega

theorem staircase_card_succ (m : ℕ) :
    (staircase (m + 1)).card = (staircase m).card + (m + 1) := by
  change (staircase (m + 1)).cells.card = _
  rw [staircase_cells_succ, Finset.card_union_of_disjoint]
  · rw [Finset.Nat.card_antidiagonal]
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases x with ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, mem_staircase] at hx
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hy
    omega

@[simp] theorem staircase_card_zero : (staircase 0).card = 0 := by
  simp [staircase, YoungDiagram.card]

theorem staircase_card_double (m : ℕ) :
    (staircase m).card * 2 = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [staircase_card_succ]
    nlinarith

/- The staircase has triangular cardinality. -/
theorem staircase_card (m : ℕ) : (staircase m).card = m * (m + 1) / 2 := by
  rw [← staircase_card_double]
  simp

end Saxl

end

end OAI
