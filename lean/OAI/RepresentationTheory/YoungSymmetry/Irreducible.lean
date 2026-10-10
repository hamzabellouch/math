import OAI.RepresentationTheory.YoungSymmetry.Polytabloid
import OAI.RepresentationTheory.FiniteUnitary.Characters

namespace OAI

namespace CubeShuffle.Specht
open scoped BigOperators Classical

noncomputable def rowEquiv (μ : YoungDiagram) (i : ℕ) :
    {x : Cell μ // row x = i} ≃ Fin (μ.rowLen i) where
  toFun x := ⟨col x.1, by
    have h := YoungDiagram.mem_iff_lt_rowLen.mp x.1.2
    change col x.1 < μ.rowLen (row x.1) at h
    simpa only [x.2] using h⟩
  invFun j := ⟨⟨(i,j),YoungDiagram.mem_iff_lt_rowLen.mpr j.2⟩,rfl⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.2.symm rfl
  right_inv j := rfl

def rowCost (μ : YoungDiagram) : ℕ := ∑ x : Cell μ, row x

lemma eq_of_row_preserving (μ ν : YoungDiagram) (e : Cell μ ≃ Cell ν)
    (he : ∀ x, row (e x) = row x) : μ = ν := by
  have hlen (i : ℕ) : μ.rowLen i = ν.rowLen i := by
    let ei : {x : Cell μ // row x = i} ≃ {x : Cell ν // row x = i} :=
      { toFun := fun x => ⟨e x.1,(he x.1).trans x.2⟩
        invFun := fun x => ⟨e.symm x.1,by
          have h := he (e.symm x.1)
          simp only [Equiv.apply_symm_apply] at h
          exact h.symm.trans x.2⟩
        left_inv := fun x => by apply Subtype.ext; exact e.symm_apply_apply _
        right_inv := fun x => by apply Subtype.ext; exact e.apply_symm_apply _ }
    simpa only [Fintype.card_fin] using Fintype.card_congr
      ((rowEquiv μ i).symm.trans (ei.trans (rowEquiv ν i)))
  apply YoungDiagram.ext
  ext ⟨i,j⟩
  simp only [YoungDiagram.mem_cells,YoungDiagram.mem_iff_lt_rowLen,hlen]

lemma column_injective_rowCost (μ ν : YoungDiagram) (e : Cell μ ≃ Cell ν)
    (h : ∀ x y : Cell μ, col x = col y → row (e x) = row (e y) → x = y) :
    rowCost μ ≤ rowCost ν ∧ (rowCost μ = rowCost ν → μ = ν) := by
  let c := rankPerm (fun x => row (e x)) h
  have hle (x : Cell μ) : row (c x) ≤ row (e x) := rankCell_row_le _ h x
  have hsumc : ∑ x, row (c x) = rowCost μ := Equiv.sum_comp c _
  have hsume : ∑ x, row (e x) = rowCost ν := Equiv.sum_comp e _
  constructor
  · rw [←hsumc,←hsume]
    exact Finset.sum_le_sum (fun x _ => hle x)
  · intro heq
    have he : ∀ x, row (c x) = row (e x) := by
      apply fun x => (Finset.sum_eq_sum_iff_of_le (fun x _ => hle x)).mp
        (hsumc.trans (heq.trans hsume.symm)) x (Finset.mem_univ _)
    apply eq_of_row_preserving μ ν (c.symm.trans e)
    intro x
    simpa using (he (c.symm x)).symm

lemma swap_relabel {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (x y : α) : e.permCongr (Equiv.swap x y) = Equiv.swap (e x) (e y) := by
  ext z
  simp only [Equiv.permCongr_apply]
  exact e.injective.map_swap x y (e.symm z) |>.trans (by simp)

/-- A nonzero column-sign vector in another tabloid module forces the usual
Young dominance inequality. For inequivalence, the single strictly increasing
row-cost is enough: equality forces equality of shapes. -/
lemma sign_vector_rowCost (μ ν : YoungDiagram) (e : Cell μ ≃ Cell ν)
    (v : Tabloid ν → ℂ) (hv : v ≠ 0)
    (hs : ∀ c : colGroup μ,
      tabloidRep ν (e.permCongr c) v = permSign (c : Equiv.Perm (Cell μ)) • v) :
    rowCost μ ≤ rowCost ν ∧ (rowCost μ = rowCost ν → μ = ν) := by
  obtain ⟨f,hf⟩ : ∃ f, v f ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨p,hp⟩ := f.2
  apply column_injective_rowCost μ ν (e.trans p)
  intro x y hcol hrow
  by_contra hne
  have hfix : tabloidAct (Equiv.swap (e x) (e y)) f = f := by
    apply swap_fixes_tabloid
    rw [hp]
    exact Fin.ext hrow
  have heq := congrArg (fun w : Tabloid ν → ℂ => w f)
    (hs ⟨Equiv.swap x y,swap_mem_colGroup x y hcol⟩)
  rw [swap_relabel,permSign_swap hne] at heq
  simp only [tabloidRep_apply,Equiv.swap_inv,hfix,Pi.smul_apply,neg_one_smul] at heq
  apply hf
  have h2 : (2:ℂ)*(v f) = 0 := by linear_combination heq
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

lemma polytabloid_col_action (μ : YoungDiagram) (c : colGroup μ) :
    tabloidRep μ c (polytabloid μ) = permSign (c:Equiv.Perm (Cell μ)) • polytabloid μ :=
  action_alternator_apply _ _ c _

/-- Specht modules of different shapes cannot be equivalent, including after
an arbitrary relabeling of the underlying finite sets. -/
theorem shapes_eq_of_equivariant_equiv (μ ν : YoungDiagram) (e : Cell μ ≃ Cell ν)
    (T : space μ ≃ₗ[ℂ] space ν)
    (hT : ∀ p v, T (representation μ p v) = representation ν (e.permCongr p) (T v)) :
    μ = ν := by
  let u : space μ := ⟨polytabloid μ,polytabloid_mem_space μ⟩
  have hu : u ≠ 0 := fun h => polytabloid_ne_zero μ (congrArg Subtype.val h)
  have hTcol (c : colGroup μ) :
      tabloidRep ν (e.permCongr c) (T u) = permSign (c:Equiv.Perm (Cell μ)) • (T u : Tabloid ν → ℂ) := by
    change (representation ν (e.permCongr c) (T u) : Tabloid ν → ℂ) = _
    rw [←hT]
    have hh : representation μ c u = permSign (c:Equiv.Perm (Cell μ)) • u :=
      Subtype.ext (polytabloid_col_action μ c)
    rw [hh,map_smul]
    rfl
  have hfwd := sign_vector_rowCost μ ν e (T u)
    (fun h => hu (T.injective (by apply Subtype.ext; simpa using h))) hTcol
  let w : space ν := ⟨polytabloid ν,polytabloid_mem_space ν⟩
  have hw : w ≠ 0 := fun h => polytabloid_ne_zero ν (congrArg Subtype.val h)
  have hTi (p : Equiv.Perm (Cell ν)) (v : space ν) :
      T.symm (representation ν p v) = representation μ (e.symm.permCongr p) (T.symm v) := by
    apply T.injective
    rw [T.apply_symm_apply,hT,T.apply_symm_apply]
    have hp : e.permCongr (e.symm.permCongr p) = p := by
      apply Equiv.ext
      intro x
      simp [Equiv.permCongr_apply]
    rw [hp]
  have hTicol (c : colGroup ν) :
      tabloidRep μ (e.symm.permCongr c) (T.symm w) =
        permSign (c:Equiv.Perm (Cell ν)) • (T.symm w : Tabloid μ → ℂ) := by
    change (representation μ (e.symm.permCongr c) (T.symm w) : Tabloid μ → ℂ) = _
    rw [←hTi]
    have hh : representation ν c w = permSign (c:Equiv.Perm (Cell ν)) • w :=
      Subtype.ext (polytabloid_col_action ν c)
    rw [hh,map_smul]
    rfl
  have hbwd := sign_vector_rowCost ν μ e.symm (T.symm w)
    (fun h => hw (T.symm.injective (by apply Subtype.ext; simpa using h))) hTicol
  exact hfwd.2 (Nat.le_antisymm hfwd.1 hbwd.1)

end CubeShuffle.Specht
namespace CubeShuffle.Specht
open scoped BigOperators Classical

noncomputable def cellRowsEquiv (μ : YoungDiagram) :
    Cell μ ≃ (i : Fin (μ.colLen 0)) × Fin (μ.rowLen i) where
  toFun x := ⟨rowIndex x,⟨col x,YoungDiagram.mem_iff_lt_rowLen.mp x.2⟩⟩
  invFun p := ⟨(p.1,p.2),YoungDiagram.mem_iff_lt_rowLen.mpr p.2.2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv p := by rcases p with ⟨⟨i,hi⟩,⟨j,hj⟩⟩; rfl

lemma card_eq_sum_rowLen (μ : YoungDiagram) : μ.card = ∑ i : Fin (μ.colLen 0), μ.rowLen i := by
  rw [←card_cell,Fintype.card_congr (cellRowsEquiv μ),Fintype.card_sigma]
  simp only [Fintype.card_fin]

lemma sum_rowLens (μ : YoungDiagram) : μ.rowLens.sum = μ.card := by
  rw [card_eq_sum_rowLen,YoungDiagram.rowLens]
  rw [Fin.sum_univ_eq_sum_range]
  have hh (n : ℕ) : (List.map μ.rowLen (List.range n)).sum = ∑ i ∈ Finset.range n, μ.rowLen i := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ,List.map_append,Finset.sum_range_succ,ih]
  exact hh _

noncomputable def diagramPartition (μ : YoungDiagram) : Nat.Partition μ.card where
  parts := μ.rowLens
  parts_pos := fun {i} hi => μ.pos_of_mem_rowLens i (by simpa using hi)
  parts_sum := by simp

noncomputable def partitionDiagram {N : ℕ} (p : Nat.Partition N) : YoungDiagram :=
  YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) (Multiset.pairwise_sort _ _).sortedGE

lemma partitionDiagram_rowLens {N : ℕ} (p : Nat.Partition N) :
    (partitionDiagram p).rowLens = p.parts.sort (· ≥ ·) := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro x hx
  exact p.parts_pos ((Multiset.mem_sort _).mp hx)

lemma partitionDiagram_card {N : ℕ} (p : Nat.Partition N) : (partitionDiagram p).card = N := by
  rw [←sum_rowLens,partitionDiagram_rowLens]
  change (↑(p.parts.sort (· ≥ ·)) : Multiset ℕ).sum = N
  rw [Multiset.sort_eq,p.parts_sum]

lemma partitionDiagram_diagramPartition (μ : YoungDiagram) :
    partitionDiagram (diagramPartition μ) = μ := by
  apply YoungDiagram.equivListRowLens.injective
  apply Subtype.ext
  change (partitionDiagram (diagramPartition μ)).rowLens = μ.rowLens
  rw [partitionDiagram_rowLens]
  change (↑μ.rowLens : Multiset ℕ).sort (· ≥ ·) = μ.rowLens
  rw [Multiset.coe_sort,List.mergeSort_eq_self _ μ.rowLens_sorted.pairwise]

abbrev Shapes (N : ℕ) := {μ : YoungDiagram // μ.card = N}

noncomputable def shapePartitionEquiv (N : ℕ) : Shapes N ≃ Nat.Partition N where
  toFun μ := { parts := μ.1.rowLens
               parts_pos := fun {i} hi => μ.1.pos_of_mem_rowLens i (by simpa using hi)
               parts_sum := by simpa using (sum_rowLens μ.1).trans μ.2 }
  invFun p := ⟨partitionDiagram p,partitionDiagram_card p⟩
  left_inv μ := by
    apply Subtype.ext
    obtain ⟨μ,rfl⟩ := μ
    exact partitionDiagram_diagramPartition μ
  right_inv p := by
    apply Nat.Partition.ext
    change ((partitionDiagram p).rowLens : Multiset ℕ) = p.parts
    rw [partitionDiagram_rowLens,Multiset.sort_eq]

noncomputable instance (N : ℕ) : Fintype (Shapes N) := Fintype.ofEquiv _ (shapePartitionEquiv N).symm

noncomputable def conjugacyPartition {α : Type*} [Fintype α] [DecidableEq α] :
    ConjClasses (Equiv.Perm α) → Nat.Partition (Fintype.card α) :=
  Quotient.lift Equiv.Perm.partition (fun _ _ hpq => (Equiv.Perm.partition_eq_of_isConj).mp hpq)

lemma conjugacyPartition_injective {α : Type*} [Fintype α] [DecidableEq α] :
    Function.Injective (conjugacyPartition (α := α)) := by
  intro p q
  induction p using Quotient.inductionOn with | _ p =>
    induction q using Quotient.inductionOn with | _ q =>
      intro h
      exact Quotient.sound ((Equiv.Perm.partition_eq_of_isConj).mpr h)

lemma card_conjugacy_le_shapes (N : ℕ) :
    Nat.card (ConjClasses (Equiv.Perm (Fin N))) ≤ Fintype.card (Shapes N) := by
  have h := Nat.card_le_card_of_injective _ (conjugacyPartition_injective (α := Fin N))
  simpa only [Fintype.card_fin, Nat.card_eq_fintype_card, Fintype.card_congr (shapePartitionEquiv N)] using h

noncomputable def labels {N : ℕ} (μ : Shapes N) : Cell μ.1 ≃ Fin N :=
  (Fintype.equivFin (Cell μ.1)).trans (finCongr ((card_cell μ.1).trans μ.2))

noncomputable def labelledRepresentation {N : ℕ} (μ : Shapes N) :
    Representation ℂ (Equiv.Perm (Fin N)) (space μ.1) :=
  (representation μ.1).comp (labels μ).symm.permCongrHom.toMonoidHom

lemma labelledRepresentation_irreducible {N : ℕ} (μ : Shapes N) :
    Representation.IsIrreducible (labelledRepresentation μ) := by
  let e := (labels μ).symm.permCongrHom
  let ρ := representation μ.1
  have hn : (⊥ : Subrepresentation (labelledRepresentation μ)) ≠ ⊤ := by
    intro h
    have he : (⟨polytabloid μ.1,polytabloid_mem_space μ.1⟩ : space μ.1) ∈
        (⊥ : Subrepresentation (labelledRepresentation μ)) := by rw [h]; trivial
    exact polytabloid_ne_zero μ.1 (congrArg Subtype.val he)
  refine { exists_pair_ne := ⟨⊥,⊤,hn⟩,eq_bot_or_eq_top := ?_ }
  intro U
  let U' : Subrepresentation ρ :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := fun p v hv => by
        have hh := U.apply_mem_toSubmodule (e.symm p) hv
        change ρ (e (e.symm p)) v ∈ U.toSubmodule at hh
        simpa using hh }
  have := representation_irreducible μ.1
  obtain h | h := IsSimpleOrder.eq_bot_or_eq_top U'
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun R : Subrepresentation ρ => R.toSubmodule) h
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun R : Subrepresentation ρ => R.toSubmodule) h

lemma labelledRepresentation_equiv_shapes {N : ℕ} (μ ν : Shapes N)
    (T : Representation.Equiv (labelledRepresentation μ) (labelledRepresentation ν)) : μ = ν := by
  apply Subtype.ext
  apply shapes_eq_of_equivariant_equiv μ.1 ν.1 ((labels μ).trans (labels ν).symm) T.toLinearEquiv
  intro p v
  have hh := Representation.IntertwiningMap.isIntertwining _ _ T.toIntertwiningMap ((labels μ).permCongr p) v
  change T.toLinearEquiv
    (representation μ.1 ((labels μ).symm.permCongr ((labels μ).permCongr p)) v) =
      representation ν.1 ((labels ν).symm.permCongr ((labels μ).permCongr p)) (T.toLinearEquiv v) at hh
  have hp : (labels μ).symm.permCongr ((labels μ).permCongr p) = p := by
    apply Equiv.ext
    intro x
    simp [Equiv.permCongr_apply]
  rw [hp] at hh
  convert hh using 2
  congr 1

end CubeShuffle.Specht

namespace CubeShuffle.Specht
open scoped Classical

/-- Actual completeness of the polytabloid representations of the full symmetric group. -/
theorem labelled_complete {N : ℕ}
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) V) [Representation.IsIrreducible ρ] :
    ∃ μ : Shapes N, Nonempty (Representation.Equiv (labelledRepresentation μ) ρ) := by
  let (μ : Shapes N) : Representation.IsIrreducible (labelledRepresentation μ) :=
    labelledRepresentation_irreducible μ
  apply FiniteCharacters.complete_of_card_conjugacy_le
    (fun μ : Shapes N => space μ.1) labelledRepresentation _ (card_conjugacy_le_shapes N) ρ
  intro μ ν h ⟨T⟩
  exact h (labelledRepresentation_equiv_shapes μ ν T)

end CubeShuffle.Specht

end OAI
