import OAI.RepresentationTheory.Saxl.ShapeRigidity

namespace OAI

noncomputable section

open scoped TensorProduct

universe uV uG

namespace Saxl

/- Rows enumerate exactly the actual cells, including the empty diagram. -/
def rowCellEquiv (μ : YoungDiagram) : μ.cells ≃ (i : Fin (μ.colLen 0)) × Fin (μ.rowLen i) where
  toFun c := ⟨⟨c.val.1, YoungDiagram.mem_iff_lt_colLen.mp
      (μ.up_left_mem le_rfl (Nat.zero_le _) c.property)⟩,
    ⟨c.val.2, YoungDiagram.mem_iff_lt_rowLen.mp c.property⟩⟩
  invFun c := ⟨(c.1.val, c.2.val), YoungDiagram.mem_iff_lt_rowLen.mpr c.2.isLt⟩
  left_inv c := Subtype.ext rfl
  right_inv c := by rcases c with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩; rfl

lemma card_eq_sum_rowLens (μ : YoungDiagram) : μ.card = μ.rowLens.sum := by
  classical
  have h := Fintype.card_congr (rowCellEquiv μ)
  simp only [Fintype.card_coe, Fintype.card_sigma, Fintype.card_fin] at h
  change μ.card = ∑ x : Fin (μ.colLen 0), μ.rowLen x at h
  rw [h, YoungDiagram.rowLens]
  rw [← List.sum_toFinset _ List.nodup_range]
  have he : (List.range (μ.colLen 0)).toFinset = Finset.range (μ.colLen 0) := by
    ext i; simp
  rw [he]
  exact Fin.sum_univ_eq_sum_range μ.rowLen (μ.colLen 0)

/- Conversion from Mathlib's partition type to its Young diagram. -/
def partitionDiagram {n : ℕ} (p : Nat.Partition n) : YoungDiagram :=
  YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) (Multiset.pairwise_sort _ _).sortedGE

lemma partitionDiagram_rowLens {n : ℕ} (p : Nat.Partition n) :
    (partitionDiagram p).rowLens = p.parts.sort (· ≥ ·) := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro a ha
  exact p.parts_pos (by simpa only [← Multiset.mem_coe, Multiset.sort_eq] using ha)

lemma partitionDiagram_card {n : ℕ} (p : Nat.Partition n) : (partitionDiagram p).card = n := by
  rw [card_eq_sum_rowLens, partitionDiagram_rowLens, ← Multiset.sum_coe,
    Multiset.sort_eq, p.parts_sum]

lemma partitionDiagram_injective {n : ℕ} :
    Function.Injective (partitionDiagram (n := n)) := by
  intro p q h
  apply Nat.Partition.ext
  have he := congrArg (fun μ => (μ.rowLens : Multiset ℕ)) h
  simpa only [partitionDiagram_rowLens, Multiset.sort_eq] using he

def partitionTableau {n : ℕ} (p : Nat.Partition n) : Tableau n (partitionDiagram p) :=
  canonicalTableau _ (partitionDiagram_card p)

/- Cycle-type partition, with only the definitional `card (Fin n)=n` transport. -/
def permPartition {n : ℕ} (g : Equiv.Perm (Fin n)) : Nat.Partition n :=
  ⟨g.partition.parts, g.partition.parts_pos, g.partition.parts_sum.trans (Fintype.card_fin n)⟩

lemma isConj_of_permPartition_eq {n : ℕ} {g h : Equiv.Perm (Fin n)}
    (hh : permPartition g = permPartition h) : IsConj g h := by
  apply Equiv.Perm.partition_eq_of_isConj.mpr
  have hp := congrArg (fun p : Nat.Partition n => p.parts) hh
  exact Nat.Partition.ext hp

/- Class functions on the symmetric group, indexed by cycle type. -/
def classFunctions (n : ℕ) : Submodule ℂ (Equiv.Perm (Fin n) → ℂ) where
  carrier := {f | ∀ g h, permPartition g = permPartition h → f g = f h}
  zero_mem' := by
    change ∀ g h, permPartition g = permPartition h → (0 : Equiv.Perm (Fin n) → ℂ) g = 0
    intro g h hh; rfl
  add_mem' := by intro f h hf hh g k hk; simp only [Pi.add_apply, hf g k hk, hh g k hk]
  smul_mem' := by intro c f hf g k hk; simp only [Pi.smul_apply, hf g k hk]

/- Select one representative where a cycle partition is realized; unused
coordinates are zero. This gives an injection even without surjectivity of
cycle-type realization. -/
def classEvaluation (n : ℕ) : (classFunctions n) →ₗ[ℂ] (Nat.Partition n → ℂ) where
  toFun f p := if h : ∃ g : Equiv.Perm (Fin n), permPartition g = p then f.val h.choose else 0
  map_add' f h := by
    ext p
    simp only [Pi.add_apply, Submodule.coe_add]
    split_ifs <;> simp
  map_smul' c f := by
    ext p
    simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply]
    split_ifs <;> simp

lemma classEvaluation_injective (n : ℕ) : Function.Injective (classEvaluation n) := by
  intro f h he
  apply Subtype.ext
  funext g
  have hh := congrFun he (permPartition g)
  have hex : ∃ k : Equiv.Perm (Fin n), permPartition k = permPartition g := ⟨g, rfl⟩
  change (if hc : ∃ k : Equiv.Perm (Fin n), permPartition k = permPartition g then
    f.val hc.choose else 0) = (if hc : ∃ k : Equiv.Perm (Fin n), permPartition k = permPartition g then
    h.val hc.choose else 0) at hh
  rw [dite_eq_left hex, dite_eq_left hex] at hh
  exact (f.property _ _ hex.choose_spec).symm.trans (hh.trans (h.property _ _ hex.choose_spec))

lemma classFunctions_finrank_le (n : ℕ) :
    Module.finrank ℂ (classFunctions n) ≤ Fintype.card (Nat.Partition n) := by
  have h := LinearMap.finrank_le_finrank_of_injective (classEvaluation_injective n)
  simpa using h

lemma char_mem_classFunctions {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    ρ.character ∈ classFunctions n := by
  intro g h he
  obtain ⟨k, rfl⟩ := isConj_iff.mp (isConj_of_permPartition_eq he)
  exact (Representation.char_conj ρ g k).symm

/- Character of the actual Specht module as an actual class function. -/
def spechtCharacter {n : ℕ} (p : Nat.Partition n) : classFunctions n :=
  ⟨(spechtRep (partitionTableau p)).character, char_mem_classFunctions _⟩

/- Bilinear character scalar product used by the finite-group orthogonality theorem. -/
def charFunctional {G : Type uG} [Group G] [Fintype G] (y : G → ℂ) : (G → ℂ) →ₗ[ℂ] ℂ where
  toFun x := (Nat.card G : ℂ)⁻¹ * ∑ g, x g * y g⁻¹
  map_add' x z := by simp [Finset.sum_add_distrib, add_mul, mul_add]
  map_smul' c x := by simp [Finset.mul_sum, mul_assoc, mul_left_comm]

lemma complex_card_ne_zero (G : Type uG) [Group G] [Fintype G] : (Nat.card G : ℂ) ≠ 0 := by
  exact_mod_cast Nat.card_pos.ne'

lemma spechtCharacter_orthonormal {n : ℕ} (p q : Nat.Partition n) :
    charFunctional (spechtCharacter q).val (spechtCharacter p).val = if p = q then 1 else 0 := by
  classical
  let : Invertible (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (complex_card_ne_zero _)
  let := specht_irreducible (partitionTableau p)
  let := specht_irreducible (partitionTableau q)
  have h := Representation.char_orthonormal (spechtRep (partitionTableau p))
    (spechtRep (partitionTableau q))
  change _ = _ at h
  have he : Nonempty ((spechtRep (partitionTableau q)).Equiv
      (spechtRep (partitionTableau p))) ↔ p = q := by
    constructor
    · rintro ⟨e⟩
      exact (partitionDiagram_injective
        (specht_shape_rigidity (partitionTableau q) (partitionTableau p) e)).symm
    · rintro rfl
      exact ⟨Representation.Equiv.refl _⟩
  simpa only [he, charFunctional, spechtCharacter, LinearMap.coe_mk, AddHom.coe_mk] using h

lemma spechtCharacter_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (spechtCharacter (n := n)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have h := congrArg (fun f : classFunctions n => charFunctional (spechtCharacter p).val f.val) hc
  change charFunctional (spechtCharacter p).val
    ((classFunctions n).subtype (∑ i, c i • spechtCharacter i)) =
    charFunctional (spechtCharacter p).val ((classFunctions n).subtype 0) at h
  simp only [map_sum, map_smul, map_zero] at h
  change (∑ i, c i * charFunctional (spechtCharacter p).val (spechtCharacter i).val) = 0 at h
  simp_rw [spechtCharacter_orthonormal] at h
  simpa using h

lemma spechtCharacter_span (n : ℕ) :
    Submodule.span ℂ (Set.range (spechtCharacter (n := n))) = ⊤ := by
  apply (spechtCharacter_linearIndependent n).span_eq_top_of_card_eq_finrank'
  exact le_antisymm (spechtCharacter_linearIndependent n).fintype_card_le_finrank
    (classFunctions_finrank_le n)



theorem irreducible_equiv_specht {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V)
    [Representation.IsIrreducible ρ] :
    ∃ p : Nat.Partition n, Nonempty (ρ.Equiv (spechtRep (partitionTableau p))) := by
  classical
  let : Invertible (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (complex_card_ne_zero _)
  by_contra h
  push Not at h
  let f : (classFunctions n) →ₗ[ℂ] ℂ :=
    (charFunctional ρ.character).comp (classFunctions n).subtype
  have hf : ∀ p : Nat.Partition n, f (spechtCharacter p) = 0 := by
    intro p
    let := specht_irreducible (partitionTableau p)
    have hp := Representation.char_orthonormal (spechtRep (partitionTableau p)) ρ
    rw [ite_eq_right (fun he => (h p).false he.some)] at hp
    exact hp
  have hk : Submodule.span ℂ (Set.range (spechtCharacter (n := n))) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact hf p
  rw [spechtCharacter_span] at hk
  have hz := hk (show (⟨ρ.character, char_mem_classFunctions ρ⟩ : classFunctions n) ∈ ⊤ from trivial)
  change charFunctional ρ.character ρ.character = 0 at hz
  have hone := Representation.char_orthonormal ρ ρ
  rw [ite_eq_left ⟨Representation.Equiv.refl ρ⟩] at hone
  exact one_ne_zero (hone.symm.trans hz)



lemma columnAlt_eq_zero_of_rows {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (hd : d < μ.colLen 0) : columnAlt (d := d) t = 0 := by
  classical
  have hz : ∀ a : Fin n → Fin d, columnAlt t (Pi.single a (1 : ℂ)) = 0 := by
    intro a
    let j : Fin (μ.colLen 0) → Fin n := fun i => t.symm
      ⟨(i.val, 0), YoungDiagram.mem_iff_lt_colLen.mpr i.isLt⟩
    have hnot : ¬ Function.Injective (a ∘ j) := by
      intro hi
      have hh := Fintype.card_le_of_injective _ hi
      simp only [Fintype.card_fin] at hh
      omega
    simp only [Function.Injective] at hnot
    push Not at hnot
    obtain ⟨i, k, ha, hik⟩ := hnot
    have hj : j i ≠ j k := by
      intro he
      apply hik
      apply Fin.ext
      have hh := congrArg (fun l => (t l).val.1) he
      simpa [j] using hh
    exact columnAlt_collision t a (j i) (j k) hj (by simp [j]) ha
  apply LinearMap.ext
  intro x
  have he : x = ∑ a, x a • Pi.single a (1 : ℂ) := by
    ext b
    simp [Pi.single_apply]
  rw [he, map_sum]
  simp only [map_smul, hz, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]

/- A Specht constituent of a `d`-letter position representation has at most
`d` rows, proved by the genuine first-column antisymmetrizer. -/
theorem specht_rows_of_hom {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (f : Representation.IntertwiningMap (spechtRep t) (wordRep n d)) (hf : f ≠ 0) :
    μ.colLen 0 ≤ d := by
  classical
  let := specht_irreducible t
  have hi := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  by_contra h
  have hd : d < μ.colLen 0 := lt_of_not_ge h
  let p : Specht t := ⟨polytabloid t, mem_cyclic _ _⟩
  have he := columnOperator_intertwining t f p
  change f (columnOperator t (spechtRep t) p) = columnAlt t (f p) at he
  rw [columnAlt_eq_zero_of_rows t hd, LinearMap.zero_apply] at he
  have hz : columnOperator t (spechtRep t) p = 0 := hi (he.trans (map_zero f).symm)
  exact columnAlt_polytabloid_ne_zero t
    ((columnOperator_subtype t (spechtSub t) p).symm.trans (congrArg Subtype.val hz))

end Saxl

end

end OAI
