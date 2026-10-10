import OAI.RepresentationTheory.Saxl.Polytabloid

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV

namespace Saxl

lemma mem_cyclic {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) : v ∈ cyclic ρ v := by
  change v ∈ Submodule.span ℂ _
  apply Submodule.subset_span
  exact ⟨1, by simp⟩

lemma cyclic_le {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (P : Subrepresentation ρ) :
    cyclic ρ v ≤ P ↔ v ∈ P := by
  constructor
  · intro h
    exact h (mem_cyclic ρ v)
  · intro hv
    change Submodule.span ℂ _ ≤ P.toSubmodule
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact P.apply_mem_toSubmodule g hv

/- The actual row-tabloid permutation module, embedded in the word space. -/
def tabloidSub {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :=
  cyclic (wordRep n (μ.colLen 0)) (Pi.single (rowWord t) 1)

lemma columnAlt_mem {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (P : Subrepresentation (wordRep n d)) {x : WordSpace n d} (hx : x ∈ P) :
    columnAlt t x ∈ P := by
  classical
  unfold columnAlt
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ (fun g _ =>
    Submodule.smul_mem _ _ (P.apply_mem_toSubmodule (g : Equiv.Perm (Fin n)) hx))

lemma spechtSub_le_tabloidSub {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    spechtSub t ≤ tabloidSub t := by
  apply (cyclic_le _ _ _).mpr
  rw [← columnAlt_row]
  exact columnAlt_mem t (tabloidSub t) (mem_cyclic _ _)

/- The Ferrers shape forces the column antisymmetrizer to have rank one
on the row-tabloid module. -/
lemma columnAlt_tabloid {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {x : WordSpace n (μ.colLen 0)} (hx : x ∈ tabloidSub t) :
    columnAlt t x ∈ Submodule.span ℂ {polytabloid t} := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    dsimp only
    rw [wordRep_single]
    exact columnAlt_single t g⁻¹
  | zero => simpa only [map_zero] using (Submodule.zero_mem (Submodule.span ℂ {polytabloid t}))
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    simpa only [map_smul] using Submodule.smul_mem _ c ih

@[simp] lemma wordRep_star {n d : ℕ} (g : Equiv.Perm (Fin n)) (x : WordSpace n d) :
    star (wordRep n d g x) = wordRep n d g (star x) := rfl

lemma polytabloid_real {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    star (polytabloid t) = polytabloid t := by
  classical
  unfold polytabloid
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [star_smul, wordRep_star]
  simp only [star_intCast]
  congr 2
  ext a
  simp [Pi.single_apply]

lemma cyclic_star {n d : ℕ} (v : WordSpace n d) (hv : star v = v)
    {x : WordSpace n d} (hx : x ∈ cyclic (wordRep n d) v) :
    star x ∈ cyclic (wordRep n d) v := by
  change star x ∈ (cyclic (wordRep n d) v).toSubmodule
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    dsimp only
    rw [wordRep_star, hv]
    exact (cyclic (wordRep n d) v).apply_mem_toSubmodule g (mem_cyclic _ _)
  | zero => simpa only [star_zero] using (Submodule.zero_mem (cyclic (wordRep n d) v).toSubmodule)
  | add x y hx hy ihx ihy =>
    simpa only [star_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    simpa only [star_smul] using Submodule.smul_mem _ (star c) ih

/- On words, precomposition by a position permutation is a bijection. -/
def wordPerm (n d : ℕ) (g : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n → Fin d) where
  toFun a := a ∘ g
  invFun a := a ∘ (g⁻¹ : Equiv.Perm (Fin n))
  left_inv a := by ext i; simp
  right_inv a := by ext i; simp

lemma wordPair_move {n d : ℕ} (g : Equiv.Perm (Fin n)) (x y : WordSpace n d) :
    dotProduct (wordRep n d g x) y = dotProduct x (wordRep n d g⁻¹ y) := by
  have hh := Equiv.sum_comp (wordPerm n d g)
    (fun a => x a * y (a ∘ (g⁻¹ : Equiv.Perm (Fin n))))
  simpa [dotProduct, wordPerm, wordRep, Function.comp_assoc] using hh

lemma columnAlt_pair {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (x y : WordSpace n d) :
    dotProduct (columnAlt t x) y = dotProduct x (columnAlt t y) := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, sum_dotProduct,
    dotProduct_sum, smul_dotProduct, dotProduct_smul, wordPair_move]
  apply (Equiv.sum_comp (Equiv.inv (columnGroup t)) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  simp only [Equiv.inv_apply, Subgroup.coe_inv, signC_inv, inv_inv]

lemma columnAlt_coefficient {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (x : WordSpace n (μ.colLen 0)) :
    columnAlt t x (rowWord t) = dotProduct x (polytabloid t) := by
  classical
  rw [← dotProduct_single_one (columnAlt t x), columnAlt_pair, columnAlt_row]

lemma polytabloid_ne_zero {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    polytabloid t ≠ 0 := by
  intro h
  have hh := congrFun h (rowWord t)
  rw [polytabloid_rowWord] at hh
  exact one_ne_zero hh

lemma specht_detect {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {x : WordSpace n (μ.colLen 0)} (hx : x ∈ spechtSub t) (hx0 : x ≠ 0) :
    ∃ g : Equiv.Perm (Fin n), dotProduct (wordRep n (μ.colLen 0) g x) (polytabloid t) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hy : ∀ y ∈ (spechtSub t).toSubmodule, dotProduct x y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      have hh := wordPair_move g⁻¹ x (polytabloid t)
      rw [inv_inv] at hh
      exact hh.symm.trans (h g⁻¹)
    | zero => exact dotProduct_zero _
    | add y z hy hz ihy ihz => rw [dotProduct_add, ihy, ihz, add_zero]
    | smul c y hy ih => rw [dotProduct_smul, ih, smul_zero]
  have hs : star x ∈ (spechtSub t).toSubmodule :=
    cyclic_star (polytabloid t) (polytabloid_real t) hx
  let : PartialOrder ℂ := RCLike.toPartialOrder
  let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  exact hx0 (dotProduct_self_star_eq_zero.mp (hy (star x) hs))

/- Every nonzero vector in the genuine complex Specht cyclic subspace
again generates that whole subspace. -/
theorem specht_cyclic_of_ne_zero {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {x : WordSpace n (μ.colLen 0)} (hx : x ∈ spechtSub t) (hx0 : x ≠ 0) :
    cyclic (wordRep n (μ.colLen 0)) x = spechtSub t := by
  classical
  apply le_antisymm ((cyclic_le _ _ _).mpr hx)
  apply (cyclic_le _ _ _).mpr
  obtain ⟨g, hg⟩ := specht_detect t hx hx0
  have he : wordRep n (μ.colLen 0) g x ∈ spechtSub t :=
    (spechtSub t).apply_mem_toSubmodule g hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (columnAlt_tabloid t (spechtSub_le_tabloidSub t he))
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    apply hg
    rw [← columnAlt_coefficient, ← hc]
    rfl
  have hh := columnAlt_mem t (cyclic (wordRep n (μ.colLen 0)) x)
    ((cyclic (wordRep n (μ.colLen 0)) x).apply_mem_toSubmodule g (mem_cyclic _ _))
  rw [← hc] at hh
  exact (Submodule.smul_mem_iff _ hc0).mp hh

/- Inclusion of a subrepresentation of a subrepresentation into the ambient space. -/
def subrepAmbient {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (U : Subrepresentation ρ)
    (S : Subrepresentation U.toRepresentation) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule.map U.toSubmodule.subtype
  apply_mem_toSubmodule g x hx := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨U.toRepresentation g y, S.apply_mem_toSubmodule g hy, rfl⟩

/- The complex polytabloid module is irreducible. -/
theorem specht_irreducible {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Representation.IsIrreducible (spechtRep t) := by
  classical
  have hb : (⊥ : Subrepresentation (spechtRep t)) ≠ ⊤ := by
    intro h
    have hp : (⟨polytabloid t, mem_cyclic _ _⟩ : Specht t) ∈
        (⊥ : Subrepresentation (spechtRep t)).toSubmodule := by
      rw [h]
      trivial
    have he : (⟨polytabloid t, mem_cyclic _ _⟩ : Specht t) = 0 :=
      (Submodule.mem_bot ℂ).mp hp
    exact polytabloid_ne_zero t (congrArg Subtype.val he)
  let : Nontrivial (Subrepresentation (spechtRep t)) := ⟨⟨⊥, ⊤, hb⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hn : S.toSubmodule ≠ ⊥ := by
    intro h
    exact hS (Subrepresentation.toSubmodule_injective h)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff S.toSubmodule).mp hn
  have hv : (x : WordSpace n (μ.colLen 0)) ≠ 0 := by
    intro h
    exact hx0 (Subtype.ext h)
  have hl : cyclic (wordRep n (μ.colLen 0)) x.val ≤ subrepAmbient (spechtSub t) S :=
    (cyclic_le _ _ _).mpr ⟨x, hx, rfl⟩
  rw [specht_cyclic_of_ne_zero t x.property hv] at hl
  apply le_antisymm le_top
  intro y hy
  have hm := hl y.property
  obtain ⟨z, hz, he⟩ := hm
  have he' : z = y := Subtype.ext he
  exact he' ▸ hz

end Saxl

end

end OAI
