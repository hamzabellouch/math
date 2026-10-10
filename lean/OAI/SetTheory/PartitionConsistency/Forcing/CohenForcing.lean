import Mathlib

namespace OAI

namespace PartitionConsistency
namespace CohenForcing
universe u v
variable {I : Type u} {κ : Type v}

/-- Countable partial functions `I × κ → 2`, represented by their graphs.
Countability of the graph is equivalent to countability of the domain for
these single-valued graphs. Conditions are ordered by reverse inclusion. -/
structure Condition (I : Type u) (κ : Type v) where
  graph : Set ((I × κ) × Bool)
  functional : ∀ (a : I × κ) (b c : Bool), (a, b) ∈ graph → (a, c) ∈ graph → b = c
  countable_graph : graph.Countable

namespace Condition

@[ext] theorem ext {p q : Condition I κ} (h : p.graph = q.graph) : p = q := by
  cases p; cases q; cases h; rfl

instance : PartialOrder (Condition I κ) where
  le p q := q.graph ⊆ p.graph
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ hpq hqr := hqr.trans hpq
  le_antisymm _ _ hpq hqp := ext (Set.Subset.antisymm hqp hpq)

@[simp] theorem le_iff (p q : Condition I κ) : p ≤ q ↔ q.graph ⊆ p.graph := Iff.rfl

instance : OrderTop (Condition I κ) where
  top := ⟨∅, by simp, Set.countable_empty⟩
  le_top _ := Set.empty_subset _

@[simp] theorem graph_top : (⊤ : Condition I κ).graph = ∅ := rfl

def dom (p : Condition I κ) : Set (I × κ) := Prod.fst '' p.graph
def support (p : Condition I κ) : Set I := Prod.fst '' p.dom

theorem countable_dom (p : Condition I κ) : p.dom.Countable :=
  p.countable_graph.image _

theorem countable_support (p : Condition I κ) : p.support.Countable :=
  p.countable_dom.image _

@[simp] theorem mem_dom (p : Condition I κ) (a : I × κ) :
    a ∈ p.dom ↔ ∃ b : Bool, (a, b) ∈ p.graph := by
  constructor
  · rintro ⟨⟨a', b⟩, h, rfl⟩
    exact ⟨b, h⟩
  · rintro ⟨b, hb⟩
    exact ⟨(a, b), hb, rfl⟩

@[simp] theorem mem_support (p : Condition I κ) (j : I) :
    j ∈ p.support ↔ ∃ a : κ, ∃ b : Bool, ((j, a), b) ∈ p.graph := by
  constructor
  · rintro ⟨⟨j', a⟩, h, rfl⟩
    exact ⟨a, (mem_dom p _).1 h⟩
  · rintro ⟨a, b, hb⟩
    exact ⟨(j, a), (mem_dom p _).2 ⟨b, hb⟩, rfl⟩

/-- The graph description is equivalent to the source's countable-domain
condition for partial functions, and does not impose an extra smallness bound. -/
theorem countable_graph_iff_dom {g : Set ((I × κ) × Bool)}
    (hg : ∀ a b c, (a, b) ∈ g → (a, c) ∈ g → b = c) :
    g.Countable ↔ (Prod.fst '' g).Countable := by
  refine ⟨fun h => h.image _, fun h => ?_⟩
  apply Set.countable_of_injective_of_countable_image (f := Prod.fst) ?_ h
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd he
  dsimp only at he
  subst c
  exact congrArg (fun z => (a, z)) (hg a b d hab hcd)

/-- Compatibility is exactly agreement wherever both assignments are defined. -/
def Compatible (p q : Condition I κ) : Prop :=
  ∀ a b c, (a, b) ∈ p.graph → (a, c) ∈ q.graph → b = c

theorem Compatible.symm {p q : Condition I κ} (h : Compatible p q) : Compatible q p :=
  fun a b c hb hc => (h a c b hc hb).symm

def union (p q : Condition I κ) (h : Compatible p q) : Condition I κ where
  graph := p.graph ∪ q.graph
  functional := by
    intro a b c hb hc
    rcases hb with hb | hb <;> rcases hc with hc | hc
    · exact p.functional a b c hb hc
    · exact h a b c hb hc
    · exact (h a c b hc hb).symm
    · exact q.functional a b c hb hc
  countable_graph := p.countable_graph.union q.countable_graph

@[simp] theorem union_graph (p q : Condition I κ) (h : Compatible p q) :
    (union p q h).graph = p.graph ∪ q.graph := rfl

theorem union_le_left (p q : Condition I κ) (h : Compatible p q) : union p q h ≤ p :=
  Set.subset_union_left

theorem union_le_right (p q : Condition I κ) (h : Compatible p q) : union p q h ≤ q :=
  Set.subset_union_right

theorem compatible_iff {p q : Condition I κ} :
    Compatible p q ↔ ∃ r : Condition I κ, r ≤ p ∧ r ≤ q := by
  constructor
  · intro h
    exact ⟨union p q h, union_le_left p q h, union_le_right p q h⟩
  · rintro ⟨r, hp, hq⟩ a b c hb hc
    exact r.functional a b c (hp hb) (hq hc)

/-- The Cohen forcing described in the source is countably closed. Unions
suffice; no closure of the diagram forcing or product is asserted. -/
theorem countably_closed (p : ℕ → Condition I κ) (hp : Antitone p) :
    ∃ r : Condition I κ, ∀ n, r ≤ p n := by
  let g := ⋃ n, (p n).graph
  have fun_g : ∀ a b c, (a, b) ∈ g → (a, c) ∈ g → b = c := by
    intro a b c hb hc
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hb
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hc
    exact (p (max n m)).functional a b c
      (hp (Nat.le_max_left _ _) hn) (hp (Nat.le_max_right _ _) hm)
  exact ⟨⟨g, fun_g, Set.countable_iUnion (fun n => (p n).countable_graph)⟩,
    fun n z hz => Set.mem_iUnion.2 ⟨n, hz⟩⟩

/-- Restriction to a set of label coordinates. -/
def restrict (p : Condition I κ) (J : Set I) : Condition I κ where
  graph := {z | z ∈ p.graph ∧ z.1.1 ∈ J}
  functional a b c hb hc := p.functional a b c hb.1 hc.1
  countable_graph := p.countable_graph.mono (fun _ h => h.1)

@[simp] theorem mem_restrict (p : Condition I κ) (J : Set I) (z : (I × κ) × Bool) :
    z ∈ (restrict p J).graph ↔ z ∈ p.graph ∧ z.1.1 ∈ J := Iff.rfl

theorem le_restrict (p : Condition I κ) (J : Set I) : p ≤ restrict p J :=
  fun _ h => h.1

theorem support_restrict_subset (p : Condition I κ) (J : Set I) :
    (restrict p J).support ⊆ J := by
  intro j hj
  obtain ⟨a, b, hab⟩ := (mem_support _ _).1 hj
  exact hab.2

theorem restrict_eq_of_support_subset (p : Condition I κ) {J : Set I}
    (h : p.support ⊆ J) : restrict p J = p := by
  apply ext
  ext z
  simp only [mem_restrict, and_iff_left_iff_imp]
  intro hz
  exact h ((mem_support p _).2 ⟨z.1.2, z.2, hz⟩)

/-- Define the coordinate action on the full graph, including both the ordinal
input and its Boolean output. -/
def coordinatePerm (π : Equiv.Perm I) : Equiv.Perm ((I × κ) × Bool) :=
  (π.prodCongr (Equiv.refl κ)).prodCongr (Equiv.refl Bool)

@[simp] theorem coordinatePerm_apply (π : Equiv.Perm I) (z : (I × κ) × Bool) :
    coordinatePerm π z = ((π z.1.1, z.1.2), z.2) := rfl
@[simp] theorem coordinatePerm_symm_apply (π : Equiv.Perm I) (z : (I × κ) × Bool) :
    (coordinatePerm π).symm z = ((π.symm z.1.1, z.1.2), z.2) := rfl

def permute (π : Equiv.Perm I) (p : Condition I κ) : Condition I κ where
  graph := coordinatePerm π '' p.graph
  functional a b c hb hc :=
    p.functional (π.symm a.1, a.2) b c
      (Set.mem_image_equiv.1 hb) (Set.mem_image_equiv.1 hc)
  countable_graph := p.countable_graph.image _

@[simp] theorem mem_permute (π : Equiv.Perm I) (p : Condition I κ) (z : (I × κ) × Bool) :
    z ∈ (permute π p).graph ↔ ((π.symm z.1.1, z.1.2), z.2) ∈ p.graph :=
  Set.mem_image_equiv

@[simp] theorem permute_one (p : Condition I κ) : permute 1 p = p := by
  ext z
  simp [Equiv.Perm.one_def]

@[simp] theorem permute_mul (π σ : Equiv.Perm I) (p : Condition I κ) :
    permute (π * σ) p = permute π (permute σ p) := by
  apply ext
  ext z
  simp [Equiv.Perm.mul_def]

@[simp] theorem permute_inv_permute (π : Equiv.Perm I) (p : Condition I κ) :
    permute π⁻¹ (permute π p) = p := by
  apply ext
  ext z
  simp [Equiv.Perm.inv_def]

@[simp] theorem permute_permute_inv (π : Equiv.Perm I) (p : Condition I κ) :
    permute π (permute π⁻¹ p) = p := by
  apply ext
  ext z
  simp [Equiv.Perm.inv_def]

/-- The same label permutations used for diagrams are order automorphisms of
Cohen forcing. They can therefore act diagonally on the product. -/
def permuteOrderIso (π : Equiv.Perm I) : Condition I κ ≃o Condition I κ where
  toFun := permute π
  invFun := permute π⁻¹
  left_inv := permute_inv_permute π
  right_inv := permute_permute_inv π
  map_rel_iff' := by
    intro p q
    change coordinatePerm π '' q.graph ⊆ coordinatePerm π '' p.graph ↔ q.graph ⊆ p.graph
    exact Set.image_subset_image_iff (coordinatePerm π).injective

theorem permute_eq_of_fixes_support (π : Equiv.Perm I) (p : Condition I κ)
    (hπ : ∀ j ∈ p.support, π j = j) : permute π p = p := by
  apply ext
  apply Set.Subset.antisymm
  · rintro z ⟨w, hw, rfl⟩
    have hfix := hπ w.1.1 ((mem_support p _).2 ⟨w.1.2, w.2, hw⟩)
    simpa [hfix] using hw
  · intro z hz
    refine ⟨z, hz, ?_⟩
    have hfix := hπ z.1.1 ((mem_support p _).2 ⟨z.1.2, z.2, hz⟩)
    simp [hfix]

/-- Two conditions agreeing on their common root and having disjoint nonroot
supports are compatible. This is the Cohen half of the locality argument. -/
theorem compatible_of_disjoint_off_root (p q : Condition I κ) (J : Set I)
    (hroot : Compatible (restrict p J) (restrict q J))
    (hdisj : Disjoint (p.support \ J) (q.support \ J)) : Compatible p q := by
  intro a b c hb hc
  by_cases ha : a.1 ∈ J
  · exact hroot a b c ⟨hb, ha⟩ ⟨hc, ha⟩
  · exact False.elim (Set.disjoint_left.1 hdisj
      ⟨(mem_support p _).2 ⟨a.2, b, hb⟩, ha⟩
      ⟨(mem_support q _).2 ⟨a.2, c, hc⟩, ha⟩)

/-- Introduce one unassigned coordinate with a specified Boolean value. -/
def insert (p : Condition I κ) (a : I × κ) (b : Bool) (h : a ∉ p.dom) : Condition I κ where
  graph := Set.insert (a, b) p.graph
  functional := by
    intro x c d hc hd
    rcases hc with hc | hc <;> rcases hd with hd | hd
    · exact (congrArg Prod.snd hc).trans (congrArg Prod.snd hd).symm
    · cases hc
      exact False.elim (h ((mem_dom p _).2 ⟨d, hd⟩))
    · cases hd
      exact False.elim (h ((mem_dom p _).2 ⟨c, hc⟩))
    · exact p.functional x c d hc hd
  countable_graph := p.countable_graph.insert _

theorem insert_le (p : Condition I κ) (a : I × κ) (b : Bool) (h : a ∉ p.dom) :
    insert p a b h ≤ p := Set.subset_insert _ _

theorem fresh_level [Uncountable κ] (p : Condition I κ) :
    ∃ a : κ, ∀ j : I, (j, a) ∉ p.dom := by
  have hc : (Prod.snd '' p.dom).Countable := p.countable_dom.image _
  have hn : Prod.snd '' p.dom ≠ Set.univ := by
    intro hu
    exact Set.not_countable_univ (hu ▸ hc)
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem _).1 hn
  exact ⟨a, fun j hj => ha ⟨(j, a), hj, rfl⟩⟩

/-- Distinct label coordinates can be assigned opposite bits at a fresh level
below every condition. This is the dense separation used for distinct labels. -/
theorem separate_labels [Uncountable κ] (p : Condition I κ) {j k : I} (hjk : j ≠ k) :
    ∃ (q : Condition I κ) (a : κ), q ≤ p ∧
      ((j, a), false) ∈ q.graph ∧ ((k, a), true) ∈ q.graph := by
  obtain ⟨a, ha⟩ := fresh_level p
  let p' := insert p (j, a) false (ha j)
  have hk : (k, a) ∉ p'.dom := by
    rintro h
    obtain ⟨b, hb⟩ := (mem_dom p' _).1 h
    rcases hb with hb | hb
    · exact hjk (congrArg (fun z : (I × κ) × Bool => z.1.1) hb).symm
    · exact ha k ((mem_dom p _).2 ⟨b, hb⟩)
  let q := insert p' (k, a) true hk
  refine ⟨q, a, (insert_le _ _ _ _).trans (insert_le _ _ _ _), ?_, ?_⟩
  · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · exact Set.mem_insert _ _

end Condition
end CohenForcing
end PartitionConsistency

end OAI
