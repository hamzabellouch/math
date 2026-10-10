import Mathlib

namespace OAI

namespace PartitionConsistency
namespace SupportFilter
universe u
variable {I : Type u}

/-- Ground pointwise stabilizer of a set of labels. -/
abbrev Fix (J : Set I) : Subgroup (Equiv.Perm I) := fixingSubgroup (Equiv.Perm I) J

@[simp] theorem mem_Fix (J : Set I) (π : Equiv.Perm I) :
    π ∈ Fix J ↔ ∀ j ∈ J, π j = j := mem_fixingSubgroup_iff (Equiv.Perm I)

/-- The actual small-support subgroup filter, rather than a condition asserting
that some symmetric interpretation already has the target properties. -/
def subgroupFilter (μ : Cardinal.{u}) : Set (Subgroup (Equiv.Perm I)) :=
  {K | ∃ J : Set I, Cardinal.mk J ≤ μ ∧ Fix J ≤ K}

theorem top_mem (μ : Cardinal.{u}) : (⊤ : Subgroup (Equiv.Perm I)) ∈ subgroupFilter μ :=
  ⟨∅, by simp, le_top⟩

theorem upward_closed {μ : Cardinal.{u}} {K L : Subgroup (Equiv.Perm I)}
    (hK : K ∈ subgroupFilter μ) (hKL : K ≤ L) : L ∈ subgroupFilter μ := by
  obtain ⟨J, hJ, hf⟩ := hK
  exact ⟨J, hJ, hf.trans hKL⟩

theorem inf_mem {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
    {K L : Subgroup (Equiv.Perm I)} (hK : K ∈ subgroupFilter μ)
    (hL : L ∈ subgroupFilter μ) : K ⊓ L ∈ subgroupFilter μ := by
  obtain ⟨J, hJ, hK⟩ := hK
  obtain ⟨J', hJ', hL⟩ := hL
  refine ⟨J ∪ J', ?_, ?_⟩
  · exact (Cardinal.mk_union_le J J').trans
      ((add_le_add hJ hJ').trans_eq (Cardinal.add_eq_self hμ))
  · simp only [Fix, fixingSubgroup_union]
    exact inf_le_inf hK hL

/-- Conjugating a pointwise stabilizer transports precisely its fixed labels. -/
theorem conjugate_fix (π : Equiv.Perm I) (J : Set I) :
    (Fix J).map (MulAut.conj π).toMonoidHom = Fix (π '' J) := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    have hτ' := (mem_Fix J τ).1 hτ
    apply (mem_Fix _ _).2
    rintro _ ⟨j, hj, rfl⟩
    change π (τ (π⁻¹ (π j))) = π j
    simp [hτ' j hj]
  · intro hσ
    rw [mem_Fix] at hσ
    refine Subgroup.mem_map.2 ⟨π⁻¹ * σ * π, ?_, ?_⟩
    · rw [mem_Fix]
      intro j hj
      change π⁻¹ (σ (π j)) = j
      rw [hσ _ ⟨j, hj, rfl⟩]
      simp
    · change π * (π⁻¹ * σ * π) * π⁻¹ = σ
      group

theorem conjugate_mem {μ : Cardinal.{u}} {K : Subgroup (Equiv.Perm I)}
    (hK : K ∈ subgroupFilter μ) (π : Equiv.Perm I) :
    K.map (MulAut.conj π).toMonoidHom ∈ subgroupFilter μ := by
  obtain ⟨J, hJ, hfix⟩ := hK
  refine ⟨π '' J, Cardinal.mk_image_le.trans hJ, ?_⟩
  rw [← conjugate_fix]
  exact Subgroup.map_mono hfix

/-- Outside a small support, a prescribed label can be moved by a transposition
fixing that support. The fresh second label is chosen in the ground universe. -/
theorem exists_moving_stabilizer [Infinite I] {J : Set I}
    (hJ : Cardinal.mk J < Cardinal.mk I) {j : I} (hj : j ∉ J) :
    ∃ π : Equiv.Perm I, π ∈ Fix J ∧ π j ≠ j := by
  classical
  have hcomp : Cardinal.mk (Jᶜ : Set I) = Cardinal.mk I :=
    Cardinal.mk_compl_of_infinite J hJ
  let : Infinite (Jᶜ : Set I) :=
    Cardinal.infinite_iff.2 (by rw [hcomp]; exact Cardinal.aleph0_le_mk I)
  obtain ⟨k, hk⟩ := exists_ne (⟨j, hj⟩ : (Jᶜ : Set I))
  have hkj : k.val ≠ j := fun h => hk (Subtype.ext h)
  refine ⟨Equiv.swap j k.val, ?_, ?_⟩
  · apply (mem_Fix _ _).2
    intro x hx
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hj (h ▸ hx))
      (fun h => k.property (h ▸ hx))
  · simpa using hkj

/-- With strictly more labels than the support bound the subgroup filter is
proper: the identity subgroup cannot contain the stabilizer of a small set. -/
theorem bot_not_mem {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
    (hsize : μ < Cardinal.mk I) :
    (⊥ : Subgroup (Equiv.Perm I)) ∉ subgroupFilter μ := by
  classical
  let : Infinite I := Cardinal.infinite_iff.2 (hμ.trans hsize.le)
  rintro ⟨J, hJ, hfix⟩
  have hjsize : Cardinal.mk J < Cardinal.mk I := hJ.trans_lt hsize
  have hne : J ≠ Set.univ := by
    intro he
    simp [he] at hjsize
  obtain ⟨j, hj⟩ := (Set.ne_univ_iff_exists_notMem J).1 hne
  obtain ⟨π, hπ, hmove⟩ := exists_moving_stabilizer hjsize hj
  have he : π = 1 := Subgroup.mem_bot.1 (hfix hπ)
  exact hmove (by simp [he])

/-- The normal-filter properties required by the set symmetric-system theorem. -/
def IsNormalFilter {G : Type*} [Group G] (F : Set (Subgroup G)) : Prop :=
  ⊤ ∈ F ∧
  (∀ K L, K ∈ F → K ≤ L → L ∈ F) ∧
  (∀ K L, K ∈ F → L ∈ F → K ⊓ L ∈ F) ∧
  (∀ g K, K ∈ F → K.map (MulAut.conj g).toMonoidHom ∈ F)

theorem isNormalFilter {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) :
    IsNormalFilter (subgroupFilter (I := I) μ) :=
  ⟨top_mem μ, fun _ _ => upward_closed, fun _ _ => inf_mem hμ,
    fun _ _ h => conjugate_mem h _⟩

/-- Small support translates to a small support, since permutations preserve
cardinality. This concerns literal actions, not automorphisms of an extension. -/
theorem transport_support {X : Type*} [MulAction (Equiv.Perm I) X]
    {J : Set I} {x : X} (h : ∀ π ∈ Fix J, π • x = x) (σ : Equiv.Perm I) :
    ∀ π ∈ Fix (σ '' J), π • (σ • x) = σ • x := by
  intro π hπ
  rw [← conjugate_fix] at hπ
  obtain ⟨τ, hτ, rfl⟩ := hπ
  change (σ * τ * σ⁻¹) • (σ • x) = σ • x
  simp [mul_smul, h τ hτ]

end SupportFilter
end PartitionConsistency

end OAI
