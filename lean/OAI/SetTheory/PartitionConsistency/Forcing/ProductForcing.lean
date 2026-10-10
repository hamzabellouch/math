import Mathlib
import OAI.SetTheory.PartitionConsistency.Forcing.Diagrams
import OAI.SetTheory.PartitionConsistency.Forcing.CohenForcing
import OAI.SetTheory.PartitionConsistency.Forcing.SupportFilter
import OAI.SetTheory.PartitionConsistency.Algebra.Placements

namespace OAI

namespace PartitionConsistency
namespace SmallPlacements
universe u
variable {I : Type u}

theorem union_bound {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
    {s t : Set I} (hs : Cardinal.mk s ≤ μ) (ht : Cardinal.mk t ≤ μ) :
    Cardinal.mk (s ∪ t : Set I) ≤ μ :=
  (Cardinal.mk_union_le s t).trans ((add_le_add hs ht).trans_eq (Cardinal.add_eq_self hμ))

/-- An independent placement has exactly the stated common root. -/
theorem intersection_eq_root {s t r : Set I} (hrs : r ⊆ s) (hrt : r ⊆ t)
    (π : Equiv.Perm I) (hfix : ∀ x ∈ r, π x = x)
    (hdisj : Disjoint (π '' (s \ r)) (t ∪ r)) : t ∩ π '' s = r := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxt, y, hys, rfl⟩
    by_cases hyr : y ∈ r
    · simpa [hfix y hyr] using hyr
    · exact False.elim (Set.disjoint_left.1 hdisj ⟨y, ⟨hys, hyr⟩, rfl⟩ (Or.inl hxt))
  · intro x hxr
    exact ⟨hrt hxr, x, hrs hxr, hfix x hxr⟩

end SmallPlacements

namespace DiagramForcing.Diagram
universe u
variable {M I : Type u}

@[simp] theorem range_permute (π : Equiv.Perm I) (s : Diagram M I) :
    (s.permute π).range = π '' s.range := by
  change Set.range (π ∘ s) = π '' Set.range s
  exact Set.range_comp π s

/-- Diagram ranges have exactly the cardinality of the monoid. -/
@[simp] theorem cardinal_range (s : Diagram M I) : Cardinal.mk s.range = Cardinal.mk M :=
  (Cardinal.mk_congr (Equiv.ofInjective s s.injective)).symm

theorem permute_eq_of_fixes_range (π : Equiv.Perm I) (s : Diagram M I)
    (hfix : ∀ j ∈ s.range, π j = j) : s.permute π = s := by
  ext x
  exact hfix _ ⟨x, rfl⟩

variable [LeftCancelMonoid M]

theorem ExactOverlap.symm {r s : Diagram M I} (h : ExactOverlap r s) : ExactOverlap s r := by
  rcases h with hd | ⟨a, b, hab, hr⟩
  · exact Or.inl hd.symm
  · exact Or.inr ⟨b, a, hab.symm, by rw [Set.inter_comm, hr, hab]⟩

/-- The binary specialization of finite diagram amalgamation. -/
theorem common_extension_two [Infinite I] [DiagramOrder.IsConical M]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    {r s : Diagram M I} (hov : ExactOverlap r s) :
    ∃ t : Diagram M I, t ≤ r ∧ t ≤ s := by
  obtain ⟨t, ht⟩ := common_extension hsize hmerger ![r, s] (by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hov
    · exact hov.symm
    · exact (hij rfl).elim)
  exact ⟨t, ht 0, ht 1⟩

end DiagramForcing.Diagram

namespace CohenForcing.Condition
universe u v
variable {I : Type u} {κ : Type v}

@[simp] theorem support_permute (π : Equiv.Perm I) (p : Condition I κ) :
    (p.permute π).support = π '' p.support := by
  ext j
  constructor
  · intro hj
    obtain ⟨a, b, hab⟩ := (mem_support _ _).1 hj
    exact ⟨π.symm j, (mem_support p _).2 ⟨a, b, (mem_permute _ _ _).1 hab⟩,
      π.apply_symm_apply j⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨a, b, hab⟩ := (mem_support _ _).1 hj
    exact (mem_support _ _).2 ⟨a, b, (mem_permute _ _ _).2 (by simpa using hab)⟩

theorem cardinal_support (p : Condition I κ) : Cardinal.mk p.support ≤ Cardinal.aleph0 :=
  Cardinal.le_aleph0_iff_set_countable.2 p.countable_support

/-- Fixing the root preserves the Cohen restriction literally. -/
theorem restrict_permute_of_fixes (π : Equiv.Perm I) (p : Condition I κ)
    {J : Set I} (hfix : ∀ j ∈ J, π j = j) :
    restrict (permute π p) J = restrict p J := by
  apply ext
  ext z
  simp only [mem_restrict, mem_permute]
  constructor <;> rintro ⟨hz, hJ⟩
  · have hx : π.symm z.1.1 = z.1.1 := by
      apply π.injective
      simpa using (hfix _ hJ).symm
    exact ⟨by simpa [hx] using hz, hJ⟩
  · have hx : π.symm z.1.1 = z.1.1 := by
      apply π.injective
      simpa using (hfix _ hJ).symm
    exact ⟨by simpa [hx] using hz, hJ⟩

end CohenForcing.Condition

namespace ProductForcing
universe u v
variable {M I : Type u} {κ : Type v}
open DiagramForcing

/-- The actual product of the Cohen and ground diagram posets. -/
abbrev Condition (M I : Type u) (κ : Type v) :=
  CohenForcing.Condition I κ × Diagram M I

/-- Simultaneous transport of labels in both coordinates, as in the paper. -/
def permute (π : Equiv.Perm I) (p : Condition M I κ) : Condition M I κ :=
  (p.1.permute π, p.2.permute π)

@[simp] theorem permute_one (p : Condition M I κ) : permute 1 p = p := by
  simp [permute]

@[simp] theorem permute_mul (π σ : Equiv.Perm I) (p : Condition M I κ) :
    permute (π * σ) p = permute π (permute σ p) := by
  simp [permute]

variable [LeftCancelMonoid M] [DiagramOrder.IsConical M]

def permuteOrderIso (π : Equiv.Perm I) : Condition M I κ ≃o Condition M I κ where
  toFun := permute π
  invFun := permute π⁻¹
  left_inv p := by simp [permute]
  right_inv p := by simp [permute]
  map_rel_iff' := by
    intro p q
    change (p.1.permute π ≤ q.1.permute π ∧ p.2.permute π ≤ q.2.permute π) ↔ _
    exact and_congr (CohenForcing.Condition.permuteOrderIso π).map_rel_iff
      (Diagram.permuteOrderIso π).map_rel_iff

/-- The independent-placement step of local decision (source
`lem:local-decision`). Compatible root restrictions suffice to place the second
product condition compatibly with the first, fixing the entire root diagram.
The monoid finite-merger property remains an explicit, unconstructed input. -/
theorem compatible_placement [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (p s₀ s₁ : Diagram M I) (hs₀ : s₀ ≤ p) (hs₁ : s₁ ≤ p)
    (d₀ d₁ : CohenForcing.Condition I κ)
    (hroot : CohenForcing.Condition.Compatible (d₀.restrict p.range) (d₁.restrict p.range)) :
    ∃ π : Equiv.Perm I, (∀ j ∈ p.range, π j = j) ∧
      s₀.range ∩ (s₁.permute π).range = p.range ∧
      ∃ q : Condition M I κ, q ≤ (d₀, s₀) ∧ q ≤ permute π (d₁, s₁) := by
  let S := s₁.range ∪ d₁.support
  let T := s₀.range ∪ d₀.support
  have hμ : Cardinal.aleph0 ≤ Cardinal.mk M := Cardinal.aleph0_le_mk M
  have hS : Cardinal.mk S ≤ Cardinal.mk M := SmallPlacements.union_bound hμ
    (by simp) (d₁.cardinal_support.trans hμ)
  have hT : Cardinal.mk T ≤ Cardinal.mk M := SmallPlacements.union_bound hμ
    (by simp) (d₀.cardinal_support.trans hμ)
  obtain ⟨π, hfix, hdisj⟩ := SmallPlacements.move_off
    ((SmallPlacements.union_bound hμ (SmallPlacements.union_bound hμ hS hT)
      (by simp : Cardinal.mk p.range ≤ Cardinal.mk M)).trans_lt hsize)
  have hs₀r := Diagram.range_antitone hs₀
  have hs₁r := Diagram.range_antitone hs₁
  have hdi : Disjoint (π '' (s₁.range \ p.range)) (s₀.range ∪ p.range) := by
    apply hdisj.mono
    · exact Set.image_mono (Set.sdiff_subset_sdiff_left Set.subset_union_left)
    · exact Set.union_subset_union Set.subset_union_left Set.Subset.rfl
  have hinter : s₀.range ∩ (s₁.permute π).range = p.range := by
    rw [Diagram.range_permute]
    exact SmallPlacements.intersection_eq_root hs₁r hs₀r π hfix hdi
  have hpf : p.permute π = p := Diagram.permute_eq_of_fixes_range π p hfix
  have hs₁p : s₁.permute π ≤ p := by
    rw [← hpf]
    exact (Diagram.permuteOrderIso π).monotone hs₁
  have hov : Diagram.ExactOverlap s₀ (s₁.permute π) := by
    obtain ⟨a, ha⟩ := hs₀
    obtain ⟨b, hb⟩ := hs₁p
    exact Or.inr ⟨a, b, ha.trans hb.symm, by rwa [ha]⟩
  obtain ⟨t, ht₀, ht₁⟩ := Diagram.common_extension_two hsize hmerger hov
  have hcdisj : Disjoint (d₀.support \ p.range) ((d₁.permute π).support \ p.range) := by
    rw [Set.disjoint_left]
    rintro j ⟨hj₀, hjp⟩ ⟨hj₁, _⟩
    rw [CohenForcing.Condition.support_permute] at hj₁
    obtain ⟨k, hk, rfl⟩ := hj₁
    have hkp : k ∉ p.range := fun h => hjp (by simpa [hfix k h] using h)
    exact Set.disjoint_left.1 hdisj ⟨k, ⟨Or.inr hk, hkp⟩, rfl⟩ (Or.inl (Or.inr hj₀))
  have hcroot : CohenForcing.Condition.Compatible (d₀.restrict p.range)
      ((d₁.permute π).restrict p.range) := by
    rwa [CohenForcing.Condition.restrict_permute_of_fixes π d₁ hfix]
  have hc := CohenForcing.Condition.compatible_of_disjoint_off_root d₀ _ _ hcroot hcdisj
  obtain ⟨d, hd₀, hd₁⟩ := CohenForcing.Condition.compatible_iff.1 hc
  exact ⟨π, hfix, hinter, (d, t), ⟨hd₀, ht₀⟩, ⟨hd₁, ht₁⟩⟩

end ProductForcing

end PartitionConsistency

end OAI
