import Mathlib
import OAI.SetTheory.PartitionConsistency.Algebra.Placements
import OAI.SetTheory.PartitionConsistency.Forcing.CohenForcing
import OAI.SetTheory.PartitionConsistency.Forcing.ForcingQuotient

namespace OAI

namespace PartitionConsistency
namespace SmallPlacements

/-- Only countably many members of a pairwise disjoint family meet a fixed
countable set. This will be applied to the nonroot supports of probe copies. -/
theorem countable_obstructions {I A : Type*} (S : A → Set I) (C : Set I)
    (hS : Pairwise (fun a b => Disjoint (S a) (S b))) (hC : C.Countable) :
    {a | (S a ∩ C).Nonempty}.Countable :=
  Set.countable_ofPred_nonempty_of_disjoint
    (fun _a _b hab => (hS hab).mono Set.inter_subset_left Set.inter_subset_left)
    (fun _ => Set.inter_subset_right) hC

/-- An uncountable family of disjoint nonroot supports always has a member
avoiding any specified countable collection of coordinates. -/
theorem exists_fresh_member {I A : Type*} [Uncountable A] (S : A → Set I)
    (C : Set I) (hS : Pairwise (fun a b => Disjoint (S a) (S b))) (hC : C.Countable) :
    ∃ a, Disjoint (S a) C := by
  have hc := countable_obstructions S C hS hC
  have hn : {a | (S a ∩ C).Nonempty} ≠ Set.univ := by
    intro hu
    exact Set.not_countable_univ (hu ▸ hc)
  obtain ⟨a, ha⟩ := Set.ne_univ_iff_exists_notMem _ |>.1 hn
  exact ⟨a, Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 ha)⟩

end SmallPlacements

namespace CohenForcing.Condition
universe u v w
variable {I : Type u} {κ : Type v} {A : Type w}

@[refl] theorem Compatible.refl (p : Condition I κ) : Compatible p p := p.functional

/-- Weakening either of two compatible partial functions preserves their
compatibility. Recall that the forcing order is reverse inclusion. -/
theorem Compatible.weaken {p q p' q' : Condition I κ} (h : Compatible p q)
    (hp : p ≤ p') (hq : q ≤ q') : Compatible p' q' :=
  fun a b c hb hc => h a b c (hp hb) (hq hc)

theorem Compatible.of_le {p q : Condition I κ} (h : p ≤ q) : Compatible p q :=
  (Compatible.refl p).weaken le_rfl h

/-- The explicit ground dense set in the probe argument for ordinal choice
(source equation `eq:probe-cohen-dense`). It contains conditions incompatible
with the common root and conditions extending one of the placed copies. -/
def probeDenseSet (root : Condition I κ) (copies : A → Condition I κ) :
    Set (Condition I κ) :=
  {c | ¬ Compatible c root ∨ ∃ a, c ≤ copies a}

/-- Pairwise independent copies with the same Cohen root give the probe dense
set. Uncountability is sufficient: a test condition has countable support.
No forcing name, generic extension, or choice in a symmetric model is assumed. -/
theorem probeDenseSet_dense [Uncountable A] (J : Set I) (root : Condition I κ)
    (copies : A → Condition I κ) (hroot : ∀ a, (copies a).restrict J = root)
    (hdisj : Pairwise (fun a b => Disjoint ((copies a).support \ J) ((copies b).support \ J))) :
    ForcingQuotient.Dense (probeDenseSet root copies) := by
  intro c
  by_cases hc : Compatible c root
  · obtain ⟨a, ha⟩ := SmallPlacements.exists_fresh_member
      (fun a => (copies a).support \ J) c.support hdisj c.countable_support
    have hr : Compatible (c.restrict J) ((copies a).restrict J) := by
      rw [hroot a]
      exact hc.weaken (le_restrict c J) le_rfl
    have hd : Disjoint (c.support \ J) ((copies a).support \ J) :=
      (ha.mono_right Set.sdiff_subset).symm
    have h := compatible_of_disjoint_off_root c (copies a) J hr hd
    exact ⟨union c (copies a) h, (union_le_left _ _ _),
      Or.inr ⟨a, union_le_right _ _ _⟩⟩
  · exact ⟨c, le_rfl, Or.inl hc⟩

/-- A filter containing the common root and meeting the displayed dense set
contains an extension of one of the copies. It is not necessary, and would be
incorrect, to assume that any preselected moved condition belongs to the filter. -/
theorem meets_probe {root : Condition I κ} {copies : A → Condition I κ}
    (G : ForcingQuotient.GenericFilter (Condition I κ)) (hroot : root ∈ G)
    (hmeets : ∃ c : Condition I κ, c ∈ G ∧ c ∈ probeDenseSet root copies) :
    ∃ a, ∃ c : Condition I κ, c ∈ G ∧ c ≤ copies a := by
  obtain ⟨c, hcG, hc⟩ := hmeets
  rcases hc with hn | ⟨a, ha⟩
  · obtain ⟨d, _, hdc, hdr⟩ := G.directed c hcG root hroot
    exact (hn (compatible_iff.2 ⟨d, hdc, hdr⟩)).elim
  · exact ⟨a, c, hcG, ha⟩

end CohenForcing.Condition
end PartitionConsistency

end OAI
