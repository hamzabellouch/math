import Mathlib

namespace OAI

namespace PartitionConsistency
namespace SmallPlacements
open Cardinal
universe u
variable {α β : Type u}

/-- A partial injection on a subset of a smaller set can be completed to an
injection into the larger infinite set. This is a ground-choice construction. -/
theorem extend_embedding [Infinite β] (h : #α < #β) {s : Set α} (f : s ↪ β) :
    ∃ g : α ↪ β, ∀ x : s, g x = f x := by
  classical
  have hf : #(Set.range f) < #β := by
    rw [← Cardinal.mk_congr (Equiv.ofInjective f f.injective)]
    exact (Cardinal.mk_le_of_injective Subtype.val_injective).trans_lt h
  have hc : #(sᶜ : Set α) ≤ #((Set.range f)ᶜ : Set β) := by
    rw [Cardinal.mk_compl_of_infinite _ hf]
    exact (Cardinal.mk_le_of_injective Subtype.val_injective).trans h.le
  obtain ⟨k⟩ := hc
  let g : α → β := fun a => if ha : a ∈ s then f ⟨a, ha⟩ else k ⟨a, ha⟩
  have hg : Function.Injective g := by
    intro a b hab
    by_cases ha : a ∈ s <;> by_cases hb : b ∈ s
    · simp only [g, dite_eq_left ha, dite_eq_left hb] at hab
      exact congrArg Subtype.val (f.injective hab)
    · simp only [g, dite_eq_left ha, dite_eq_right hb] at hab
      exact False.elim ((k ⟨b, hb⟩).property ⟨⟨a, ha⟩, hab⟩)
    · simp only [g, dite_eq_right ha, dite_eq_left hb] at hab
      exact False.elim ((k ⟨a, ha⟩).property ⟨⟨b, hb⟩, hab.symm⟩)
    · simp only [g, dite_eq_right ha, dite_eq_right hb] at hab
      exact congrArg Subtype.val (k.injective (Subtype.ext hab))
  exact ⟨⟨g, hg⟩, fun x => by simp [g, x.property]⟩

/-- An embedding into a larger infinite set can be chosen to cover a prescribed
subset whose cardinality does not exceed that of its domain. -/
theorem embedding_cover [Infinite β] (h : #α < #β) {s : Set β} (hs : #s ≤ #α) :
    ∃ g : α ↪ β, s ⊆ Set.range g := by
  classical
  obtain ⟨k⟩ := hs
  let e : s ≃ Set.range k := Equiv.ofInjective k k.injective
  let f : Set.range k ↪ β := e.symm.toEmbedding.trans (Function.Embedding.subtype _)
  obtain ⟨g, hg⟩ := extend_embedding h f
  refine ⟨g, ?_⟩
  intro b hb
  refine ⟨k ⟨b, hb⟩, ?_⟩
  simpa [f, e] using hg (e ⟨b, hb⟩)

/-- Complete an existing partial injection and cover a prescribed small subset
at the same time. No value already prescribed is altered. -/
theorem extend_embedding_cover [Infinite β] (h : #α < #β) {s : Set α}
    (f : s ↪ β) {J : Set β} (hJ : #J ≤ #(sᶜ : Set α)) :
    ∃ g : α ↪ β, (∀ x : s, g x = f x) ∧ J ⊆ Set.range g := by
  classical
  have hfr : #(Set.range f) < #β := by
    rw [← Cardinal.mk_congr (Equiv.ofInjective f f.injective)]
    exact (Cardinal.mk_le_of_injective Subtype.val_injective).trans_lt h
  have hcom : #((Set.range f)ᶜ : Set β) = #β :=
    Cardinal.mk_compl_of_infinite _ hfr
  let _ : Infinite ((Set.range f)ᶜ : Set β) :=
    Cardinal.infinite_iff.2 (by rw [hcom]; exact Cardinal.aleph0_le_mk β)
  let K : Set ((Set.range f)ᶜ : Set β) := {b | b.val ∈ J}
  have hK : #K ≤ #(sᶜ : Set α) := by
    have hk : Function.Injective (fun x : K => (⟨x.val.val, x.property⟩ : J)) := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : J => z.val) hxy
    exact (Cardinal.mk_le_of_injective hk).trans hJ
  obtain ⟨k, hk⟩ := embedding_cover
    (α := (sᶜ : Set α)) (β := ((Set.range f)ᶜ : Set β))
    (by rw [hcom]; exact (Cardinal.mk_le_of_injective Subtype.val_injective).trans_lt h) hK
  let g : α → β := fun a => if ha : a ∈ s then f ⟨a, ha⟩ else k ⟨a, ha⟩
  have hg : Function.Injective g := by
    intro a b hab
    by_cases ha : a ∈ s <;> by_cases hb : b ∈ s
    · simp only [g, dite_eq_left ha, dite_eq_left hb] at hab
      exact congrArg Subtype.val (f.injective hab)
    · simp only [g, dite_eq_left ha, dite_eq_right hb] at hab
      exact False.elim ((k ⟨b, hb⟩).property ⟨⟨a, ha⟩, hab⟩)
    · simp only [g, dite_eq_right ha, dite_eq_left hb] at hab
      exact False.elim ((k ⟨a, ha⟩).property ⟨⟨b, hb⟩, hab.symm⟩)
    · simp only [g, dite_eq_right ha, dite_eq_right hb] at hab
      exact congrArg Subtype.val (k.injective (Subtype.ext hab))
  refine ⟨⟨g, hg⟩, (fun x => by simp [g, x.property]), ?_⟩
  intro b hb
  by_cases hbf : b ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hbf
    exact ⟨x.val, by simp [g, x.property]⟩
  · obtain ⟨x, hx⟩ := hk (show (⟨b, hbf⟩ : ((Set.range f)ᶜ : Set β)) ∈ K from hb)
    refine ⟨x.val, ?_⟩
    have hn : x.val ∉ s := x.property
    change (if h : x.val ∈ s then f ⟨x.val, h⟩ else (k x).val) = b
    rw [dite_eq_right hn]
    exact congrArg Subtype.val hx

/-- A small ground partial placement extends to a permutation. -/
theorem extend_permutation {s : Set α} (f : s ↪ α) (hs : #s < #α) :
    ∃ π : Equiv.Perm α, ∀ x : s, π x = f x :=
  Cardinal.extend_function_of_lt f hs ⟨Equiv.refl α⟩

/-- Move a small set off any other small set, leaving a specified common
root fixed. The complement of the forbidden union supplies the fresh labels. -/
theorem move_off [Infinite α] {s t r : Set α}
    (hst : #(s ∪ t ∪ r : Set α) < #α) :
    ∃ π : Equiv.Perm α, (∀ x ∈ r, π x = x) ∧
      Disjoint (π '' (s \ r)) (t ∪ r) := by
  classical
  have hc : #((s ∪ t ∪ r)ᶜ : Set α) = #α :=
    Cardinal.mk_compl_of_infinite _ hst
  have he : #(s \ r : Set α) ≤ #((s ∪ t ∪ r)ᶜ : Set α) := by
    rw [hc]
    exact Cardinal.mk_le_of_injective Subtype.val_injective
  obtain ⟨e⟩ := he
  let f : (s ∪ r : Set α) → α :=
    fun x => if hx : x.val ∈ r then x.val else e ⟨x.val, (x.property.resolve_right hx), hx⟩
  have hf : Function.Injective f := by
    intro a b hab
    by_cases ha : a.val ∈ r <;> by_cases hb : b.val ∈ r
    · simp only [f, dite_eq_left ha, dite_eq_left hb] at hab
      exact Subtype.ext hab
    · simp only [f, dite_eq_left ha, dite_eq_right hb] at hab
      exact False.elim ((e ⟨b.val, b.property.resolve_right hb, hb⟩).property
        (hab ▸ Or.inr ha))
    · simp only [f, dite_eq_right ha, dite_eq_left hb] at hab
      exact False.elim ((e ⟨a.val, a.property.resolve_right ha, ha⟩).property
        (hab.symm ▸ Or.inr hb))
    · simp only [f, dite_eq_right ha, dite_eq_right hb] at hab
      apply Subtype.ext
      exact congrArg (fun z : (s \ r : Set α) => z.val) (e.injective (Subtype.ext hab))
  have hsr : #(s ∪ r : Set α) < #α :=
    (Cardinal.mk_le_mk_of_subset (by intro x hx; simp only [Set.mem_union] at hx ⊢; tauto)).trans_lt hst
  obtain ⟨π, hπ⟩ := extend_permutation ⟨f, hf⟩ hsr
  refine ⟨π, ?_, ?_⟩
  · intro x hx
    simpa [f, hx] using hπ ⟨x, Or.inr hx⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨x, ⟨hx, hxr⟩, rfl⟩ ht
    have hp : π x = e ⟨x, hx, hxr⟩ := by
      simpa [f, hxr] using hπ ⟨x, Or.inl hx⟩
    rw [hp] at ht
    apply (e ⟨x, hx, hxr⟩).property
    rcases ht with ht | ht
    · exact Or.inl (Or.inr ht)
    · exact Or.inr ht

end SmallPlacements
end PartitionConsistency

end OAI
