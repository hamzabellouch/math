import OAI.SetTheory.PartitionPrinciple.Transfinite.SetRankBounds

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

def taggedExtension (P N : ZFSet.{u}) : ZFSet.{u} :=
  P ∪ ZFSet.prod {P} N

theorem pair_tag_not_mem (P q : ZFSet.{u}) : ZFSet.pair P q ∉ P := by
  intro member
  have first : ZFSet.rank P < ZFSet.rank ({P} : ZFSet.{u}) :=
    ZFSet.rank_lt_of_mem (ZFSet.mem_singleton.2 rfl)
  have second : ZFSet.rank ({P} : ZFSet.{u}) < ZFSet.rank (ZFSet.pair P q) :=
    ZFSet.rank_lt_of_mem (ZFSet.mem_pair.2 (Or.inl rfl))
  exact (lt_irrefl (ZFSet.rank P))
    (first.trans (second.trans (ZFSet.rank_lt_of_mem member)))

theorem mem_taggedExtension {P N z : ZFSet.{u}} :
    z ∈ taggedExtension P N ↔ z ∈ P ∨ ∃ q ∈ N, z = ZFSet.pair P q := by
  constructor
  · intro hz
    rcases ZFSet.mem_union.1 hz with hz | hz
    · exact Or.inl hz
    · obtain ⟨p, hp, q, hq, eq⟩ := ZFSet.mem_prod.1 hz
      exact Or.inr ⟨q, hq, (ZFSet.mem_singleton.1 hp) ▸ eq⟩
  · intro hz
    rcases hz with hz | ⟨q, hq, rfl⟩
    · exact ZFSet.mem_union.2 (Or.inl hz)
    · exact ZFSet.mem_union.2
        (Or.inr (ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, hq⟩))

theorem old_mem_taggedExtension {P N z : ZFSet.{u}} (hz : z ∈ P) :
    z ∈ taggedExtension P N :=
  mem_taggedExtension.2 (Or.inl hz)

theorem pair_mem_taggedExtension {P N q : ZFSet.{u}} :
    ZFSet.pair P q ∈ taggedExtension P N ↔ q ∈ N := by
  constructor
  · intro h
    rcases mem_taggedExtension.1 h with old | ⟨r, hr, eq⟩
    · exact False.elim (pair_tag_not_mem P q old)
    · exact (ZFSet.pair_inj.1 eq).2.symm ▸ hr
  · intro hq
    exact mem_taggedExtension.2 (Or.inr ⟨q, hq, rfl⟩)

theorem taggedExtension_disjoint (P N : ZFSet.{u}) :
    ∀ z ∈ P, z ∉ ZFSet.prod {P} N := by
  intro z hz tagged
  obtain ⟨p, hp, q, _, eq⟩ := ZFSet.mem_prod.1 tagged
  have same : z = ZFSet.pair P q := (ZFSet.mem_singleton.1 hp) ▸ eq
  exact pair_tag_not_mem P q (same ▸ hz)

def taggedExtensionEncode (P N : ZFSet.{u}) :
    ({x : ZFSet.{u} // x ∈ P} ⊕ {q : ZFSet.{u} // q ∈ N}) → ZFSet.{u}
  | .inl x => x.val
  | .inr q => ZFSet.pair P q.val

theorem taggedExtensionEncode_inl (P N : ZFSet.{u}) (x : {x : ZFSet.{u} // x ∈ P}) :
    taggedExtensionEncode P N (.inl x) = x.val := rfl

theorem taggedExtensionEncode_inr (P N : ZFSet.{u}) (q : {q : ZFSet.{u} // q ∈ N}) :
    taggedExtensionEncode P N (.inr q) = ZFSet.pair P q.val := rfl

theorem taggedExtensionEncode_mem (P N : ZFSet.{u})
    (x : {x : ZFSet.{u} // x ∈ P} ⊕ {q : ZFSet.{u} // q ∈ N}) :
    taggedExtensionEncode P N x ∈ taggedExtension P N := by
  cases x with
  | inl x => exact old_mem_taggedExtension x.property
  | inr q => exact pair_mem_taggedExtension.2 q.property

theorem taggedExtensionEncode_injective (P N : ZFSet.{u}) :
    Function.Injective (taggedExtensionEncode P N) := by
  intro x y eq
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (Subtype.ext eq)
    | inr q =>
      change x.val = ZFSet.pair P q.val at eq
      exact False.elim (pair_tag_not_mem P q.val (eq ▸ x.property))
  | inr q =>
    cases y with
    | inl x =>
      change ZFSet.pair P q.val = x.val at eq
      exact False.elim (pair_tag_not_mem P q.val (eq.symm ▸ x.property))
    | inr r => exact congrArg Sum.inr (Subtype.ext (ZFSet.pair_inj.1 eq).2)

theorem taggedExtensionEncode_surjective (P N : ZFSet.{u}) :
    ∀ z ∈ taggedExtension P N,
      ∃ x : {x : ZFSet.{u} // x ∈ P} ⊕ {q : ZFSet.{u} // q ∈ N},
        taggedExtensionEncode P N x = z := by
  intro z hz
  rcases mem_taggedExtension.1 hz with old | ⟨q, hq, eq⟩
  · exact ⟨Sum.inl ⟨z, old⟩, rfl⟩
  · exact ⟨Sum.inr ⟨q, hq⟩, eq.symm⟩

noncomputable def taggedExtensionEquiv (P N : ZFSet.{u}) :
    ({x : ZFSet.{u} // x ∈ P} ⊕ {q : ZFSet.{u} // q ∈ N}) ≃
      {z : ZFSet.{u} // z ∈ taggedExtension P N} :=
  Equiv.ofBijective (fun x => ⟨taggedExtensionEncode P N x, taggedExtensionEncode_mem P N x⟩)
    ⟨fun _ _ eq => taggedExtensionEncode_injective P N (congrArg Subtype.val eq),
      fun z => by
        obtain ⟨x, eq⟩ := taggedExtensionEncode_surjective P N z.val z.property
        exact ⟨x, Subtype.ext eq⟩⟩

end PartitionPilot.Forcing

end

end OAI
