import OAI.SetTheory.PartitionPrinciple.Transfinite.OrdinalSetCodes

namespace OAI

section

namespace PartitionPilot.SetRealization

open Cardinal
open scoped Cardinal
universe u

structure Presentation (A : Type u) where
  carrier : ZFSet.{u}
  encode : A → ZFSet.{u}
  injective : Function.Injective encode
  mem_carrier : ∀ x, x ∈ carrier ↔ ∃ a, encode a = x

namespace Presentation
variable {A B : Type u}

theorem encode_mem (s : Presentation A) (a : A) : s.encode a ∈ s.carrier :=
  (s.mem_carrier _).2 ⟨a, rfl⟩

noncomputable def carrierEquiv (s : Presentation A) : A ≃ s.carrier.toSet :=
  Equiv.ofBijective (fun a => ⟨s.encode a, s.encode_mem a⟩) ⟨
    fun _ _ h => s.injective (congrArg Subtype.val h),
    fun x => by
      rcases (s.mem_carrier x.val).1 x.property with ⟨a, ha⟩
      exact ⟨a, Subtype.ext ha⟩⟩

noncomputable def ordinalIndex (A : Type u) : A ≃ Set.Iio (#A).ord :=
  (Nonempty.some (Cardinal.eq.mp (Cardinal.mk_ord_toType (#A)).symm)).trans
    (Ordinal.ToType.mk (o := (#A).ord)).toEquiv.symm

noncomputable def canonical (A : Type u) : Presentation A where
  carrier := ordinalCode (#A).ord
  encode a := ordinalCode (ordinalIndex A a).val
  injective := by
    intro a b eq
    exact (ordinalIndex A).injective (Subtype.ext (ordinalCode_injective eq))
  mem_carrier x := by
    rw [mem_ordinalCode]
    constructor
    · rintro ⟨o, h, eq⟩
      rcases (ordinalIndex A).surjective ⟨o, h⟩ with ⟨a, ha⟩
      exact ⟨a, by rw [ha]; exact eq⟩
    · rintro ⟨a, eq⟩
      exact ⟨(ordinalIndex A a).val, (ordinalIndex A a).property, eq⟩

theorem rank_canonical (A : Type u) : ZFSet.rank (canonical A).carrier = (#A).ord :=
  rank_ordinalCode _

theorem canonical_rank_lt (A : Type u) (κ : Cardinal.{u}) (small : #A < κ) :
    ZFSet.rank (canonical A).carrier < κ.ord := by
  rw [rank_canonical]
  exact Cardinal.ord_lt_ord.2 small

noncomputable def product (s : Presentation A) (t : Presentation B) : Presentation (A × B) where
  carrier := ZFSet.prod s.carrier t.carrier
  encode a := ZFSet.pair (s.encode a.1) (t.encode a.2)
  injective := by
    intro a b eq
    have parts := ZFSet.pair_inj.1 eq
    exact Prod.ext (s.injective parts.1) (t.injective parts.2)
  mem_carrier x := by
    rw [ZFSet.mem_prod]
    constructor
    · rintro ⟨y, hy, z, hz, eq⟩
      rcases (s.mem_carrier y).1 hy with ⟨a, ha⟩
      rcases (t.mem_carrier z).1 hz with ⟨b, hb⟩
      exact ⟨(a, b), by rw [ha, hb]; exact eq.symm⟩
    · rintro ⟨a, eq⟩
      exact ⟨s.encode a.1, s.encode_mem a.1, t.encode a.2, t.encode_mem a.2, eq.symm⟩

noncomputable def subset (s : Presentation A) (p : A → Prop) : ZFSet.{u} :=
  ZFSet.range (fun a : Subtype p => s.encode a.val)

theorem mem_subset (s : Presentation A) (p : A → Prop) (x : ZFSet.{u}) :
    x ∈ s.subset p ↔ ∃ a, p a ∧ s.encode a = x := by
  rw [subset, ZFSet.mem_range]
  constructor
  · rintro ⟨a, eq⟩
    exact ⟨a.val, a.property, eq⟩
  · rintro ⟨a, h, eq⟩
    exact ⟨⟨a, h⟩, eq⟩

theorem encode_mem_subset (s : Presentation A) (p : A → Prop) (a : A) :
    s.encode a ∈ s.subset p ↔ p a := by
  rw [mem_subset]
  constructor
  · rintro ⟨b, hb, eq⟩
    exact s.injective eq ▸ hb
  · intro h
    exact ⟨a, h, rfl⟩

theorem subset_carrier (s : Presentation A) (p : A → Prop) : s.subset p ⊆ s.carrier := by
  intro x hx
  rcases (s.mem_subset p x).1 hx with ⟨a, _, eq⟩
  exact eq ▸ s.encode_mem a

theorem rank_subset_le (s : Presentation A) (p : A → Prop) :
    ZFSet.rank (s.subset p) ≤ ZFSet.rank s.carrier :=
  ZFSet.rank_mono (s.subset_carrier p)

end Presentation
end PartitionPilot.SetRealization

end

end OAI
