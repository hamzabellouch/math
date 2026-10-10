import Mathlib.SetTheory.ZFC.Rank

namespace OAI

section

namespace PartitionPilot.SetRealization

universe u

noncomputable def ordinalCode (o : Ordinal.{u}) : ZFSet.{u} :=
  ZFSet.range (fun i : Set.Iio o => ordinalCode i.val)
termination_by o
decreasing_by exact i.property

theorem ordinalCode_eq (o : Ordinal.{u}) :
    ordinalCode o = ZFSet.range (fun i : Set.Iio o => ordinalCode i.val) := by
  exact ordinalCode.eq_def o

theorem rank_ordinalCode (o : Ordinal.{u}) : ZFSet.rank (ordinalCode o) = o := by
  have wf : WellFounded ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop) := wellFounded_lt
  induction o using wf.induction with
  | h o ih =>
    rw [ordinalCode_eq, ZFSet.rank_range]
    have ranks : (fun i : Set.Iio o => Order.succ (ZFSet.rank (ordinalCode i.val))) =
        (fun i : Set.Iio o => Order.succ i.val) := by
      funext i
      rw [ih i.val i.property]
    simp_rw [ranks, Order.succ_eq_add_one]
    apply le_antisymm (Ordinal.iSup_add_one_le fun index => index.property)
    by_contra! smaller
    exact lt_irrefl _ (Ordinal.lt_iSup_add_one
      (fun index : Set.Iio o => index.val) ⟨_, smaller⟩)

theorem ordinalCode_injective : Function.Injective (ordinalCode.{u}) := by
  intro a b eq
  have ranks := congrArg ZFSet.rank eq
  simpa only [rank_ordinalCode] using ranks

theorem mem_ordinalCode_iff (a b : Ordinal.{u}) :
    ordinalCode a ∈ ordinalCode b ↔ a < b := by
  rw [ordinalCode_eq b, ZFSet.mem_range]
  constructor
  · rintro ⟨i, eq⟩
    exact (ordinalCode_injective eq) ▸ i.property
  · intro h
    exact ⟨⟨a, h⟩, rfl⟩

theorem mem_ordinalCode {x : ZFSet.{u}} {o : Ordinal.{u}} :
    x ∈ ordinalCode o ↔ ∃ a < o, ordinalCode a = x := by
  rw [ordinalCode_eq o, ZFSet.mem_range]
  constructor
  · rintro ⟨i, eq⟩
    exact ⟨i.val, i.property, eq⟩
  · rintro ⟨a, h, eq⟩
    exact ⟨⟨a, h⟩, eq⟩

end PartitionPilot.SetRealization

end

end OAI
