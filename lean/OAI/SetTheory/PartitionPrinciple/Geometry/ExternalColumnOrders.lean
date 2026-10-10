import OAI.SetTheory.PartitionPrinciple.Definability.ExternalColumnCodes

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps
universe u

noncomputable def ordinalColumnOrder {C : ZFSet.{u}} (ordinal : ordinalSetProperty C) :
    LinearHeightOrder (SetMembers C) where
  lt x y := SetMembers.raw x ∈ SetMembers.raw y
  irrefl x := ZFSet.mem_irrefl (SetMembers.raw x)
  trans {x y z} lower upper := ordinal.2 (SetMembers.raw z) (SetMembers.raw_mem z) (SetMembers.raw y) upper (SetMembers.raw x) lower
  compare x y := (ordinalSetProperty_mem_compare ordinal (SetMembers.raw_mem x) (SetMembers.raw_mem y)).imp id
    (fun h => h.imp (fun eq => SetMembers.raw_injective C eq) id)

namespace ExternalColumnCode
variable {C K base sequence cap : ZFSet.{u}} (code : ExternalColumnCode C K base sequence cap)

theorem typed_increasing (ordinal : ordinalSetProperty C) (n : Nat) :
    (ordinalColumnOrder ordinal).lt (code.smallColumn n) (code.smallColumn (n + 1)) :=
  code.smallColumn_increasing n

theorem typed_cap_bound (ordinal : ordinalSetProperty C) (n : Nat) :
    (ordinalColumnOrder ordinal).lt (code.smallColumn n) (SetMembers.ofMem cap code.cap_mem) := by
  simpa only [ordinalColumnOrder, SetMembers.raw_ofMem] using code.smallColumn_bounded n

theorem typed_old_bound (ordinal : ordinalSetProperty C) (x : SetMembers C)
    (member : SetMembers.raw x ∈ K) (n : Nat) :
    (ordinalColumnOrder ordinal).lt x (code.smallColumn n) := by
  simpa only [ordinalColumnOrder, smallColumn, SetMembers.raw_ofMem] using code.old_below member n

end ExternalColumnCode

end PartitionPilot.Forcing

end

end OAI
