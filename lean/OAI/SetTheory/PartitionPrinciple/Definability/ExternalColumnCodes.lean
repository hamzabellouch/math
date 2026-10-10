import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCodedBinaryHeights

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps
universe u

theorem successorColumnGraph_injection {C base sequence : ZFSet.{u}}
    (function : ZFSet.IsFunc ZFSet.omega C sequence)
    (entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ sequence ↔ y = compressionStamp base n) :
    InjectionCode ZFSet.omega C sequence := by
  refine ⟨function, ?_⟩
  intro x y z first second
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 (ZFSet.pair_mem_prod.1 (function.1 first)).1
  obtain ⟨m, rfl⟩ := (mem_omega_iff_natSetCode y).1 (ZFSet.pair_mem_prod.1 (function.1 second)).1
  have equal := ((entries n z).1 first).symm.trans ((entries m z).1 second)
  have same : n = m := by
    by_contra different
    rcases Nat.lt_or_gt_of_ne different with lower | greater
    · have member := (compressionStamp_mem_iff base n m).2 lower
      rw [equal] at member
      exact ZFSet.mem_irrefl _ member
    · have member := (compressionStamp_mem_iff base m n).2 greater
      rw [equal] at member
      exact ZFSet.mem_irrefl _ member
  exact congrArg natSetCode same

structure ExternalColumnCode (C K base sequence cap : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc ZFSet.omega C sequence
  entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ sequence ↔ y = compressionStamp base n
  base_mem : base ∈ C
  cap_mem : cap ∈ C
  old_bound : ∀ a ∈ K, a ∈ base
  cap_bound : ∀ n, compressionStamp base n ∈ cap

namespace ExternalColumnCode
variable {C K base sequence cap : ZFSet.{u}} (code : ExternalColumnCode C K base sequence cap)
include code

theorem value_mem (n : Nat) : compressionStamp base n ∈ C :=
  (ZFSet.pair_mem_prod.1 (code.function.1 ((code.entries n _).2 rfl))).2

theorem old_below {a : ZFSet.{u}} (ha : a ∈ K) (n : Nat) : a ∈ compressionStamp base n :=
  compressionStamp_old_mem (Or.inl (code.old_bound a ha)) n

theorem injection : InjectionCode ZFSet.omega C sequence :=
  successorColumnGraph_injection code.function code.entries

noncomputable def smallColumn (n : Nat) : SetMembers C :=
  SetMembers.ofMem (compressionStamp base n) (code.value_mem n)

theorem smallColumn_graph :
    natPresentation.graph (SetMembers.presentation C) (fun n => code.smallColumn n.down) = sequence := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨n, rfl⟩ := (natPresentation.mem_graph (SetMembers.presentation C) _ z).1 hz
    exact (code.entries n.down _).2 (SetMembers.raw_ofMem _ _)
  · intro hz
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 hz)
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 hx
    have equal := (code.entries n y).1 hz
    exact (natPresentation.mem_graph (SetMembers.presentation C) _ _).2
      ⟨⟨n⟩, by change ZFSet.pair (natSetCode n) (SetMembers.raw (code.smallColumn n)) = _
               simp only [smallColumn, SetMembers.raw_ofMem, equal]⟩

theorem smallColumn_increasing (n : Nat) :
    SetMembers.raw (code.smallColumn n) ∈ SetMembers.raw (code.smallColumn (n + 1)) := by
  simp only [smallColumn, SetMembers.raw_ofMem]
  exact (compressionStamp_mem_iff base n (n + 1)).2 (Nat.lt_succ_self n)

theorem smallColumn_bounded (n : Nat) : SetMembers.raw (code.smallColumn n) ∈ cap := by
  simpa only [smallColumn, SetMembers.raw_ofMem] using code.cap_bound n

theorem old_height_below {P D old : ZFSet.{u}}
    (function : ZFSet.IsFunc P (ZFSet.prod C D) old)
    (columns : heightColumns P C D old ⊆ K)
    {x a q : ZFSet.{u}} (entry : ZFSet.pair x (ZFSet.pair a q) ∈ old) (n : Nat) :
    a ∈ SetMembers.raw (code.smallColumn n) := by
  simpa only [smallColumn, SetMembers.raw_ofMem] using
    code.old_below (columns (mem_heightColumns_of_entry function entry)) n

end ExternalColumnCode

structure GroundExternalColumnData (M : TransitiveGround.{u}) (C K : ZFSet.{u}) where
  base : ZFSet.{u}
  sequence : ZFSet.{u}
  cap : ZFSet.{u}
  sequence_ground : sequence ∈ M.sets
  code : ExternalColumnCode C K base sequence cap
  range_ground : relationImage ZFSet.omega C sequence ∈ M.sets
  inverse_ground : relationConverse ZFSet.omega C sequence ∈ M.sets
  inverse_code : InjectionCode (relationImage ZFSet.omega C sequence) ZFSet.omega
    (relationConverse ZFSet.omega C sequence)

end PartitionPilot.Forcing

end

end OAI
