import OAI.SetTheory.PartitionPrinciple.Forcing.GroundBinaryRowNames

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization
universe u
variable (M : TransitiveGround.{u})

noncomputable def binaryRowSetName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    Name (SetMembers.presentation (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :=
  Name.assemble (fun i : SetMembers I => M.binaryRowName I C one (SetMembers.raw i)) (fun _ => one)

theorem entry_binaryRowSetName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (σ : Name (SetMembers.presentation
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)))
    (p : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    Name.Entry σ (M.binaryRowSetName I C one) p ↔
      ∃ i ∈ I, M.binaryRowName I C one i = σ ∧ one = p := by
  rw [binaryRowSetName, Name.entry_assemble]
  constructor
  · rintro ⟨i, eq, condition⟩
    exact ⟨SetMembers.raw i, SetMembers.raw_mem i, eq, condition⟩
  · rintro ⟨i, hi, eq, condition⟩
    exact ⟨SetMembers.ofMem i hi, by simpa only [SetMembers.raw_ofMem] using eq, condition⟩

theorem mem_binaryRowSetName_code (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (z : ZFSet.{u}) :
    z ∈ (M.binaryRowSetName I C one).val ↔ ∃ i ∈ I,
      z = ZFSet.pair (M.binaryRowName I C one i).val (SetMembers.raw one) := by
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨i, eq⟩
    exact ⟨SetMembers.raw i, SetMembers.raw_mem i, eq.symm⟩
  · rintro ⟨i, hi, eq⟩
    refine ⟨SetMembers.ofMem i hi, ?_⟩
    simpa only [SetMembers.presentation, SetMembers.raw_ofMem] using eq.symm

theorem eval_binaryRowSetName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    letI := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    ∀ H : ConditionFilter (SetMembers
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)), H.mem one →
      Name.eval {p | H.mem p} (M.binaryRowSetName I C one) =
        ZFSet.range (fun i : SetMembers I => M.binaryGenericRow I C H (SetMembers.raw i)) := by
  let := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  intro H hone
  apply ZFSet.ext
  intro x
  rw [binaryRowSetName, Name.mem_eval_assemble, ZFSet.mem_range]
  constructor
  · rintro ⟨i, _, eq⟩
    rw [M.eval_binaryRowName I C one H hone] at eq
    exact ⟨i, eq⟩
  · rintro ⟨i, eq⟩
    exact ⟨i, hone, (M.eval_binaryRowName I C one H hone (SetMembers.raw i)).trans eq⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
