import OAI.SetTheory.PartitionPrinciple.Geometry.GroundBinaryRows

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization
universe u
variable (M : TransitiveGround.{u})

noncomputable def binaryRowName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (i : ZFSet.{u}) :
    Name (SetMembers.presentation (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :=
  Name.assemble
    (fun z : {z : SetMembers C × SetMembers
        (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega) //
        ZFSet.pair (ZFSet.pair i (SetMembers.raw z.1)) (natSetCode 1) ∈ SetMembers.raw z.2} =>
      Name.check (SetMembers.presentation
        (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) one (SetMembers.raw z.val.1))
    (fun z => z.val.2)

theorem entry_binaryRowName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (i : ZFSet.{u})
    (σ : Name (SetMembers.presentation
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)))
    (p : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    Name.Entry σ (M.binaryRowName I C one i) p ↔ ∃ c ∈ C,
      Name.check (SetMembers.presentation
        (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) one c = σ ∧
      ZFSet.pair (ZFSet.pair i c) (natSetCode 1) ∈ SetMembers.raw p := by
  rw [binaryRowName, Name.entry_assemble]
  constructor
  · rintro ⟨z, eq, rfl⟩
    exact ⟨SetMembers.raw z.val.1, SetMembers.raw_mem z.val.1, eq, z.property⟩
  · rintro ⟨c, hc, eq, assigned⟩
    refine ⟨⟨(SetMembers.ofMem c hc, p), ?_⟩, ?_, rfl⟩
    · simpa only [SetMembers.raw_ofMem] using assigned
    · simpa only [SetMembers.raw_ofMem] using eq

theorem mem_binaryRowName_code (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (i z : ZFSet.{u}) :
    z ∈ (M.binaryRowName I C one i).val ↔ ∃ c ∈ C,
      ∃ p ∈ M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega,
        z = ZFSet.pair (Name.check (SetMembers.presentation
          (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) one c).val p ∧
        ZFSet.pair (ZFSet.pair i c) (natSetCode 1) ∈ p := by
  constructor
  · intro hz
    obtain ⟨σ, p, eq⟩ := Name.entries_cover (M.binaryRowName I C one i) hz
    change z = ZFSet.pair σ.val (SetMembers.raw p) at eq
    have entry : Name.Entry σ (M.binaryRowName I C one i) p := by
      change ZFSet.pair σ.val (SetMembers.raw p) ∈ (M.binaryRowName I C one i).val
      rw [← eq]
      exact hz
    obtain ⟨c, hc, child, assigned⟩ := (M.entry_binaryRowName I C one i σ p).1 entry
    refine ⟨c, hc, SetMembers.raw p, SetMembers.raw_mem p, ?_, assigned⟩
    rw [child]
    exact eq
  · rintro ⟨c, hc, p, hp, eq, assigned⟩
    have entry := (M.entry_binaryRowName I C one i _ (SetMembers.ofMem p hp)).2
      ⟨c, hc, rfl, by simpa only [SetMembers.raw_ofMem] using assigned⟩
    change ZFSet.pair (Name.check (SetMembers.presentation
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) one c).val
        (SetMembers.raw (SetMembers.ofMem p hp)) ∈ (M.binaryRowName I C one i).val at entry
    rw [SetMembers.raw_ofMem] at entry
    exact eq.symm ▸ entry

theorem mem_eval_binaryRowName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (H : Set (SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)))
    (hone : one ∈ H) (i x : ZFSet.{u}) :
    x ∈ Name.eval H (M.binaryRowName I C one i) ↔ x ∈ C ∧
      ∃ p, p ∈ H ∧ ZFSet.pair (ZFSet.pair i x) (natSetCode 1) ∈ SetMembers.raw p := by
  rw [Name.mem_eval]
  constructor
  · rintro ⟨σ, p, entry, hp, eq⟩
    obtain ⟨c, hc, rfl, assigned⟩ := (M.entry_binaryRowName I C one i σ p).1 entry
    rw [Name.eval_check H one hone] at eq
    exact ⟨eq ▸ hc, p, hp, eq ▸ assigned⟩
  · rintro ⟨hx, p, hp, assigned⟩
    exact ⟨Name.check (SetMembers.presentation
        (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) one x, p,
      (M.entry_binaryRowName I C one i _ p).2 ⟨x, hx, rfl, assigned⟩,
      hp, Name.eval_check H one hone x⟩

theorem eval_binaryRowName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    letI := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    ∀ H : ConditionFilter (SetMembers
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)),
      H.mem one → ∀ i : ZFSet.{u},
      Name.eval {p | H.mem p} (M.binaryRowName I C one i) = M.binaryGenericRow I C H i := by
  let := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  intro H hone i
  apply ZFSet.ext
  intro x
  rw [M.mem_eval_binaryRowName I C one {p | H.mem p} hone i x,
    M.mem_binaryGenericRow I C H i x,
    M.mem_countableGenericGraph (ZFSet.prod I C) (natSetCode 2) H]
  rfl

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
