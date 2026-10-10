import OAI.SetTheory.PartitionPrinciple.Forcing.OrbitPairGraphNames

namespace OAI

section

namespace PartitionPilot.Forcing.Rows

open SetRealization Compression.RecursiveMaps
open Compression.RecursiveMaps.CountableColumns Compression.RecursiveMaps.MainStage.OrdinalRun

noncomputable def namePresentation : Presentation RowForcing := Presentation.canonical RowForcing

noncomputable def posetAction : PosetAction (FinalActor Column) RowForcing where
  iso := rowAction
  one := rowAction_one
  mul := rowAction_mul

noncomputable def columnCode (α : Column) : ZFSet.{1} := ordinalCode (Ordinal.lift.{1,0} α.val)

theorem columnCode_injective : Function.Injective columnCode := by
  intro α β eq
  exact Subtype.ext (Ordinal.lift_inj.1 (ordinalCode_injective eq))

noncomputable def rowName (i : Position) : Name namePresentation :=
  Name.assemble
    (fun c : {c : Column × RowForcing // c.2.value (i, c.1) = some true} =>
      Name.check namePresentation ⊤ (columnCode c.val.1))
    (fun c => c.val.2)

theorem entry_rowName (i : Position) (σ : Name namePresentation) (p : RowForcing) :
    Name.Entry σ (rowName i) p ↔ ∃ α,
      Name.check namePresentation ⊤ (columnCode α) = σ ∧ p.value (i, α) = some true := by
  rw [rowName, Name.entry_assemble]
  constructor
  · rintro ⟨c, eq, rfl⟩
    exact ⟨c.val.1, eq, c.property⟩
  · rintro ⟨α, eq, hp⟩
    exact ⟨⟨(α, p), hp⟩, eq, rfl⟩

theorem rowName_action (g : FinalActor Column) (i : Position) :
    posetAction.act namePresentation g (rowName i) = rowName (positionAction g i) := by
  apply Name.ext
  intro σ q
  change Name.Entry σ (Name.rename namePresentation (rowAction g) (rowName i)) q ↔ _
  rw [Name.entry_rename, entry_rowName]
  constructor
  · rintro ⟨ν, p, entry, eq, rfl⟩
    obtain ⟨α, rfl, hp⟩ := (entry_rowName i ν p).1 entry
    refine ⟨α, ?_, (rowAction_value g p i α).trans hp⟩
    exact (posetAction.act_check namePresentation g (columnCode α)).symm.trans eq
  · rintro ⟨α, rfl, hq⟩
    let p := (rowAction g).symm q
    have pq : rowAction g p = q := (rowAction g).apply_symm_apply q
    have hp : p.value (i, α) = some true := by
      have hv := rowAction_value g p i α
      rw [pq] at hv
      exact hv.symm.trans hq
    exact ⟨Name.check namePresentation ⊤ (columnCode α), p,
      (entry_rowName i _ p).2 ⟨α, rfl, hp⟩,
      posetAction.act_check namePresentation g (columnCode α), pq⟩

theorem rowName_supported (i : Position) :
    (finalAction Column).fixSubgroup i.val ≤ posetAction.stabilizer namePresentation (rowName i) := by
  intro g fixed
  change posetAction.act namePresentation g (rowName i) = rowName i
  rw [rowName_action]
  apply congrArg rowName
  exact Subtype.ext (fixed i.val ((finalOrder Column).refl i.val))

theorem rowName_hs (i : Position) :
    HereditarilySymmetric posetAction namePresentation (supportFamily Column) (rowName i) := by
  refine HereditarilySymmetric.mk ⟨i.val, rowName_supported i⟩ ?_
  intro σ p entry
  obtain ⟨α, rfl, _⟩ := (entry_rowName i σ p).1 entry
  exact HereditarilySymmetric.check posetAction namePresentation (supportFamily Column) (columnCode α)

theorem mem_eval_rowName (H : Set RowForcing) (top : ⊤ ∈ H) (i : Position) (x : ZFSet.{1}) :
    x ∈ Name.eval H (rowName i) ↔
      ∃ α p, p ∈ H ∧ p.value (i, α) = some true ∧ columnCode α = x := by
  rw [Name.mem_eval]
  constructor
  · rintro ⟨σ, p, entry, hp, eq⟩
    obtain ⟨α, rfl, value⟩ := (entry_rowName i σ p).1 entry
    rw [Name.eval_check H ⊤ top] at eq
    exact ⟨α, p, hp, value, eq⟩
  · rintro ⟨α, p, hp, value, eq⟩
    exact ⟨Name.check namePresentation ⊤ (columnCode α), p,
      (entry_rowName i _ p).2 ⟨α, rfl, value⟩, hp,
      (Name.eval_check H ⊤ top (columnCode α)).trans eq⟩

theorem column_mem_eval_rowName (F : ConditionFilter RowForcing) (i : Position) (α : Column) :
    columnCode α ∈ Name.eval {p | F.mem p} (rowName i) ↔
      ∃ p, F.mem p ∧ p.value (i, α) = some true := by
  rw [mem_eval_rowName {p | F.mem p} F.top_mem]
  constructor
  · rintro ⟨β, p, hp, value, eq⟩
    have same := columnCode_injective eq
    exact ⟨p, hp, same ▸ value⟩
  · rintro ⟨p, hp, value⟩
    exact ⟨α, p, hp, value, rfl⟩

theorem rowName_recovers_row (F : ConditionFilter RowForcing)
    (generic : F.GenericFor (denseFamily Position)) (i : Position) (α : Column) :
    columnCode α ∈ Name.eval {p | F.mem p} (rowName i) ↔ α ∈ row F generic i := by
  rw [column_mem_eval_rowName, mem_row_iff]

theorem rowName_values_injective (F : ConditionFilter RowForcing)
    (generic : F.GenericFor (denseFamily Position)) :
    Function.Injective (fun i => Name.eval {p | F.mem p} (rowName i)) := by
  intro i j eq
  change Name.eval {p | F.mem p} (rowName i) = Name.eval {p | F.mem p} (rowName j) at eq
  apply row_injective F generic
  apply Set.ext
  intro α
  rw [← rowName_recovers_row F generic, ← rowName_recovers_row F generic, eq]

end PartitionPilot.Forcing.Rows

end

end OAI
