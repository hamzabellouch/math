import OAI.SetTheory.PartitionPrinciple.Forcing.RowSupportDescent

namespace OAI

section

namespace PartitionPilot.Forcing.Rows

open Compression.RecursiveMaps Compression.RecursiveMaps.CountableColumns
open Compression.RecursiveMaps.MainStage.OrdinalRun

def rowAtomicFamily (N : Name.NameDomain namePresentation) : Set (Set RowForcing) :=
  Name.atomicFamily N ∪ {E | ∃ p C B D x y, x ∈ N.names ∧ y ∈ N.names ∧
    E ∈ descentWitnessFamily p C B D x y}

theorem translated_eval_eq_of_forcesEq (N : Name.NameDomain namePresentation)
    (translated : ∀ g τ, τ ∈ N.names → posetAction.act namePresentation g τ ∈ N.names)
    (H : ConditionFilter RowForcing) (generic : H.GenericFor (Name.atomicFamily N))
    {x y : Name namePresentation} (hx : x ∈ N.names) (hy : y ∈ N.names)
    {p : RowForcing} (eq : Name.ForcesEq p x y) :
    ∀ g, H.mem (rowAction g p) →
      Name.eval {q | H.mem q} (posetAction.act namePresentation g x) =
      Name.eval {q | H.mem q} (posetAction.act namePresentation g y) := by
  intro g active
  exact Name.forcesEq_sound N H generic _ (translated g x hx) _ (translated g y hy)
    _ active (posetAction.forcesEq_act namePresentation g eq)

theorem row_common_support_of_eval_eq (N : Name.NameDomain namePresentation)
    (translated : ∀ g τ, τ ∈ N.names → posetAction.act namePresentation g τ ∈ N.names)
    (mixed : ∀ W p τ, τ ∈ N.names → posetAction.mix namePresentation
      ((finalAction Column).fixSubgroup W) p τ ∈ N.names)
    (H : ConditionFilter RowForcing) (generic : H.GenericFor (rowAtomicFamily N))
    (C B : FinalPoint Column) (x y : Name namePresentation)
    (hx : x ∈ N.names) (hy : y ∈ N.names)
    (sx : (finalAction Column).fixSubgroup C ≤ posetAction.stabilizer namePresentation x)
    (sy : (finalAction Column).fixSubgroup B ≤ posetAction.stabilizer namePresentation y)
    (hs : HereditarilySymmetric posetAction namePresentation (supportFamily Column) x)
    (values : Name.eval {q | H.mem q} x = Name.eval {q | H.mem q} y) :
    ∃ z ∈ N.names,
      HereditarilySymmetric posetAction namePresentation (supportFamily Column) z ∧
      (finalAction Column).fixSubgroup ((finalOrder Column).meet C B) ≤
        posetAction.stabilizer namePresentation z ∧
      Name.nameRank z ≤ Name.nameRank x ∧
      Name.eval {q | H.mem q} z = Name.eval {q | H.mem q} x := by
  have atoms : H.GenericFor (Name.atomicFamily N) :=
    fun E hE dense => generic E (Or.inl hE) dense
  obtain ⟨p, hp, eq⟩ := (Name.eval_eq_iff_forcesEq N H atoms hx hy).1 values
  obtain ⟨D, bp, upper⟩ := bounds_with p {C, B} ((Set.countable_singleton B).insert C)
  have cd := upper C (by simp)
  have bd := upper B (by simp)
  have copies : H.GenericFor (descentWitnessFamily p C B D x y) :=
    fun E hE dense => generic E (Or.inr ⟨p, C, B, D, x, y, hx, hy, hE⟩) dense
  let W := (finalOrder Column).meet C B
  let K := (finalAction Column).fixSubgroup W
  refine ⟨posetAction.mix namePresentation K p x, mixed W p x hx,
    posetAction.mix_hs namePresentation (supportFamily Column) K ⟨W, le_rfl⟩ p hs,
    ?_, posetAction.nameRank_mix_le namePresentation K p x, ?_⟩
  · intro g hg
    exact posetAction.mix_fixed namePresentation K p x hg
  · exact row_mix_capture p C B D x y bp cd bd sx sy H copies hp
      (translated_eval_eq_of_forcesEq N translated H atoms hx hy eq)

end PartitionPilot.Forcing.Rows

end

end OAI
