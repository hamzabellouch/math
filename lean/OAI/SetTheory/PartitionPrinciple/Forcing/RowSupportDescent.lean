import OAI.SetTheory.PartitionPrinciple.Geometry.RowCopyRefinements

namespace OAI

section

namespace PartitionPilot.Forcing.Rows

open Compression.RecursiveMaps Compression.RecursiveMaps.CountableColumns
open Compression.RecursiveMaps.MainStage.OrdinalRun

def descentWitnessFamily (p : RowForcing) (C B D : FinalPoint Column)
    (x y : Name namePresentation) : Set (Set RowForcing) :=
  posetAction.copyWitnessFamily namePresentation
    ((finalAction Column).fixSubgroup ((finalOrder Column).meet C B))
    (Separated D ((finalOrder Column).meet C B)) p x y

theorem row_mix_capture (p : RowForcing) (C B D : FinalPoint Column)
    (x y : Name namePresentation) (bp : Bounds p D)
    (cd : (finalOrder Column).le C D) (bd : (finalOrder Column).le B D)
    (sx : (finalAction Column).fixSubgroup C ≤ posetAction.stabilizer namePresentation x)
    (sy : (finalAction Column).fixSubgroup B ≤ posetAction.stabilizer namePresentation y)
    (H : ConditionFilter RowForcing) (generic : H.GenericFor (descentWitnessFamily p C B D x y))
    (hp : H.mem p)
    (xy : ∀ g, H.mem (rowAction g p) →
      Name.eval {q | H.mem q} (posetAction.act namePresentation g x) =
      Name.eval {q | H.mem q} (posetAction.act namePresentation g y)) :
    Name.eval {q | H.mem q} (posetAction.mix namePresentation
      ((finalAction Column).fixSubgroup ((finalOrder Column).meet C B)) p x) =
      Name.eval {q | H.mem q} x := by
  apply posetAction.mix_capture_from_refinements namePresentation
    ((finalAction Column).fixSubgroup ((finalOrder Column).meet C B))
    (Separated D ((finalOrder Column).meet C B)) p x y H generic hp xy
  · exact rectangle_refinement p C B D x y bp cd bd sx sy
  · intro g₁ hg₁ g₂ hg₂ r ref₁ _
    exact separation_refinement p ((finalOrder Column).meet C B) D bp
      ((finalOrder Column).trans ((finalOrder Column).meet_le_left C B) cd)
      g₁ hg₁ g₂ hg₂ r ref₁

theorem row_common_support (p : RowForcing) (C B D : FinalPoint Column)
    (x y : Name namePresentation) (bp : Bounds p D)
    (cd : (finalOrder Column).le C D) (bd : (finalOrder Column).le B D)
    (sx : (finalAction Column).fixSubgroup C ≤ posetAction.stabilizer namePresentation x)
    (sy : (finalAction Column).fixSubgroup B ≤ posetAction.stabilizer namePresentation y)
    (hs : HereditarilySymmetric posetAction namePresentation (supportFamily Column) x)
    (H : ConditionFilter RowForcing) (generic : H.GenericFor (descentWitnessFamily p C B D x y))
    (hp : H.mem p)
    (xy : ∀ g, H.mem (rowAction g p) →
      Name.eval {q | H.mem q} (posetAction.act namePresentation g x) =
      Name.eval {q | H.mem q} (posetAction.act namePresentation g y)) :
    ∃ z : Name namePresentation,
      HereditarilySymmetric posetAction namePresentation (supportFamily Column) z ∧
      (finalAction Column).fixSubgroup ((finalOrder Column).meet C B) ≤
        posetAction.stabilizer namePresentation z ∧
      Name.nameRank z ≤ Name.nameRank x ∧
      Name.eval {q | H.mem q} z = Name.eval {q | H.mem q} x := by
  let K := (finalAction Column).fixSubgroup ((finalOrder Column).meet C B)
  refine ⟨posetAction.mix namePresentation K p x,
    posetAction.mix_hs namePresentation (supportFamily Column) K
      ⟨(finalOrder Column).meet C B, le_rfl⟩ p hs, ?_,
    posetAction.nameRank_mix_le namePresentation K p x, ?_⟩
  · intro g hg
    exact posetAction.mix_fixed namePresentation K p x hg
  · exact row_mix_capture p C B D x y bp cd bd sx sy H generic hp xy

end PartitionPilot.Forcing.Rows

end

end OAI
