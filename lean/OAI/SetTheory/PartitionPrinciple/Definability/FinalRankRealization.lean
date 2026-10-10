import OAI.SetTheory.PartitionPrinciple.Geometry.GroundGeometry

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

open Cardinal CountableColumns SetRealization
open scoped Cardinal

noncomputable def finalSetPresentation (Label : Type 1) :
    GeometryPresentation (FinalPoint Label) (FinalActor Label) :=
  ⟨Presentation.canonical (FinalPoint Label), Presentation.canonical (FinalActor Label)⟩

theorem finalSetPresentation_points_rank (Label : Type 1) :
    ZFSet.rank (finalSetPresentation Label).points.carrier = (#(FinalPoint Label)).ord :=
  Presentation.rank_canonical _

theorem finalSetPresentation_actors_rank (Label : Type 1) :
    ZFSet.rank (finalSetPresentation Label).actors.carrier = (#(FinalActor Label)).ord :=
  Presentation.rank_canonical _

theorem finalSetPresentation_rank_bounds (Label : Type 1) (κ : Cardinal.{1})
    (inaccessible : κ.IsInaccessible) (labels : #Label < κ) :
    (finalSetPresentation Label).RankBounds (finalOrder Label) (finalAction Label)
      (finalBottom Label) κ.ord := by
  have small := final_cardinal_bounds Label κ inaccessible labels
  exact (finalSetPresentation Label).rank_bounds (finalOrder Label) (finalAction Label)
    (finalBottom Label) (Cardinal.isSuccLimit_ord inaccessible.1.le)
    (Presentation.canonical_rank_lt _ κ small.1) (Presentation.canonical_rank_lt _ κ small.2)

theorem countableOrdinalLabels_rank_bounds (κ : Cardinal.{1}) (inaccessible : κ.IsInaccessible) :
    (finalSetPresentation Column).RankBounds (finalOrder Column) (finalAction Column)
      (finalBottom Column) κ.ord :=
  finalSetPresentation_rank_bounds Column κ inaccessible (cardinal_lt_inaccessible κ inaccessible)

theorem countableOrdinalLabels_ground_rank_realization
    (κ : Cardinal.{1}) (inaccessible : κ.IsInaccessible) :
    ∃ s : GeometryPresentation (FinalPoint Column) (FinalActor Column),
      GroundGeometryLaws (finalOrder Column) (finalAction Column) κ ∧
      s.RankBounds (finalOrder Column) (finalAction Column) (finalBottom Column) κ.ord :=
  ⟨finalSetPresentation Column, countableOrdinalLabels_ground_geometry κ inaccessible,
    countableOrdinalLabels_rank_bounds κ inaccessible⟩

end PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

end

end OAI
