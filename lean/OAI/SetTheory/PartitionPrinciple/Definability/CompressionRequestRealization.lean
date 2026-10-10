import OAI.SetTheory.PartitionPrinciple.Geometry.CompressionExternalTileOverlaps

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps.TileRequests.Family
open Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

theorem generator_root_of_tile (r : R) (j : f.Child r) (x y : A)
    (equal : ((f.tile r).child j).toFun x = (f.tile r).root.toFun y) :
    f.translate a (generator J f.Letters ⟨r, j⟩) ((f.copy a 1).toFun x) =
      (f.copy a 1).toFun y := by
  rw [f.translate_copy, mul_one]
  simpa only [one_mul] using f.transfer_child_root a 1 r j x y equal

theorem generator_root_meet_of_tile (r : R) (j : f.Child r) (x y z : A)
    (equal : (f.tile r).order.meet (((f.tile r).child j).toFun x)
      ((f.tile r).root.toFun y) = (f.tile r).root.toFun z) :
    (f.gluedOrder a).meet
      (f.translate a (generator J f.Letters ⟨r, j⟩) ((f.copy a 1).toFun x))
      ((f.copy a 1).toFun y) = (f.copy a 1).toFun z := by
  rw [f.translate_copy, mul_one]
  simpa only [one_mul] using f.transfer_child_root_meet a 1 r j x y z equal

theorem generator_children_meet_of_tile (r : R) (j k : f.Child r) (x y z : A)
    (equal : (f.tile r).order.meet (((f.tile r).child j).toFun x)
      (((f.tile r).child k).toFun y) = ((f.tile r).child j).toFun z) :
    (f.gluedOrder a).meet
      (f.translate a (generator J f.Letters ⟨r, j⟩) ((f.copy a 1).toFun x))
      (f.translate a (generator J f.Letters ⟨r, k⟩) ((f.copy a 1).toFun y)) =
      f.translate a (generator J f.Letters ⟨r, j⟩) ((f.copy a 1).toFun z) := by
  simp only [f.translate_copy, mul_one]
  simpa only [one_mul] using f.transfer_child_child_meet a 1 r j k x y z equal

theorem generator_fixes_ideal_of_tile (r : R) (j : f.Child r) (W : A)
    (equal : ∀ x, P.le x W → ((f.tile r).child j).toFun x = (f.tile r).root.toFun x)
    (z : f.Node a) (lower : (f.gluedOrder a).le z ((f.copy a 1).toFun W)) :
    f.translate a (generator J f.Letters ⟨r, j⟩) z = z := by
  obtain ⟨x, rfl⟩ := (f.copy a 1).ideal W z lower
  exact f.generator_root_of_tile a r j x x (equal x (((f.copy a 1).le_iff x W).1 lower))

theorem identityCopy_preservesProfiles : PreservesProfiles (f.copy a 1).toMeetEmbedding :=
  (f.copy a 1).preservesProfiles f.top f.greatest

end PartitionPilot.Compression.RecursiveMaps.TileRequests.Family




namespace PartitionPilot.Forcing.GroundCompressionCompletion
open SetRealization Compression Compression.RecursiveMaps Attachment CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))
local notation "U" => completion.algebra.union.fields 0
local notation "P" => completion.algebra.union.meet.toSmallMeetOrder
local notation "family" => completion.externalFamily group oldAction compression
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet

theorem external_separation_fixes (W : SetMembers P0) :
    letI := group.toGroup
    let w : SetMembers U := SetMembers.ofMem (SetMembers.raw W) (compression.subset (SetMembers.raw_mem W))
    ∀ z, ((family).gluedOrder (action)).le z (((family).copy (action) 1).toFun w) →
      (family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inl W), ⟨()⟩⟩) z = z := by
  let := group.toGroup
  dsimp only
  exact (family).generator_fixes_ideal_of_tile (action) (.inr (.inl W)) ⟨()⟩ _
    (fun x lower => TileRequests.Request.separation_agrees _ _ _ x lower)

theorem external_separation_meet (W : SetMembers P0) (x y : SetMembers U)
    (wx : ZFSet.pair (SetMembers.raw W) (SetMembers.raw x) ∈ completion.algebra.union.fields 1)
    (wy : ZFSet.pair (SetMembers.raw W) (SetMembers.raw y) ∈ completion.algebra.union.fields 1) :
    letI := group.toGroup
    ((family).gluedOrder (action)).meet
      ((family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inl W), ⟨()⟩⟩)
        (((family).copy (action) 1).toFun x)) (((family).copy (action) 1).toFun y) =
      ((family).copy (action) 1).toFun
        (SetMembers.ofMem (SetMembers.raw W) (compression.subset (SetMembers.raw_mem W))) := by
  let := group.toGroup
  exact (family).generator_root_meet_of_tile (action) (.inr (.inl W)) ⟨()⟩ x y _
    (BinaryTiles.separation_cross_meet P _ x y
      (by simpa only [MeetOrderCode.toSmallMeetOrder, SetMembers.raw_ofMem] using wx)
      (by simpa only [MeetOrderCode.toSmallMeetOrder, SetMembers.raw_ofMem] using wy))

theorem external_compression_restriction (i : SetMembers I) (x : SetMembers U) :
    letI := group.toGroup
    (family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inl i, ⟨()⟩⟩)
      (((family).copy (action) 1).toFun x) =
        ((family).copy (action) 1).toFun ((completion.externalCopy i).toFun x).val := by
  let := group.toGroup
  exact (family).generator_root_of_tile (action) (.inl i) ⟨()⟩ x _
    (TileRequests.Request.compression_agrees _ _ _ _ x)

theorem external_compression_top (i : SetMembers I) :
    letI := group.toGroup
    (family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inl i, ⟨()⟩⟩)
      (((family).copy (action) 1).toFun (SetMembers.ofMem τ completion.top_mem)) =
        ((family).copy (action) 1).toFun (completion.externalCap i) := by
  let := group.toGroup
  exact (family).generator_root_of_tile (action) (.inl i) ⟨()⟩ _ _
    (BinaryTiles.compression_top P _ _ (family).greatest _)

theorem external_rectangle_roots (z : SetMembers (externalRectangles P0 G r0 μ0 A0))
    (x : SetMembers U) (below : (P).le x (completion.externalRectangle group oldAction compression z).C) :
    letI := group.toGroup
    let r := completion.externalRectangle group oldAction compression z
    (family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inr z), ⟨false⟩⟩)
      (((family).copy (action) 1).toFun x) =
        ((family).copy (action) 1).toFun (((action).iso r.first).toFun x) ∧
    (family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inr z), ⟨true⟩⟩)
      (((family).copy (action) 1).toFun x) =
        ((family).copy (action) 1).toFun (((action).iso r.second).toFun x) := by
  let := group.toGroup
  dsimp only
  let r := (completion.externalRectangle group oldAction compression z).toInput
    (family).top (family).greatest
  exact ⟨(family).generator_root_of_tile (action) (.inr (.inr z)) ⟨false⟩ x _ (r.first_agrees x below),
    (family).generator_root_of_tile (action) (.inr (.inr z)) ⟨true⟩ x _ (r.second_agrees x below)⟩

theorem external_rectangle_children (z : SetMembers (externalRectangles P0 G r0 μ0 A0))
    (x : SetMembers U) (below : (P).le x (completion.externalRectangle group oldAction compression z).B) :
    letI := group.toGroup
    (family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inr z), ⟨false⟩⟩)
      (((family).copy (action) 1).toFun x) =
    (family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inr z), ⟨true⟩⟩)
      (((family).copy (action) 1).toFun x) := by
  let := group.toGroup
  let r := (completion.externalRectangle group oldAction compression z).toInput
    (family).top (family).greatest
  simp only [TileRequests.Family.translate_copy, mul_one]
  have equal := congrArg ((family).placedTile (action) 1 (.inr (.inr z))).toFun
    ((r.children_intersection x x).2 ⟨below, rfl⟩)
  change ((family).placedTile (action) 1 (.inr (.inr z))).toFun
    ((((family).tile (.inr (.inr z))).child ⟨false⟩).toFun x) =
      ((family).placedTile (action) 1 (.inr (.inr z))).toFun
        ((((family).tile (.inr (.inr z))).child ⟨true⟩).toFun x) at equal
  simpa only [one_mul] using
    ((family).child_identification (action) 1 (.inr (.inr z)) ⟨false⟩ x).symm.trans
      (equal.trans ((family).child_identification (action) 1 (.inr (.inr z)) ⟨true⟩ x))

theorem external_rectangle_root_meets (z : SetMembers (externalRectangles P0 G r0 μ0 A0))
    (x : SetMembers U) :
    letI := group.toGroup
    let r := completion.externalRectangle group oldAction compression z
    ((family).gluedOrder (action)).meet
      ((family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inr z), ⟨false⟩⟩)
        (((family).copy (action) 1).toFun r.D)) (((family).copy (action) 1).toFun x) =
      ((family).copy (action) 1).toFun ((P).meet (((action).iso r.first).toFun r.C) x) ∧
    ((family).gluedOrder (action)).meet
      ((family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inr z), ⟨true⟩⟩)
        (((family).copy (action) 1).toFun r.D)) (((family).copy (action) 1).toFun x) =
      ((family).copy (action) 1).toFun ((P).meet (((action).iso r.second).toFun r.C) x) := by
  let := group.toGroup
  dsimp only
  let r := (completion.externalRectangle group oldAction compression z).toInput
    (family).top (family).greatest
  exact ⟨(family).generator_root_meet_of_tile (action) (.inr (.inr z)) ⟨false⟩ r.D x _ (r.first_meet_root x),
    (family).generator_root_meet_of_tile (action) (.inr (.inr z)) ⟨true⟩ r.D x _ (r.second_meet_root x)⟩

theorem external_rectangle_children_meet (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) :
    letI := group.toGroup
    let r := completion.externalRectangle group oldAction compression z
    ((family).gluedOrder (action)).meet
      ((family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inr z), ⟨false⟩⟩)
        (((family).copy (action) 1).toFun r.D))
      ((family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inr z), ⟨true⟩⟩)
        (((family).copy (action) 1).toFun r.D)) =
    (family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inr z), ⟨false⟩⟩)
      (((family).copy (action) 1).toFun r.B) := by
  let := group.toGroup
  dsimp only
  let r := (completion.externalRectangle group oldAction compression z).toInput
    (family).top (family).greatest
  exact (family).generator_children_meet_of_tile (action) (.inr (.inr z)) ⟨false⟩ ⟨true⟩ r.D r.D r.B r.children_meet

end PartitionPilot.Forcing.GroundCompressionCompletion

end OAI
