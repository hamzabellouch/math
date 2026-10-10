import OAI.SetTheory.PartitionPrinciple.Geometry.CompressionExternalTileOverlaps
import OAI.SetTheory.PartitionPrinciple.Geometry.RequestedOwnerSlotLaws

namespace OAI

section

namespace PartitionPilot.Forcing.GroundCompressionCompletion
open SetRealization Compression.RecursiveMaps.TileRequests
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))

theorem externalFamilyVertexCode_eq_slot
    (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0))
    (i : Option ((completion.externalFamily group oldAction compression).Child r)) :
    completion.externalFamilyVertexCode group oldAction compression r i =
      natSetCode (((completion.externalFamily group oldAction compression).request r).vertexSlot i) := by
  cases r with
  | inl r => cases i <;> rfl
  | inr r =>
    cases r with
    | inl r => cases i <;> rfl
    | inr r =>
      cases i with
      | none => rfl
      | some b => cases b with | up b => cases b <;> rfl

end PartitionPilot.Forcing.GroundCompressionCompletion

end

end OAI
