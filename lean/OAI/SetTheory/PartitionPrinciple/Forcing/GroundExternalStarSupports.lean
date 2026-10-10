import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalLocalHeightSelection

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (P r μ A : ZFSet.{u})
local notation "letters" => externalChildLetters I P (externalRectangles P G r μ A)
local notation "requests" => externalRequestCarrier I P (externalRectangles P G r μ A)
local notation "Q" => completion.externalPointCarrier P r μ A
local notation "vertices" => M.externalStarVertices G letters requests m one

noncomputable def externalStarSupports : ZFSet.{u} :=
  externalStarSupportGraph vertices Q (M.externalGroupCarrier G letters m one)
    (completion.algebra.union.fields 0) (M.externalCosetCarrier G letters m one) requests
    (M.externalCosetClassifier G letters m one) (completion.externalPointClassifier P r μ A)
    (completion.localTilePoints P r μ A) (completion.externalPointAction P r μ A)
    (natSetCode 0) (natSetCode 1)

noncomputable def externalStarSupport (v : ZFSet.{u}) : ZFSet.{u} :=
  relationFiber Q (completion.externalStarSupports P r μ A) v

noncomputable def externalStarSupportFamily : ZFSet.{u} :=
  M.relationFiberFamily vertices Q (completion.externalStarSupports P r μ A)

theorem externalStarSupport_subset (v : ZFSet.{u}) : completion.externalStarSupport P r μ A v ⊆ Q :=
  fun _ hz => ((mem_relationFiber _ _ _ _).1 hz).1

end GroundCompressionCompletion

namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "vertices" => M.externalStarVertices G letters requests m one
include data group oldAction pairing unions powers separation infinite hG hP0

theorem externalStarSupports_ground : completion.externalStarSupports P0 r0 μ0 A0 ∈ M.sets := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have cosets := data.externalCosets_ground pairing unions powers separation hG
  exact M.externalStarSupportGraph_mem pairing unions powers separation
    (data.externalStarCarriers_ground pairing unions powers separation hG).1 geometry.carrier_ground
    data.group.carrier_mem (completion.algebra.union.ground 0) cosets.2.1 data.words.requests_ground
    cosets.2.2 geometry.classifier_ground
    (data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0).2.2.2.2
    geometry.action_ground (M.natSetCode_mem separation infinite 0) (M.natSetCode_mem separation infinite 1)

theorem externalStarSupportFamily_spec :
    completion.externalStarSupportFamily P0 r0 μ0 A0 ∈ M.sets ∧
      ZFSet.IsFunc vertices (M.groundPower Q) (completion.externalStarSupportFamily P0 r0 μ0 A0) ∧
      ∀ v f, ZFSet.pair v f ∈ completion.externalStarSupportFamily P0 r0 μ0 A0 ↔
        v ∈ vertices ∧ f = completion.externalStarSupport P0 r0 μ0 A0 v := by
  have hv := (data.externalStarCarriers_ground pairing unions powers separation hG).1
  have hq := (data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0).1
  have hs := data.externalStarSupports_ground group oldAction pairing unions powers separation infinite hG hP0
  exact ⟨M.relationFiberFamily_mem pairing unions powers separation hv hq hs,
    M.relationFiberFamily_function separation hv hq hs,
    M.relationFiberFamily_entries separation hv hq hs⟩

end GroundExternalGeometryInputs
end PartitionPilot.Forcing

end

end OAI
