import OAI.SetTheory.PartitionPrinciple.Transfinite.ExternalChronologyStageLaws

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem heightOrderRestriction_restrict {Q L r : ZFSet.{u}} (subset : Q ⊆ L) :
    heightOrderRestriction Q (heightOrderRestriction L r) = heightOrderRestriction Q r := by
  apply ZFSet.ext
  intro z
  simp only [heightOrderRestriction, ZFSet.mem_sep]
  constructor
  · rintro ⟨⟨entry, _⟩, small⟩
    exact ⟨entry, small⟩
  · rintro ⟨entry, small⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 small
    exact ⟨⟨entry, ZFSet.pair_mem_prod.2 ⟨subset hx, subset hy⟩⟩,
      ZFSet.pair_mem_prod.2 ⟨hx, hy⟩⟩

namespace GroundExternalBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "r" => completion.externalPointOrder P0 r0 μ0 A0
local notation "μ" => completion.externalPointMeet P0 r0 μ0 A0

theorem cutoff_order_restriction {n k : Nat} (before : n ≤ k) :
    heightOrderRestriction (births.cutoff n) (births.cutoffOrder k) = births.cutoffOrder n :=
  heightOrderRestriction_restrict (births.cutoff_mono before)

theorem cutoff_meet_restriction {n k : Nat} (before : n ≤ k) :
    graphRestriction (ZFSet.prod (births.cutoff n) (births.cutoff n)) (births.cutoffMeet k) =
      births.cutoffMeet n := by
  apply graphRestriction_restrict
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
  exact ZFSet.pair_mem_prod.2 ⟨births.cutoff_mono before hx, births.cutoff_mono before hy⟩

theorem cutoff_birth_restriction {n k : Nat} (before : n ≤ k) :
    graphRestriction (births.cutoff n) (births.cutoffBirth k) = births.cutoffBirth n :=
  graphRestriction_restrict (births.cutoff_mono before)

theorem cutoff_height_restriction (height : ZFSet.{u}) {n k : Nat} (before : n ≤ k) :
    graphRestriction (births.cutoff n) (births.cutoffHeight height k) = births.cutoffHeight height n :=
  graphRestriction_restrict (births.cutoff_mono before)

variable {inv : ZFSet.{u}}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
include data group oldAction pairing unions powers separation infinite hG hP0

theorem pair_mem_order_iff_cutoff (x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ r ↔ ∃ n : Nat, ZFSet.pair x y ∈ births.cutoffOrder n := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have levels := (data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
  constructor
  · intro entry
    have bounds := ZFSet.pair_mem_prod.1 (geometry.meet.order.relation entry)
    obtain ⟨n, hx⟩ := (births.cutoff_union levels x).1 bounds.1
    obtain ⟨k, hy⟩ := (births.cutoff_union levels y).1 bounds.2
    exact ⟨max n k, (pair_mem_heightOrderRestriction _ _ _ _).2
      ⟨entry, births.cutoff_mono (le_max_left n k) hx, births.cutoff_mono (le_max_right n k) hy⟩⟩
  · rintro ⟨n, entry⟩
    exact ((pair_mem_heightOrderRestriction _ _ _ _).1 entry).1

theorem pair_mem_meet_iff_cutoff (x y z : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair x y) z ∈ μ ↔
      ∃ n : Nat, ZFSet.pair (ZFSet.pair x y) z ∈ births.cutoffMeet n := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have levels := (data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
  constructor
  · intro entry
    have bounds := ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 (geometry.meet.operation.1 entry)).1
    obtain ⟨n, hx⟩ := (births.cutoff_union levels x).1 bounds.1
    obtain ⟨k, hy⟩ := (births.cutoff_union levels y).1 bounds.2
    exact ⟨max n k, pair_mem_graphRestriction.2 ⟨entry,
      ZFSet.pair_mem_prod.2 ⟨births.cutoff_mono (le_max_left n k) hx,
        births.cutoff_mono (le_max_right n k) hy⟩⟩⟩
  · rintro ⟨n, entry⟩
    exact (pair_mem_graphRestriction.1 entry).1

theorem pair_mem_birth_iff_cutoff (x t : ZFSet.{u}) :
    ZFSet.pair x t ∈ births.birth ↔ ∃ n : Nat, ZFSet.pair x t ∈ births.cutoffBirth n := by
  have levels := (data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
  constructor
  · intro entry
    obtain ⟨n, hx⟩ := (births.cutoff_union levels x).1 (ZFSet.pair_mem_prod.1 (births.function.1 entry)).1
    exact ⟨n, pair_mem_graphRestriction.2 ⟨entry, hx⟩⟩
  · rintro ⟨n, entry⟩
    exact (pair_mem_graphRestriction.1 entry).1

theorem pair_mem_height_iff_cutoff {C D rD lo hi seed : ZFSet.{u}}
    (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 C D rD lo hi seed completion) (x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ heights.height ↔
      ∃ n : Nat, ZFSet.pair x y ∈ births.cutoffHeight heights.height n := by
  have levels := (data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
  constructor
  · intro entry
    obtain ⟨n, hx⟩ := (births.cutoff_union levels x).1 (ZFSet.pair_mem_prod.1 (heights.code.function.1 entry)).1
    exact ⟨n, pair_mem_graphRestriction.2 ⟨entry, hx⟩⟩
  · rintro ⟨n, entry⟩
    exact (pair_mem_graphRestriction.1 entry).1

end GroundExternalBirthData

end PartitionPilot.Forcing

end

end OAI
