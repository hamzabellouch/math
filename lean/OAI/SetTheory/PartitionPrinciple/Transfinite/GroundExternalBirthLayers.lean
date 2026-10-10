import OAI.SetTheory.PartitionPrinciple.Definability.ExternalFamilySlotCodes
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundPreparationFamilyImages

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem pushedBirthGraph_oldMeet {A B T rA rB μA μB e old : ZFSet.{u}}
    (source : MeetOrderCode A rA μA) (target : MeetOrderCode B rB μB)
    (embedding : MeetEmbeddingCode A B rA rB μA μB e)
    (born : ZFSet.IsFunc A T old) (oldMeet : OldMeetCode rA μA old) :
    OldMeetCode rB μB (pushedHeightGraph A B T e old) := by
  intro x y z a b c bornY bornX earlier notLower meetXY bornZ
  have function := pushedHeightGraph_function embedding.injection born
  have hx := (ZFSet.pair_mem_prod.1 (function.1 bornX)).1
  have hy := (ZFSet.pair_mem_prod.1 (function.1 bornY)).1
  obtain ⟨_, x0, hx0, copyX⟩ := (mem_relationImage _ _ _ _).1 hx
  obtain ⟨_, y0, hy0, copyY⟩ := (mem_relationImage _ _ _ _).1 hy
  obtain ⟨z0, sourceMeet, _⟩ := source.operation.2 (ZFSet.pair x0 y0) (ZFSet.pair_mem_prod.2 ⟨hx0, hy0⟩)
  have hz0 := (ZFSet.pair_mem_prod.1 (source.operation.1 sourceMeet)).2
  obtain ⟨z1, copyZ, _⟩ := embedding.injection.function.2 z0 hz0
  have targetMeet := embedding.map_meet x0 y0 z0 x y z1 sourceMeet copyX copyY copyZ
  obtain ⟨_, _, unique⟩ := target.operation.2 (ZFSet.pair x y)
    (ZFSet.pair_mem_prod.1 (target.operation.1 meetXY)).1
  have equal := (unique z1 targetMeet).trans (unique z meetXY).symm
  subst z1
  exact oldMeet x0 y0 z0 a b c
    ((pushedHeightGraph_entry embedding.injection born copyY).1 bornY)
    ((pushedHeightGraph_entry embedding.injection born copyX).1 bornX) earlier
    (fun lower => notLower (embedding.monotone x0 y0 x y lower copyX copyY)) sourceMeet
    ((pushedHeightGraph_entry embedding.injection born copyZ).1 bornZ)

end PartitionPilot.Forcing


section

namespace PartitionPilot.Forcing.GroundCompressionCompletion
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
noncomputable def externalSeedBirth (P r μ A times birth : ZFSet.{u}) : ZFSet.{u} :=
  pushedHeightGraph (completion.algebra.union.fields 0) (completion.externalPointCarrier P r μ A)
    times (completion.externalIdentityCopyGraph P r μ A) birth

end PartitionPilot.Forcing.GroundCompressionCompletion

namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 times birth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "old" => completion.externalSeedBirth P0 r0 μ0 A0 times birth
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG

theorem externalSeedBirth_spec (hP0 : P0 ∈ M.sets) (hTimes : times ∈ M.sets) (hBirth : birth ∈ M.sets)
    (born : ZFSet.IsFunc (completion.algebra.union.fields 0) times birth)
    (oldMeet : OldMeetCode (completion.algebra.union.fields 1) (completion.algebra.union.fields 2) birth) :
    old ∈ M.sets ∧ ZFSet.IsFunc P times old ∧
      OldMeetCode (completion.externalPointOrder P0 r0 μ0 A0) (completion.externalPointMeet P0 r0 μ0 A0) old := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have embedding := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  exact ⟨M.pushedHeightGraph_mem pairing unions powers separation (completion.algebra.union.ground 0)
    geometry.carrier_ground hTimes (geometry.copies_ground _ data.group.group_code.identity_mem) hBirth,
    pushedHeightGraph_function embedding.injection born,
    pushedBirthGraph_oldMeet completion.algebra.union.meet geometry.meet embedding.toMeetEmbeddingCode born oldMeet⟩

theorem externalSeedBirth_entry
    (born : ZFSet.IsFunc (completion.algebra.union.fields 0) times birth)
    {x y t : ZFSet.{u}} (copied : ZFSet.pair x y ∈ completion.externalIdentityCopyGraph P0 r0 μ0 A0) :
    ZFSet.pair y t ∈ old ↔ ZFSet.pair x t ∈ birth :=
  pushedHeightGraph_entry
    (data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG).injection born copied

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end


namespace PartitionPilot.Forcing
universe u
namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
noncomputable def externalBirthGraph (P r μ A oldTimes oldBirth limit stamps : ZFSet.{u}) : ZFSet.{u} :=
  ownerBirthGraph (completion.externalSeedCarrier P r μ A) (completion.externalPointCarrier P r μ A)
    limit (completion.externalSeedBirth P r μ A oldTimes oldBirth)
    (completion.externalOwnerLevels P r μ A) stamps

end GroundCompressionCompletion

structure GroundExternalBirthData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P r μ A oldTimes oldBirth : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ) where
  stamps : ZFSet.{u}
  limit : ZFSet.{u}
  stamps_ground : stamps ∈ M.sets
  limit_ground : limit ∈ M.sets
  times : CompressionStampCode oldTimes stamps limit
  seed_function : ZFSet.IsFunc (completion.externalSeedCarrier P r μ A) oldTimes
    (completion.externalSeedBirth P r μ A oldTimes oldBirth)
  birth_ground : completion.externalBirthGraph P r μ A oldTimes oldBirth limit stamps ∈ M.sets
  function : ZFSet.IsFunc (completion.externalPointCarrier P r μ A) limit
    (completion.externalBirthGraph P r μ A oldTimes oldBirth limit stamps)
  old_meet : OldMeetCode (completion.externalPointOrder P r μ A) (completion.externalPointMeet P r μ A)
    (completion.externalBirthGraph P r μ A oldTimes oldBirth limit stamps)
  preserves_seed : ∀ x y t, ZFSet.pair x y ∈ completion.externalIdentityCopyGraph P r μ A →
    (ZFSet.pair y t ∈ completion.externalBirthGraph P r μ A oldTimes oldBirth limit stamps ↔
      ZFSet.pair x t ∈ oldBirth)

namespace GroundExternalBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P r μ A oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalBirthData M initial I Sources Reps G m one T τ P r μ A oldTimes oldBirth completion)
noncomputable def birth : ZFSet.{u} :=
  completion.externalBirthGraph P r μ A oldTimes oldBirth data.limit data.stamps

include data
theorem old_before {x a : ZFSet.{u}}
    (entry : ZFSet.pair x a ∈ completion.externalSeedBirth P r μ A oldTimes oldBirth) (n : Nat) :
    a ∈ compressionStamp oldTimes n :=
  compressionStamp_old_mem (Or.inl (ZFSet.pair_mem_prod.1 (data.seed_function.1 entry)).2) n

theorem stamp_fiber (n : Nat) (x : ZFSet.{u}) :
    ZFSet.pair x (compressionStamp oldTimes n) ∈ data.birth ↔
      x ∈ ownerFresh (completion.externalSeedCarrier P r μ A) (completion.externalPointCarrier P r μ A) ∧
        ZFSet.pair x (natSetCode n) ∈ completion.externalOwnerLevels P r μ A := by
  apply ownerBirthGraph_stamp_fiber data.seed_function data.times.ownerStampCode
  · intro y a k t entry stamp
    rw [(data.times.entries k t).1 stamp]
    exact data.old_before entry k
  · exact (data.times.entries n _).2 rfl

theorem no_limit_birth (x : ZFSet.{u}) : ZFSet.pair x data.limit ∉ data.birth :=
  fun entry => ZFSet.mem_irrefl data.limit (ZFSet.pair_mem_prod.1 (data.function.1 entry)).2

end GroundExternalBirthData

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "s" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "vpres" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "vcode" => completion.externalFamilyVertexCode group oldAction data.original

noncomputable def externalBirthCopyVertex (k : Nat) (r : Index) : Option ((family).Child r) := by
  classical
  exact if h : ∃ i, ((family).request r).vertexSlot i = k % 3 then Classical.choose h else none

theorem externalBirthCopyVertex_eq (k : Nat) (r : Index) (i : Option ((family).Child r))
    (slot : ((family).request r).vertexSlot i = k % 3) :
    data.externalBirthCopyVertex group oldAction k r = i := by
  classical
  have existsSlot : ∃ j, ((family).request r).vertexSlot j = k % 3 := ⟨i, slot⟩
  simp only [externalBirthCopyVertex, dite_eq_left existsSlot]
  exact ((family).request r).vertexSlot_injective ((Classical.choose_spec existsSlot).trans slot.symm)

include data group oldAction pairing unions powers separation infinite hG

theorem externalBirthCopy_witness (hP0 : P0 ∈ M.sets) (k : Nat) {x : ZFSet.{u}}
    (level : ZFSet.pair x (natSetCode k) ∈ completion.externalOwnerLevels P0 r0 μ0 A0) :
    letI := group.toGroup
    ∃ w r, ZFSet.pair x ((vpres).encode (.inr (w, r))) ∈ completion.externalStarOwner P0 r0 μ0 A0 ∧
      x ∈ relationImage U B (completion.externalCopyGraph P0 r0 μ0 A0
        ((s).encode ((family).flatWord w r (data.externalBirthCopyVertex group oldAction k r)))) := by
  let := group.toGroup
  have owner := (data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
  obtain ⟨_, v, n, j, hj, owned, _, slot, rank⟩ :=
    (data.externalOwnerLevels_entry_iff group oldAction pairing unions powers separation infinite hG hP0 x k).1 level
  have selected := (pair_mem_leastSlotOwnerGraph_of_owner owner owned).1 slot
  obtain ⟨w, r, i, a, eqV, eqJ, eqX⟩ :=
    data.externalTileSlotPoints_decode group oldAction pairing unions powers separation infinite hG selected.2.2.1
  have ji : j = ((family).request r).vertexSlot i := by
    apply natSetCode_injective
    exact eqJ.trans (completion.externalFamilyVertexCode_eq_slot group oldAction data.original r i)
  have chosen : data.externalBirthCopyVertex group oldAction k r = i := by
    apply data.externalBirthCopyVertex_eq group oldAction
    rw [← ji, rank, depthSlotIndex, Nat.add_mod]
    simp only [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt hj]
  refine ⟨w, r, eqV ▸ owned, ?_⟩
  rw [chosen, eqX, (family).flatVertex_copy]
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  rw [data.externalCopyGraph_eq_graph group oldAction pairing unions powers separation infinite hG]
  apply (mem_relationImage _ _ _ _).2
  exact ⟨qc ▸ (q).encode_mem _, SetMembers.raw a, SetMembers.raw_mem a,
    ((SetMembers.presentation U).pair_mem_graph (q) _ a _).2 rfl⟩

end PartitionPilot.Forcing.GroundExternalGeometryInputs



namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "old" => completion.externalSeedBirth P0 r0 μ0 A0 oldTimes oldBirth
include data group oldAction pairing unions powers separation collection infinite hG hP0

theorem exists_externalBirths_of_seed (hOldTimes : oldTimes ∈ M.sets)
    (ordinal : ordinalSetProperty oldTimes) (hOldBirth : oldBirth ∈ M.sets)
    (born : ZFSet.IsFunc (completion.algebra.union.fields 0) oldTimes oldBirth)
    (oldMeet : OldMeetCode (completion.algebra.union.fields 1) (completion.algebra.union.fields 2) oldBirth) :
    Nonempty (GroundExternalBirthData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 oldTimes oldBirth completion) := by
  obtain ⟨stamps, hStamps, limit, hLimit, _, stampCode⟩ :=
    M.exists_groundCompressionStamps pairing unions separation collection infinite hOldTimes ordinal
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have seed := data.externalSeedBirth_spec group oldAction pairing unions powers separation infinite hG hP0
    hOldTimes hOldBirth born oldMeet
  have levels := data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0
  have hP := data.externalSeedCarrier_ground group oldAction pairing unions powers separation infinite hG hP0
  have subset : P ⊆ B := fun _ hx => ((mem_relationImage _ _ _ _).1 hx).1
  have times : oldTimes ⊆ limit := fun _ ht => stampCode.union.subset 0 (compressionStamp_old_mem (Or.inl ht) 0)
  have oldBefore : ∀ x a n t, ZFSet.pair x a ∈ old → ZFSet.pair (natSetCode n) t ∈ stamps → a ∈ t := by
    intro x a n t entry stamp
    rw [(stampCode.entries n t).1 stamp]
    exact compressionStamp_old_mem (Or.inl (ZFSet.pair_mem_prod.1 (seed.2.1.1 entry)).2) n
  refine ⟨{
    stamps := stamps
    limit := limit
    stamps_ground := hStamps
    limit_ground := hLimit
    times := stampCode
    seed_function := seed.2.1
    birth_ground := M.ownerBirthGraph_mem pairing unions powers separation hP geometry.carrier_ground hLimit
      seed.1 levels.1 hStamps (M.omega_mem separation infinite)
    function := ownerBirthGraph_function seed.2.1 subset times levels.2 stampCode.function
    old_meet := ?_
    preserves_seed := ?_ }⟩
  · apply ownerBirthGraph_oldMeet geometry.meet seed.2.1 subset times levels.2 stampCode.ownerStampCode seed.2.2
    · intro x hx y hy lower
      exact data.externalSeedCarrier_lower group oldAction pairing unions powers separation infinite hG hx hy lower
    · exact oldBefore
    · intro x _ y _ n k first second lower
      exact data.externalOwnerLevels_monotone group oldAction pairing unions powers separation infinite hG hP0 lower first second
  · intro x y t copied
    have embedding := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
    have bounds := ZFSet.pair_mem_prod.1 (embedding.injection.function.1 copied)
    have hy : y ∈ P := (mem_relationImage _ _ _ _).2 ⟨bounds.2, x, bounds.1, copied⟩
    exact (ownerBirthGraph_old_iff hy).trans
      (data.externalSeedBirth_entry group oldAction pairing unions powers separation infinite hG born copied)

theorem exists_externalBirths {base originalBirth : ZFSet.{u}}
    (births : GroundCompressionBirthData M initial I Sources Reps G m one T
      completion.algebra.union base originalBirth) :
    Nonempty (GroundExternalBirthData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 births.limit births.birth completion) :=
  data.exists_externalBirths_of_seed group oldAction pairing unions powers separation collection infinite hG hP0
    births.limit_ground births.times.ordinal births.birth_ground births.function births.old_meet

end PartitionPilot.Forcing.GroundExternalGeometryInputs



namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetFormula SetRealization Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "U" => completion.algebra.union.fields 0
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "owners" => completion.externalStarOwner P0 r0 μ0 A0
local notation "depths" => M.externalStarDepth G letters requests m one
local notation "levels" => completion.externalOwnerLevels P0 r0 μ0 A0
local notation "family" => completion.externalFamily group oldAction data.original
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "vpres" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "s" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
include data group oldAction pairing unions powers separation infinite hG

theorem externalBirthCopy_level_slot (hP0 : P0 ∈ M.sets) :
    letI := group.toGroup
    ∀ (w : External (SetMembers G) (family).Letters) (r : Index) (k : Nat) {x : ZFSet.{u}},
      ZFSet.pair x ((vpres).encode (.inr (w, r))) ∈ owners →
      ZFSet.pair x (natSetCode k) ∈ levels →
        ∃ n, ZFSet.pair ((vpres).encode (.inr (w, r))) (natSetCode n) ∈ depths ∧
          k = depthSlotIndex n (((family).request r).vertexSlot (data.externalBirthCopyVertex group oldAction k r)) := by
  let := group.toGroup
  intro w r k x active level
  obtain ⟨_, v, n, j, hj, owned, depth, slot, rank⟩ :=
    (data.externalOwnerLevels_entry_iff group oldAction pairing unions powers separation infinite hG hP0 x k).1 level
  have owner := (data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
  have sameOwner := (show FunctionGraphOn B owners from ⟨_, owner⟩).unique owned active
  subst v
  have selected := (pair_mem_leastSlotOwnerGraph_of_owner owner active).1 slot
  obtain ⟨w', r', i, _, eqV, eqJ, _⟩ :=
    data.externalTileSlotPoints_decode group oldAction pairing unions powers separation infinite hG selected.2.2.1
  have same := Sum.inr.inj ((vpres).injective eqV)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  have ji : j = ((family).request r).vertexSlot i :=
    natSetCode_injective (eqJ.trans (completion.externalFamilyVertexCode_eq_slot group oldAction data.original r i))
  have chosen : data.externalBirthCopyVertex group oldAction k r = i := by
    apply data.externalBirthCopyVertex_eq group oldAction
    rw [← ji, rank, depthSlotIndex, Nat.add_mod]
    simp only [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt hj]
  exact ⟨n, depth, by rw [chosen, ← ji]; exact rank⟩

theorem externalBirthCopy_level_bound (hP0 : P0 ∈ M.sets) :
    letI := group.toGroup
    ∀ (w : External (SetMembers G) (family).Letters) (r : Index) (k : Nat) {x u y : ZFSet.{u}},
      ZFSet.pair x ((vpres).encode (.inr (w, r))) ∈ owners →
      ZFSet.pair x (natSetCode k) ∈ levels →
      ZFSet.pair u y ∈ completion.externalCopyGraph P0 r0 μ0 A0
        ((s).encode ((family).flatWord w r (data.externalBirthCopyVertex group oldAction k r))) →
      y ∈ P ∨ ∃ l ≤ k, ZFSet.pair y (natSetCode l) ∈ levels := by
  let := group.toGroup
  intro w r k x u y active level copied
  obtain ⟨n, depth, rank⟩ := data.externalBirthCopy_level_slot group oldAction pairing unions powers separation infinite hG hP0
    w r k active level
  let i := data.externalBirthCopyVertex group oldAction k r
  rw [data.externalCopyGraph_eq_graph group oldAction pairing unions powers separation infinite hG] at copied
  obtain ⟨a, equal⟩ := ((SetMembers.presentation U).mem_graph (q) _ _).1 copied
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  have supported := (data.externalTileSlotPoints_entry group oldAction pairing unions powers separation infinite hG
    w r i ((family).copy (action) ((family).flatWord w r i) |>.toFun a)).2
    ⟨a, (family).flatVertex_copy (action) w r i a⟩
  rw [completion.externalFamilyVertexCode_eq_slot group oldAction data.original r i] at supported
  have bound := data.externalSlotCopy_old_or_level_bound group oldAction pairing unions powers separation infinite hG hP0
    supported depth
  rw [← rank] at bound
  exact bound

theorem externalBirthCopy_image_level_bound (hP0 : P0 ∈ M.sets) :
    letI := group.toGroup
    ∀ (w : External (SetMembers G) (family).Letters) (r : Index) (k : Nat) {x y : ZFSet.{u}},
      ZFSet.pair x ((vpres).encode (.inr (w, r))) ∈ owners →
      ZFSet.pair x (natSetCode k) ∈ levels →
      y ∈ relationImage U B (completion.externalCopyGraph P0 r0 μ0 A0
        ((s).encode ((family).flatWord w r (data.externalBirthCopyVertex group oldAction k r)))) →
      y ∈ P ∨ ∃ l ≤ k, ZFSet.pair y (natSetCode l) ∈ levels := by
  let := group.toGroup
  intro w r k x y active level image
  obtain ⟨_, u, _, copied⟩ := (mem_relationImage _ _ _ _).1 image
  exact data.externalBirthCopy_level_bound group oldAction pairing unions powers separation infinite hG hP0
    w r k active level copied

end PartitionPilot.Forcing.GroundExternalGeometryInputs




namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "s" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "vpres" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "levels" => completion.externalOwnerLevels P0 r0 μ0 A0
local notation "owner" => completion.externalStarOwner P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG hP0 births

noncomputable def externalBirth_fresh_layer
    (Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u})
    (atSpace : Space oldTimes = U)
    (atOrder : sourceOrder oldTimes = completion.algebra.union.fields 1)
    (atMeet : sourceMeet oldTimes = completion.algebra.union.fields 2) (k : Nat) :
    CodedGrowthLayer M Space sourceOrder sourceMeet B (completion.externalPointOrder P0 r0 μ0 A0)
      (completion.externalPointMeet P0 r0 μ0 A0) births.birth (compressionStamp oldTimes k) := by
  classical
  letI := group.toGroup
  let Copies := External (SetMembers G) (family).Letters × Index
  let e (v : Copies) := completion.externalCopyGraph P0 r0 μ0 A0
    ((s).encode ((family).flatWord v.1 v.2 (data.externalBirthCopyVertex group oldAction k v.2)))
  let Slice := {x : ZFSet.{u} // x ∈ ownerFresh P B ∧ ZFSet.pair x (natSetCode k) ∈ levels}
  have witnesses (x : Slice) : ∃ v : Copies,
      ZFSet.pair x.val ((vpres).encode (.inr v)) ∈ owner ∧ x.val ∈ relationImage U B (e v) := by
    obtain ⟨w, r, owned, covered⟩ :=
      data.externalBirthCopy_witness group oldAction pairing unions powers separation infinite hG hP0 k x.property.2
    exact ⟨(w, r), owned, covered⟩
  let pick (x : Slice) : Copies := Classical.choose (witnesses x)
  have selected (x : Slice) :
      ZFSet.pair x.val ((vpres).encode (.inr (pick x))) ∈ owner ∧
        x.val ∈ relationImage U B (e (pick x)) := Classical.choose_spec (witnesses x)
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have levelCode := (data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have oldSubset : P ⊆ B := fun _ hx => ((mem_relationImage _ _ _ _).1 hx).1
  have times : oldTimes ⊆ births.limit := fun _ ht =>
    births.times.union.subset 0 (compressionStamp_old_mem (Or.inl ht) 0)
  have oldBefore : ∀ x a n t, ZFSet.pair x a ∈ completion.externalSeedBirth P0 r0 μ0 A0 oldTimes oldBirth →
      ZFSet.pair (natSetCode n) t ∈ births.stamps → a ∈ t := by
    intro x a n t entry stamp
    rw [(births.times.entries n t).1 stamp]
    exact births.old_before entry n
  refine ownerBirthGraph_separated births.seed_function oldSubset times levelCode births.times.ownerStampCode
    oldBefore ((births.times.entries k _).2 rfl) Copies (fun _ => oldTimes) e
    (fun _ => compressionStamp_base_mem oldTimes k) ?_ ?_ pick ?_ ?_
  · intro v
    exact geometry.copies_ground _ (sc ▸ (s).encode_mem _)
  · intro v
    rw [atSpace, atOrder, atMeet]
    exact geometry.copies _ (sc ▸ (s).encode_mem _)
  · intro x _
    rw [atSpace]
    exact (selected x).2
  · intro x y _ _ different
    have differentOwners : (vpres).encode (.inr (pick x)) ≠ (vpres).encode (.inr (pick y)) := by
      intro equal
      exact different (Sum.inr.inj ((vpres).injective equal))
    have hx := ((mem_ownerFresh P B x.val).1 x.property.1).1
    have hy := ((mem_ownerFresh P B y.val).1 y.property.1).1
    obtain ⟨z, meetEntry, _⟩ := geometry.meet.operation.2 (ZFSet.pair x.val y.val) (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
    refine ⟨z, (ZFSet.pair_mem_prod.1 (geometry.meet.operation.1 meetEntry)).2, meetEntry, ?_⟩
    exact data.externalOwnerLevels_meet_old_or_lower group oldAction pairing unions powers separation infinite hG hP0
      (selected x).1 (selected y).1 differentOwners x.property.2 y.property.2 meetEntry

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end OAI
