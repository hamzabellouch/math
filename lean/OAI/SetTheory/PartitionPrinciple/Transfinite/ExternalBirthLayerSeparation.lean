import OAI.SetTheory.PartitionPrinciple.Definability.CodedLayerRestrictions
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalSlotCopies
import OAI.SetTheory.PartitionPrinciple.Transfinite.ExternalChronologyStageLaws

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundExternalBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion)
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "V" => M.externalStarVertices G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0))
  (externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)) m one
local notation "owner" => completion.externalStarOwner P0 r0 μ0 A0

noncomputable def layerFiber (k : Nat) : ZFSet.{u} := layerBirthFiber B births.birth (compressionStamp oldTimes k)
noncomputable def layerOwners (k : Nat) : ZFSet.{u} := relationImage (births.layerFiber k) V owner
noncomputable def layerComponents (k : Nat) : ZFSet.{u} := graphRestriction (births.layerFiber k) owner
noncomputable def layerIndices (k : Nat) : ZFSet.{u} := constantFamilyGraph (births.layerOwners k) oldTimes
noncomputable def layerMaps (k : Nat) : ZFSet.{u} :=
  completion.externalSlotCopyMaps P0 r0 μ0 A0 (births.layerOwners k) (natSetCode (k % 3))
noncomputable def layerWitness (k : Nat) : ZFSet.{u} :=
  separatedLayerWitness (births.layerOwners k) (births.layerIndices k) (births.layerMaps k)
    (M.groundRelations U B) (births.layerComponents k) (births.layerFiber k)

theorem mem_layerFiber (k : Nat) (x : ZFSet.{u}) :
    x ∈ births.layerFiber k ↔ x ∈ B ∧ ZFSet.pair x (compressionStamp oldTimes k) ∈ births.birth :=
  mem_layerBirthFiber _ _ _ _

theorem layerFiber_level {k : Nat} {x : ZFSet.{u}} (hx : x ∈ births.layerFiber k) :
    ZFSet.pair x (natSetCode k) ∈ completion.externalOwnerLevels P0 r0 μ0 A0 :=
  ((births.stamp_fiber k x).1 ((births.mem_layerFiber k x).1 hx).2).2

theorem layerOwners_cases {k : Nat} {v : ZFSet.{u}} (hv : v ∈ births.layerOwners k) :
    v ∈ V ∧ ∃ x ∈ births.layerFiber k, ZFSet.pair x v ∈ owner :=
  (mem_relationImage _ _ _ _).1 hv

variable {inv : ZFSet.{u}}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
include data group oldAction pairing unions powers separation infinite hG hP0

theorem layer_fields_ground (k : Nat) :
    births.layerFiber k ∈ M.sets ∧ births.layerOwners k ∈ M.sets ∧
      births.layerComponents k ∈ M.sets ∧ births.layerIndices k ∈ M.sets ∧
      births.layerMaps k ∈ M.sets ∧ M.groundRelations U B ∈ M.sets := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have owners := data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0
  have vertices := (data.externalStarCarriers_ground pairing unions powers separation hG).1
  have fiber := M.layerBirthFiber_mem separation geometry.carrier_ground births.birth_ground
    (M.transitive births.limit_ground (births.times.stamp_mem_limit k))
  have active := M.relationImage_mem separation fiber vertices owners.1
  have components := M.graphRestriction_mem unions separation fiber owners.1
  have indices := M.constantFamilyGraph_mem pairing unions powers separation active
    (M.transitive births.limit_ground births.times.base_mem_limit)
  have maps := data.externalSlotCopyMaps_spec group oldAction pairing unions powers separation infinite hG hP0
    active (M.natSetCode_mem separation infinite (k % 3))
  exact ⟨fiber, active, components, indices, maps.1,
    M.groundRelations_mem pairing unions powers separation (completion.algebra.union.ground 0) geometry.carrier_ground⟩

theorem layerComponents_function (k : Nat) :
    ZFSet.IsFunc (births.layerFiber k) (births.layerOwners k) (births.layerComponents k) := by
  have ownerCode := (data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
  have restricted := (show FunctionGraphOn B owner from ⟨V, ownerCode⟩).restrict
    (fun x hx => (births.mem_layerFiber k x).1 hx |>.1)
  apply isFunc_retarget_of_entries restricted.to_isFunc
  intro x v entry
  obtain ⟨owned, hx⟩ := pair_mem_graphRestriction.1 entry
  exact (mem_relationImage _ _ _ _).2
    ⟨(ZFSet.pair_mem_prod.1 (ownerCode.1 owned)).2, x, hx, owned⟩

omit data group oldAction pairing unions powers separation infinite hG hP0 in
theorem layerIndices_function (k : Nat) :
    ZFSet.IsFunc (births.layerOwners k) (compressionStamp oldTimes k) (births.layerIndices k) := by
  apply isFunc_retarget_of_entries (constantFamilyGraph_function (births.layerOwners k) oldTimes)
  intro v t entry
  rw [((pair_mem_constantFamilyGraph _ _ _ _).1 entry).2]
  exact compressionStamp_base_mem oldTimes k

theorem layerMaps_spec (k : Nat) :
    ZFSet.IsFunc (births.layerOwners k) (M.groundRelations U B) (births.layerMaps k) ∧
      ∀ v e, ZFSet.pair v e ∈ births.layerMaps k ↔ v ∈ births.layerOwners k ∧
        e = indexedRelationSection U B (completion.externalSlotCopyRelation P0 r0 μ0 A0 (natSetCode (k % 3))) v := by
  exact (data.externalSlotCopyMaps_spec group oldAction pairing unions powers separation infinite hG hP0
    (births.layer_fields_ground data group oldAction pairing unions powers separation infinite hG hP0 k).2.1
    (M.natSetCode_mem separation infinite (k % 3))).2

theorem layerWitness_ground (k : Nat) : births.layerWitness k ∈ M.sets := by
  have ground := births.layer_fields_ground data group oldAction pairing unions powers separation infinite hG hP0 k
  exact M.separatedLayerWitness_mem pairing unions ground.2.1 ground.2.2.2.1
    ground.2.2.2.2.1 ground.2.2.2.2.2 ground.2.2.1 ground.1

end GroundExternalBirthData
end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula SetRealization Compression Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "s" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "vpres" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "owner" => completion.externalStarOwner P0 r0 μ0 A0
local notation "levels" => completion.externalOwnerLevels P0 r0 μ0 A0
include births data group oldAction pairing unions powers separation infinite hG hP0

theorem layerMaps_copy (k : Nat) {x v e : ZFSet.{u}}
    (hx : x ∈ births.layerFiber k) (owned : ZFSet.pair x v ∈ owner)
    (mapEntry : ZFSet.pair v e ∈ births.layerMaps k) :
    letI := group.toGroup
    ∃ w r, v = (vpres).encode (.inr (w, r)) ∧
      e = completion.externalCopyGraph P0 r0 μ0 A0
        ((s).encode ((family).flatWord w r (data.externalBirthCopyVertex group oldAction k r))) ∧
      x ∈ relationImage U B e := by
  let := group.toGroup
  have level := births.layerFiber_level hx
  obtain ⟨w, r, actualOwner, covered⟩ := data.externalBirthCopy_witness group oldAction
    pairing unions powers separation infinite hG hP0 k level
  have ownerCode : FunctionGraphOn B owner :=
    ⟨_, (data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0).2⟩
  have same := ownerCode.unique owned actualOwner
  obtain ⟨n, _, rank⟩ := data.externalBirthCopy_level_slot group oldAction
    pairing unions powers separation infinite hG hP0 w r k actualOwner level
  let i := data.externalBirthCopyVertex group oldAction k r
  have slot : ((family).request r).vertexSlot i = k % 3 := by
    rw [rank, depthSlotIndex, Nat.add_mod]
    simp only [i, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod, Nat.zero_add,
      Nat.mod_eq_of_lt (((family).request r).vertexSlot_lt_three (data.externalBirthCopyVertex group oldAction k r))]
  have literal : completion.externalFamilyVertexCode group oldAction data.original r i = natSetCode (k % 3) :=
    (completion.externalFamilyVertexCode_eq_slot group oldAction data.original r i).trans
      (congrArg natSetCode slot)
  have mapEq := ((births.layerMaps_spec data group oldAction pairing unions powers separation infinite hG hP0 k).2 v e).1 mapEntry |>.2
  have sectionEq := data.externalSlotCopySection_eq group oldAction pairing unions powers separation infinite hG w r i
  rw [literal, ← same] at sectionEq
  have actual := mapEq.trans sectionEq
  exact ⟨w, r, same, actual, actual.symm ▸ covered⟩

theorem layerMaps_embedding (k : Nat) {v e : ZFSet.{u}}
    (mapEntry : ZFSet.pair v e ∈ births.layerMaps k) :
    MeetEmbeddingCode U B (completion.algebra.union.fields 1) (completion.externalPointOrder P0 r0 μ0 A0)
      (completion.algebra.union.fields 2) (completion.externalPointMeet P0 r0 μ0 A0) e := by
  let := group.toGroup
  have active := ((births.layerMaps_spec data group oldAction pairing unions powers separation infinite hG hP0 k).2 v e).1 mapEntry |>.1
  obtain ⟨_, x, hx, owned⟩ := births.layerOwners_cases active
  obtain ⟨w, r, _, rfl, _⟩ := births.layerMaps_copy data group oldAction pairing unions powers separation infinite hG hP0 k hx owned mapEntry
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  exact geometry.copies _ (sc ▸ (s).encode_mem _)

theorem layerMaps_outputs_cutoff (k n : Nat) (before : k ≤ n) {v e u y : ZFSet.{u}}
    (mapEntry : ZFSet.pair v e ∈ births.layerMaps k) (copied : ZFSet.pair u y ∈ e) :
    y ∈ births.cutoff n := by
  let := group.toGroup
  have active := ((births.layerMaps_spec data group oldAction pairing unions powers separation infinite hG hP0 k).2 v e).1 mapEntry |>.1
  obtain ⟨_, x, hx, owned⟩ := births.layerOwners_cases active
  obtain ⟨w, r, same, actual, _⟩ := births.layerMaps_copy data group oldAction pairing unions powers separation infinite hG hP0 k hx owned mapEntry
  rcases data.externalBirthCopy_level_bound group oldAction pairing unions powers separation infinite hG hP0
    w r k (same ▸ owned) (births.layerFiber_level hx) (actual ▸ copied) with old | ⟨l, bound, level⟩
  · exact births.cutoff_old n old
  · have levelCode := (data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
    have fresh := (mem_ownerFresh P B y).1 (ZFSet.pair_mem_prod.1 (levelCode.1 level)).1
    apply (mem_ownerLevelPrefix _ _ _ _ _).2
    refine Or.inr ⟨fresh.1, fresh.2, natSetCode l, natSetCode_mem_omega l, level, ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_trans bound before) with less | same
    · exact Or.inr ((natSetCode_mem_iff _ _).2 less)
    · exact Or.inl (congrArg natSetCode same)

theorem layerMaps_cutoff_embedding (k n : Nat) (before : k ≤ n) {v e : ZFSet.{u}}
    (mapEntry : ZFSet.pair v e ∈ births.layerMaps k) :
    MeetEmbeddingCode U (births.cutoff n) (completion.algebra.union.fields 1) (births.cutoffOrder n)
      (completion.algebra.union.fields 2) (births.cutoffMeet n) e :=
  (births.layerMaps_embedding data group oldAction pairing unions powers separation infinite hG hP0 k mapEntry).restrictTarget
    (fun _ _ copied => births.layerMaps_outputs_cutoff data group oldAction pairing unions powers separation infinite hG hP0 k n before mapEntry copied)

end PartitionPilot.Forcing.GroundExternalBirthData




namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula SetRealization Compression Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "s" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "vpres" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "owner" => completion.externalStarOwner P0 r0 μ0 A0
local notation "levels" => completion.externalOwnerLevels P0 r0 μ0 A0
include births data group oldAction pairing unions powers separation infinite hG hP0

omit data group oldAction pairing unions powers separation infinite hG hP0 in
theorem layerFiber_cutoff (k n : Nat) (before : k ≤ n) :
    births.layerFiber k = layerBirthFiber (births.cutoff n) (births.cutoffBirth n) (compressionStamp oldTimes k) := by
  apply ZFSet.ext
  intro x
  rw [births.mem_layerFiber, mem_layerBirthFiber]
  constructor
  · rintro ⟨hx, entry⟩
    have fresh := (births.stamp_fiber k x).1 entry
    have hxCut : x ∈ births.cutoff n := by
      apply (mem_ownerLevelPrefix _ _ _ _ _).2
      refine Or.inr ⟨hx, ((mem_ownerFresh P B x).1 fresh.1).2,
        natSetCode k, natSetCode_mem_omega k, fresh.2, ?_⟩
      rcases Nat.lt_or_eq_of_le before with less | same
      · exact Or.inr ((natSetCode_mem_iff _ _).2 less)
      · exact Or.inl (congrArg natSetCode same)
    exact ⟨hxCut, pair_mem_graphRestriction.2 ⟨entry, hxCut⟩⟩
  · rintro ⟨hx, entry⟩
    exact ⟨births.cutoff_subset n hx, (pair_mem_graphRestriction.1 entry).1⟩

theorem layerComponents_earlier_meet (k : Nat) {x y v w : ZFSet.{u}}
    (hx : x ∈ births.layerFiber k) (hy : y ∈ births.layerFiber k)
    (first : ZFSet.pair x v ∈ births.layerComponents k)
    (second : ZFSet.pair y w ∈ births.layerComponents k) (different : v ≠ w) :
    ∃ z a, ZFSet.pair (ZFSet.pair x y) z ∈ completion.externalPointMeet P0 r0 μ0 A0 ∧
      ZFSet.pair z a ∈ births.birth ∧ a ∈ compressionStamp oldTimes k := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have bounds := ZFSet.pair_mem_prod.2
    ⟨((births.mem_layerFiber k x).1 hx).1, ((births.mem_layerFiber k y).1 hy).1⟩
  obtain ⟨z, meetEntry, _⟩ := geometry.meet.operation.2 (ZFSet.pair x y) bounds
  have hz := (ZFSet.pair_mem_prod.1 (geometry.meet.operation.1 meetEntry)).2
  obtain ⟨a, born, _⟩ := births.function.2 z hz
  have earlier := data.externalOwnerLevels_meet_old_or_lower group oldAction pairing unions powers separation infinite hG hP0
    (pair_mem_graphRestriction.1 first).1 (pair_mem_graphRestriction.1 second).1 different
    (births.layerFiber_level hx) (births.layerFiber_level hy) meetEntry
  refine ⟨z, a, meetEntry, born, ?_⟩
  apply ownerBirthGraph_earlier_of_level births.seed_function
    (data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
    births.times.ownerStampCode ?_ ((births.times.entries k _).2 rfl) born earlier
  intro u b j t entry stamp
  rw [(births.times.entries j t).1 stamp]
  exact births.old_before entry j

end PartitionPilot.Forcing.GroundExternalBirthData

end OAI
