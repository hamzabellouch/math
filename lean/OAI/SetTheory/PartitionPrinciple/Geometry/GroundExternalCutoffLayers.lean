import OAI.SetTheory.PartitionPrinciple.Definability.CodedLayerRestrictions
import OAI.SetTheory.PartitionPrinciple.Transfinite.ExternalChronologyStageLaws

namespace OAI



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

noncomputable def externalBirth_cutoff_fresh_layer
    (Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u})
    (atSpace : Space oldTimes = U)
    (atOrder : sourceOrder oldTimes = completion.algebra.union.fields 1)
    (atMeet : sourceMeet oldTimes = completion.algebra.union.fields 2)
    (k n : Nat) (before : k ≤ n) :
    CodedGrowthLayer M Space sourceOrder sourceMeet (births.cutoff n) (births.cutoffOrder n)
      (births.cutoffMeet n) (births.cutoffBirth n) (compressionStamp oldTimes k) := by
  classical
  letI := group.toGroup
  let Copies := External (SetMembers G) (family).Letters × Index
  let Slice := {x : ZFSet.{u} // x ∈ ownerFresh P B ∧ ZFSet.pair x (natSetCode k) ∈ levels}
  let Active := {v : Copies // ∃ x : Slice, ZFSet.pair x.val ((vpres).encode (.inr v)) ∈ owner}
  let e (v : Active) := completion.externalCopyGraph P0 r0 μ0 A0
    ((s).encode ((family).flatWord v.val.1 v.val.2 (data.externalBirthCopyVertex group oldAction k v.val.2)))
  have witnesses (x : Slice) : ∃ v : Active,
      ZFSet.pair x.val ((vpres).encode (.inr v.val)) ∈ owner ∧ x.val ∈ relationImage U B (e v) := by
    obtain ⟨w, r, owned, covered⟩ :=
      data.externalBirthCopy_witness group oldAction pairing unions powers separation infinite hG hP0 k x.property.2
    exact ⟨⟨(w, r), x, owned⟩, owned, covered⟩
  let pick (x : Slice) : Active := Classical.choose (witnesses x)
  have selected (x : Slice) :
      ZFSet.pair x.val ((vpres).encode (.inr (pick x).val)) ∈ owner ∧
        x.val ∈ relationImage U B (e (pick x)) := Classical.choose_spec (witnesses x)
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have levelCode := (data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have values (v : Active) : ∀ x y, ZFSet.pair x y ∈ e v → y ∈ births.cutoff n := by
    intro x y entry
    obtain ⟨active, owned⟩ := v.property
    rcases data.externalBirthCopy_level_bound group oldAction pairing unions powers separation infinite hG hP0
      v.val.1 v.val.2 k owned active.property.2 entry with old | ⟨l, bound, level⟩
    · exact births.cutoff_old n old
    · have fresh := (mem_ownerFresh P B y).1 (ZFSet.pair_mem_prod.1 (levelCode.1 level)).1
      apply (mem_ownerLevelPrefix _ _ _ _ _).2
      refine Or.inr ⟨fresh.1, fresh.2, natSetCode l, natSetCode_mem_omega l, level, ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_trans bound before) with less | same
      · exact Or.inr ((natSetCode_mem_iff _ _).2 less)
      · exact Or.inl (congrArg natSetCode same)
  have cutoffMeet := geometry.meet.restrict_lower (births.cutoff_subset n)
    (births.cutoff_lower data group oldAction pairing unions powers separation infinite hG hP0 n)
  have oldSubset : P ⊆ B := fun _ hx => ((mem_relationImage _ _ _ _).1 hx).1
  have times : oldTimes ⊆ births.limit := fun _ ht =>
    births.times.union.subset 0 (compressionStamp_old_mem (Or.inl ht) 0)
  have oldBefore : ∀ x a j t, ZFSet.pair x a ∈ completion.externalSeedBirth P0 r0 μ0 A0 oldTimes oldBirth →
      ZFSet.pair (natSetCode j) t ∈ births.stamps → a ∈ t := by
    intro x a j t entry stamp
    rw [(births.times.entries j t).1 stamp]
    exact births.old_before entry j
  have layer : CodedGrowthLayer M Space sourceOrder sourceMeet (births.cutoff n) (births.cutoffOrder n)
      (births.cutoffMeet n) births.birth (compressionStamp oldTimes k) := by
    refine ownerBirthGraph_separated births.seed_function oldSubset times levelCode births.times.ownerStampCode
      oldBefore ((births.times.entries k _).2 rfl) Active (fun _ => oldTimes) e
      (fun _ => compressionStamp_base_mem oldTimes k) ?_ ?_ pick ?_ ?_
    · intro v
      exact geometry.copies_ground _ (sc ▸ (s).encode_mem _)
    · intro v
      rw [atSpace, atOrder, atMeet]
      exact (geometry.copies _ (sc ▸ (s).encode_mem _)).restrictTarget (values v)
    · intro x hx
      rw [atSpace]
      obtain ⟨_, u, hu, entry⟩ := (mem_relationImage _ _ _ _).1 (selected x).2
      exact (mem_relationImage _ _ _ _).2 ⟨hx, u, hu, entry⟩
    · intro x y hx hy different
      have differentOwners : (vpres).encode (.inr (pick x).val) ≠ (vpres).encode (.inr (pick y).val) := by
        intro equal
        exact different (Subtype.ext (Sum.inr.inj ((vpres).injective equal)))
      obtain ⟨z, meetEntry, _⟩ := geometry.meet.operation.2 (ZFSet.pair x.val y.val)
        (ZFSet.pair_mem_prod.2 ⟨births.cutoff_subset n hx, births.cutoff_subset n hy⟩)
      refine ⟨z, (ZFSet.pair_mem_prod.1 (geometry.meet.operation.1 meetEntry)).2,
        pair_mem_graphRestriction.2 ⟨meetEntry, ZFSet.pair_mem_prod.2 ⟨hx, hy⟩⟩, ?_⟩
      exact data.externalOwnerLevels_meet_old_or_lower group oldAction pairing unions powers separation infinite hG hP0
        (selected x).1 (selected y).1 differentOwners x.property.2 y.property.2 meetEntry
  exact layer.restrictBirth cutoffMeet

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end OAI
