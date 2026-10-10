import OAI.SetTheory.PartitionPrinciple.Definability.ExternalStarCarrierRanks
import OAI.SetTheory.PartitionPrinciple.Transfinite.ExternalBirthLayerSeparation

namespace OAI



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

variable {HQs Hrs Hμs HTime : ZFSet.{u}}
variable (historySpaces : FunctionGraphOn HTime HQs)
variable (historyOrders : FunctionGraphOn HTime Hrs)
variable (historyMeets : FunctionGraphOn HTime Hμs)
variable (source : ZFSet.pair oldTimes (completion.algebra.union.fields 0) ∈ HQs ∧
  ZFSet.pair oldTimes (completion.algebra.union.fields 1) ∈ Hrs ∧
  ZFSet.pair oldTimes (completion.algebra.union.fields 2) ∈ Hμs)

include historySpaces historyOrders historyMeets source

theorem layerSeparatedCode (k : Nat) :
    SeparatedLayerCode HQs Hrs Hμs B (completion.externalPointOrder P0 r0 μ0 A0)
      (completion.externalPointMeet P0 r0 μ0 A0) births.birth (compressionStamp oldTimes k)
      (births.layerOwners k) (births.layerIndices k) (births.layerMaps k)
      (M.groundRelations U B) (births.layerComponents k) (births.layerFiber k) := by
  refine ⟨births.layerIndices_function k,
    (births.layerMaps_spec data group oldAction pairing unions powers separation infinite hG hP0 k).1,
    rfl, births.layerComponents_function data group oldAction pairing unions powers separation infinite hG hP0 k,
    ?_, ?_, ?_⟩
  · intro i _ t _ e Q R V indexEntry mapEntry spaceEntry orderEntry meetEntry
    obtain rfl := ((pair_mem_constantFamilyGraph _ _ _ _).1 indexEntry).2
    have qeq := historySpaces.unique spaceEntry source.1
    have req := historyOrders.unique orderEntry source.2.1
    have veq := historyMeets.unique meetEntry source.2.2
    subst Q R V
    exact births.layerMaps_embedding data group oldAction pairing unions powers separation infinite hG hP0 k mapEntry
  · intro i _ t _ e Q x _ indexEntry mapEntry spaceEntry componentEntry
    obtain rfl := ((pair_mem_constantFamilyGraph _ _ _ _).1 indexEntry).2
    have qeq := historySpaces.unique spaceEntry source.1
    subst Q
    have owned := (pair_mem_graphRestriction.1 componentEntry).1
    have hx := (pair_mem_graphRestriction.1 componentEntry).2
    obtain ⟨_, _, _, _, covered⟩ := births.layerMaps_copy data group oldAction pairing unions powers separation infinite hG hP0 k hx owned mapEntry
    exact covered
  · intro x hx y hy i _ j _ first second different
    exact Or.inl (births.layerComponents_earlier_meet data group oldAction pairing unions powers separation infinite hG hP0 k hx hy first second different)

theorem cutoffLayerSeparatedCode (k n : Nat) (before : k ≤ n) :
    SeparatedLayerCode HQs Hrs Hμs (births.cutoff n) (births.cutoffOrder n)
      (births.cutoffMeet n) (births.cutoffBirth n) (compressionStamp oldTimes k)
      (births.layerOwners k) (births.layerIndices k) (births.layerMaps k)
      (M.groundRelations U B) (births.layerComponents k) (births.layerFiber k) := by
  have full := births.layerSeparatedCode data group oldAction pairing unions powers separation infinite hG hP0
    historySpaces historyOrders historyMeets source k
  refine ⟨full.indices, full.maps, births.layerFiber_cutoff k n before, full.components, ?_, ?_, ?_⟩
  · intro i _ t _ e Q R V indexEntry mapEntry spaceEntry orderEntry meetEntry
    obtain rfl := ((pair_mem_constantFamilyGraph _ _ _ _).1 indexEntry).2
    have qeq := historySpaces.unique spaceEntry source.1
    have req := historyOrders.unique orderEntry source.2.1
    have veq := historyMeets.unique meetEntry source.2.2
    subst Q R V
    exact births.layerMaps_cutoff_embedding data group oldAction pairing unions powers separation infinite hG hP0 k n before mapEntry
  · intro i hi t ht e Q x hx indexEntry mapEntry spaceEntry componentEntry
    obtain ⟨_, u, hu, copied⟩ := (mem_relationImage _ _ _ _).1
      (full.cover i hi t ht e Q x (births.cutoff_subset n hx) indexEntry mapEntry spaceEntry componentEntry)
    exact (mem_relationImage _ _ _ _).2 ⟨hx, u, hu, copied⟩
  · intro x hx y hy i _ j _ first second different
    have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
    obtain ⟨z, a, meetEntry, born, earlier⟩ := births.layerComponents_earlier_meet data group oldAction pairing unions powers separation infinite hG hP0 k hx hy first second different
    have hxCut := ((mem_layerBirthFiber _ _ _ _).1 (births.layerFiber_cutoff k n before ▸ hx)).1
    have hyCut := ((mem_layerBirthFiber _ _ _ _).1 (births.layerFiber_cutoff k n before ▸ hy)).1
    have hz := (ZFSet.pair_mem_prod.1 (geometry.meet.operation.1 meetEntry)).2
    have hzCut := births.cutoff_lower data group oldAction pairing unions powers separation infinite hG hP0 n z hz x hxCut
      (geometry.meet.lower_left x y z meetEntry)
    exact Or.inl ⟨z, a, pair_mem_graphRestriction.2 ⟨meetEntry, ZFSet.pair_mem_prod.2 ⟨hxCut, hyCut⟩⟩,
      pair_mem_graphRestriction.2 ⟨born, hzCut⟩, earlier⟩

theorem layerWitness_spec (k : Nat) {N : ZFSet.{u}} :
    births.layerWitness k ∈ M.sets ∧
      GrowthLayerWitnessCode HQs Hrs Hμs B (completion.externalPointOrder P0 r0 μ0 A0)
        (completion.externalPointMeet P0 r0 μ0 A0) births.birth (compressionStamp oldTimes k) N
        (births.layerWitness k) :=
  ⟨births.layerWitness_ground data group oldAction pairing unions powers separation infinite hG hP0 k,
    Or.inr (Or.inr ⟨_, _, _, _, _, _, rfl,
      births.layerSeparatedCode data group oldAction pairing unions powers separation infinite hG hP0
        historySpaces historyOrders historyMeets source k⟩)⟩

theorem cutoffLayerWitness_spec (k n : Nat) (before : k ≤ n) {N : ZFSet.{u}} :
    births.layerWitness k ∈ M.sets ∧
      GrowthLayerWitnessCode HQs Hrs Hμs (births.cutoff n) (births.cutoffOrder n)
        (births.cutoffMeet n) (births.cutoffBirth n) (compressionStamp oldTimes k) N
        (births.layerWitness k) :=
  ⟨births.layerWitness_ground data group oldAction pairing unions powers separation infinite hG hP0 k,
    Or.inr (Or.inr ⟨_, _, _, _, _, _, rfl,
      births.cutoffLayerSeparatedCode data group oldAction pairing unions powers separation infinite hG hP0
        historySpaces historyOrders historyMeets source k n before⟩)⟩

end PartitionPilot.Forcing.GroundExternalBirthData



namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
variable (omega : ZFSet.rank ZFSet.omega < o) (indices : ZFSet.rank I < o)
variable (points : ZFSet.rank P0 < o) (actors : ZFSet.rank G < o)
variable (completed : ZFSet.rank (completion.algebra.union.fields 0) < o)
variable (time : ZFSet.rank oldTimes < o)
include data group action pairing unions powers separation infinite hG hP0
  limit omega indices points actors completed time

theorem layerWitness_rank_lt (k : Nat) : ZFSet.rank (births.layerWitness k) < o := by
  have carrier := completion.externalPointCarrier_rank_lt_of_inputs limit r0 μ0 A0
    omega indices points actors completed
  have vertices := M.externalStarVertices_rank_lt_of_inputs limit r0 μ0 A0 m one
    omega indices points actors
  have fiber := (ZFSet.rank_mono (fun x hx => (births.mem_layerFiber k x).1 hx |>.1)).trans_lt carrier
  have owners := (ZFSet.rank_mono (fun v hv => (births.layerOwners_cases (k := k) hv).1)).trans_lt vertices
  have bound := M.groundRelations_rank_lt limit completed carrier
  exact separatedLayerWitness_rank_lt limit owners
    (rank_constantFamilyGraph_lt limit owners time)
    (rank_functionGraph_lt limit
      (births.layerMaps_spec data group action pairing unions powers separation infinite hG hP0 k).1
      owners bound) bound
    (rank_functionGraph_lt limit
      (births.layerComponents_function data group action pairing unions powers separation infinite hG hP0 k)
      fiber owners) fiber

variable {HQs Hrs Hμs HTime : ZFSet.{u}}
variable (historySpaces : FunctionGraphOn HTime HQs)
variable (historyOrders : FunctionGraphOn HTime Hrs)
variable (historyMeets : FunctionGraphOn HTime Hμs)
variable (source : ZFSet.pair oldTimes (completion.algebra.union.fields 0) ∈ HQs ∧
  ZFSet.pair oldTimes (completion.algebra.union.fields 1) ∈ Hrs ∧
  ZFSet.pair oldTimes (completion.algebra.union.fields 2) ∈ Hμs)
include historySpaces historyOrders historyMeets source

theorem ranked_layerWitness_spec (k : Nat) {N : ZFSet.{u}} :
    births.layerWitness k ∈ M.sets ∧ ZFSet.rank (births.layerWitness k) < o ∧
      GrowthLayerWitnessCode HQs Hrs Hμs (completion.externalPointCarrier P0 r0 μ0 A0)
        (completion.externalPointOrder P0 r0 μ0 A0) (completion.externalPointMeet P0 r0 μ0 A0)
        births.birth (compressionStamp oldTimes k) N (births.layerWitness k) := by
  have code := births.layerWitness_spec data group action pairing unions powers separation infinite hG hP0
    historySpaces historyOrders historyMeets source k (N := N)
  exact ⟨code.1, births.layerWitness_rank_lt data group action pairing unions powers separation infinite
    hG hP0 limit omega indices points actors completed time k, code.2⟩

theorem ranked_cutoffLayerWitness_spec (k n : Nat) (before : k ≤ n) {N : ZFSet.{u}} :
    births.layerWitness k ∈ M.sets ∧ ZFSet.rank (births.layerWitness k) < o ∧
      GrowthLayerWitnessCode HQs Hrs Hμs (births.cutoff n) (births.cutoffOrder n)
        (births.cutoffMeet n) (births.cutoffBirth n) (compressionStamp oldTimes k) N
        (births.layerWitness k) := by
  have code := births.cutoffLayerWitness_spec data group action pairing unions powers separation infinite hG hP0
    historySpaces historyOrders historyMeets source k n before (N := N)
  exact ⟨code.1, births.layerWitness_rank_lt data group action pairing unions powers separation infinite
    hG hP0 limit omega indices points actors completed time k, code.2⟩

end PartitionPilot.Forcing.GroundExternalBirthData

end OAI
