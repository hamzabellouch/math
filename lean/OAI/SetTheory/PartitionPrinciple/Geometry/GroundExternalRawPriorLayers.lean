import OAI.SetTheory.PartitionPrinciple.Definability.CodedLayerRestrictions
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundLayerWitnessPushforward
import OAI.SetTheory.PartitionPrinciple.Transfinite.ExternalChronologyStageLaws

namespace OAI

section

namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)

local notation "U" => completion.algebra.union.fields 0
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "E" => completion.externalIdentityCopyGraph P0 r0 μ0 A0

include births in
theorem priorFiber_image {t y : ZFSet.{u}}
    (oldTime : t ∈ oldTimes ∨ t = oldTimes) (born : ZFSet.pair y t ∈ births.birth) :
    ∃ x ∈ U, ZFSet.pair x y ∈ E := by
  rcases (pair_mem_ownerBirthGraph _ _ _ _ _ _ _ _).1 born with oldEntry | freshEntry
  · exact (mem_relationImage U B E y).1
      (ZFSet.pair_mem_prod.1 (births.seed_function.1 oldEntry)).1 |>.2
  · obtain ⟨_, _, _, n, hn, _, stamp⟩ := freshEntry
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    have later := compressionStamp_old_mem oldTime n
    rw [← (births.times.entries n t).1 stamp] at later
    exact (ZFSet.mem_irrefl t later).elim

include births data group action pairing unions powers separation infinite hG hP0

theorem rawPriorWitness {Qs rs μs t N z : ZFSet.{u}}
    (hQs : Qs ∈ M.sets) (hN : N ∈ M.sets) (hz : z ∈ M.sets)
    (code : GrowthLayerWitnessCode Qs rs μs U (completion.algebra.union.fields 1)
      (completion.algebra.union.fields 2) oldBirth t N z)
    (oldTime : t ∈ oldTimes ∨ t = oldTimes) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode Qs rs μs B
      (completion.externalPointOrder P0 r0 μ0 A0) (completion.externalPointMeet P0 r0 μ0 A0)
      births.birth t N z' := by
  have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP0
  have embedding := data.externalIdentityCopy_ideal group action pairing unions powers separation infinite hG
  apply code.ground_pushforward pairing unions powers separation (completion.algebra.union.ground 0)
    geometry.carrier_ground (geometry.copies_ground _ data.group.group_code.identity_mem)
    hQs hN hz completion.algebra.union.meet embedding.toMeetEmbeddingCode
  · exact fun x y a copied => births.preserves_seed x y a copied
  · exact fun _ _ entry => births.priorFiber_image oldTime entry

theorem rawCutoffPriorWitness {Qs rs μs t N z : ZFSet.{u}}
    (hQs : Qs ∈ M.sets) (hN : N ∈ M.sets) (hz : z ∈ M.sets)
    (code : GrowthLayerWitnessCode Qs rs μs U (completion.algebra.union.fields 1)
      (completion.algebra.union.fields 2) oldBirth t N z)
    (oldTime : t ∈ oldTimes ∨ t = oldTimes) (n : Nat) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode Qs rs μs (births.cutoff n)
      (births.cutoffOrder n) (births.cutoffMeet n) (births.cutoffBirth n) t N z' := by
  have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP0
  have embedding := data.externalIdentityCopy_ideal group action pairing unions powers separation infinite hG
  have contained : ∀ x y, ZFSet.pair x y ∈ E → y ∈ births.cutoff n := by
    intro x y copied
    have bounds := ZFSet.pair_mem_prod.1 (embedding.injection.function.1 copied)
    exact births.cutoff_old n ((mem_relationImage U B E y).2 ⟨bounds.2, x, bounds.1, copied⟩)
  have restricted := embedding.toMeetEmbeddingCode.restrictTarget (Q := births.cutoff n) contained
  have family := births.cutoffFamily_spec data group action pairing unions powers separation infinite hG hP0
  have hCut := M.pair_right (M.transitive family.1 ((family.2.2 n _).2 rfl))
  apply code.ground_pushforward pairing unions powers separation (completion.algebra.union.ground 0)
    hCut
    (geometry.copies_ground _ data.group.group_code.identity_mem) hQs hN hz
    completion.algebra.union.meet restricted
  · intro x y a copied
    change ZFSet.pair y a ∈ graphRestriction (births.cutoff n) births.birth ↔ _
    rw [pair_mem_graphRestriction]
    exact (and_iff_left (contained x y copied)).trans (births.preserves_seed x y a copied)
  · intro y _ entry
    exact births.priorFiber_image oldTime (pair_mem_graphRestriction.1 entry).1

end PartitionPilot.Forcing.GroundExternalBirthData

end

end OAI
