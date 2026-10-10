import OAI.SetTheory.PartitionPrinciple.Forcing.GroundFixedTopTerminal
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalCutoffCoherence
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalCutoffLayers
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalProfilePreservation
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundInitialExternalBirths
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundTwoStageMainDiagram

namespace OAI


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
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
local notation "U" => completion.algebra.union.fields 0
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "r" => completion.externalPointOrder P0 r0 μ0 A0
local notation "μ" => completion.externalPointMeet P0 r0 μ0 A0
local notation "E" => completion.externalIdentityCopyGraph P0 r0 μ0 A0
local notation "levels" => completion.externalOwnerLevels P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG hP0 births

noncomputable def externalBirth_prior_layer
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}} {t : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet U
      (completion.algebra.union.fields 1) (completion.algebra.union.fields 2) oldBirth t)
    (groundSources : ∀ s ∈ t, Space s ∈ M.sets)
    (oldFunction : ZFSet.IsFunc U oldTimes oldBirth) (oldTime : t ∈ oldTimes ∨ t = oldTimes) :
    CodedGrowthLayer M Space sourceOrder sourceMeet B r μ births.birth t := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have embedding := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  apply layer.ownerBirth_pushforward pairing unions powers separation (completion.algebra.union.ground 0)
    geometry.carrier_ground (geometry.copies_ground _ data.group.group_code.identity_mem)
    (M.omega_mem separation infinite) groundSources completion.algebra.union.meet
    embedding.toMeetEmbeddingCode (fun _ hx => hx) oldFunction
  intro n a entry
  rw [(births.times.entries n a).1 entry]
  exact compressionStamp_old_mem oldTime n

noncomputable def externalBirth_cutoff_prior_layer
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}} {t : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet U
      (completion.algebra.union.fields 1) (completion.algebra.union.fields 2) oldBirth t)
    (groundSources : ∀ s ∈ t, Space s ∈ M.sets)
    (oldFunction : ZFSet.IsFunc U oldTimes oldBirth) (oldTime : t ∈ oldTimes ∨ t = oldTimes)
    (n : Nat) :
    CodedGrowthLayer M Space sourceOrder sourceMeet (births.cutoff n)
      (births.cutoffOrder n) (births.cutoffMeet n) (births.cutoffBirth n) t := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have embedding := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  have hQ := M.ownerLevelPrefix_mem pairing unions powers separation infinite
    (data.externalSeedCarrier_ground group oldAction pairing unions powers separation infinite hG hP0)
    geometry.carrier_ground
    (data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0).1
    (fun _ hx => (mem_relationImage _ _ _ _).1 hx |>.1) (natSetCode_mem_omega n)
  have restricted := embedding.toMeetEmbeddingCode.restrictTarget (Q := births.cutoff n) (by
    intro x y copied
    have bounds := ZFSet.pair_mem_prod.1 (embedding.injection.function.1 copied)
    exact births.cutoff_old n ((mem_relationImage _ _ _ _).2 ⟨bounds.2, x, bounds.1, copied⟩))
  have transported : CodedGrowthLayer M Space sourceOrder sourceMeet (births.cutoff n)
      (births.cutoffOrder n) (births.cutoffMeet n) births.birth t := by
    apply layer.ownerBirth_pushforward pairing unions powers separation (completion.algebra.union.ground 0)
      hQ (geometry.copies_ground _ data.group.group_code.identity_mem) (M.omega_mem separation infinite)
      groundSources completion.algebra.union.meet restricted (births.cutoff_subset n) oldFunction
    intro k a entry
    rw [(births.times.entries k a).1 entry]
    exact compressionStamp_old_mem oldTime k
  exact transported.restrictBirth
    (geometry.meet.restrict_lower (births.cutoff_subset n)
      (births.cutoff_lower data group oldAction pairing unions powers separation infinite hG hP0 n))

end PartitionPilot.Forcing.GroundExternalGeometryInputs



namespace PartitionPilot.Forcing
universe u

structure GroundChronologicalExternal (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
    (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 oldTimes oldBirth completion)
    (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 C D rD lo hi seed completion)
    (prior : GroundChronologicalHistory M T0 C D rD) where
  inputs : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion
  history : GroundChronologicalHistory M (insert births.limit births.limit) C D rD
  old_values : ∀ s, s ∈ oldTimes ∨ s = oldTimes →
    history.space s = prior.space s ∧ history.order s = prior.order s ∧
      history.meetGraph s = prior.meetGraph s ∧ history.birth s = prior.birth s ∧ history.height s = prior.height s
  stamp_values : ∀ n,
    history.space (compressionStamp oldTimes n) = births.cutoff n ∧
    history.order (compressionStamp oldTimes n) = births.cutoffOrder n ∧
    history.meetGraph (compressionStamp oldTimes n) = births.cutoffMeet n ∧
    history.birth (compressionStamp oldTimes n) = births.cutoffBirth n ∧
    history.height (compressionStamp oldTimes n) = births.cutoffHeight heights.height n
  limit_values :
    history.space births.limit = completion.externalPointCarrier P0 r0 μ0 A0 ∧
    history.order births.limit = completion.externalPointOrder P0 r0 μ0 A0 ∧
    history.meetGraph births.limit = completion.externalPointMeet P0 r0 μ0 A0 ∧
    history.birth births.limit = births.birth ∧ history.height births.limit = heights.height
  bounded_history : GroundChronologicalHistory M (insert births.limit births.limit) C D rD
  bounded_old_values : ∀ s ∈ births.limit,
    bounded_history.space s = history.space s ∧ bounded_history.order s = history.order s ∧
    bounded_history.meetGraph s = history.meetGraph s ∧ bounded_history.birth s = history.birth s ∧
    bounded_history.height s = history.height s
  bounded_values :
    bounded_history.space births.limit = completion.externalBoundedCarrier P0 r0 μ0 A0 ∧
    bounded_history.order births.limit = completion.externalBoundedOrder P0 r0 μ0 A0 ∧
    bounded_history.meetGraph births.limit = completion.externalBoundedMeet P0 r0 μ0 A0 ∧
    bounded_history.birth births.limit = births.boundedBirth ∧
    bounded_history.height births.limit = heights.boundedHeight

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (prior : GroundChronologicalHistory M T0 C D rD)

theorem chronologyFields_ground
    (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
    (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
    (ordinal : ordinalSetProperty T0) (hOld : oldTimes ∈ T0)
    {s : ZFSet.{u}} (cutoff : s ∈ insert births.limit births.limit) :
    let fields := births.chronologyFields heights prior
    fields.space s ∈ M.sets ∧ fields.order s ∈ M.sets ∧ fields.meetGraph s ∈ M.sets ∧
      fields.birth s ∈ M.sets ∧ fields.height s ∈ M.sets := by
  classical
  dsimp only
  by_cases before : s ∈ oldTimes ∨ s = oldTimes
  · have hs := before.elim (fun member => ordinal.1 oldTimes hOld s member)
      (fun equal => equal.symm ▸ hOld)
    obtain ⟨space, order, meet, birth, height⟩ := births.chronologyFields_old heights prior before
    rw [space, order, meet, birth, height]
    exact ⟨prior.space_mem s hs, prior.order_mem s hs, prior.meet_mem s hs,
      prior.birth_mem s hs, prior.height_mem s hs⟩
  · rcases ZFSet.mem_insert_iff.1 cutoff with rfl | below
    · obtain ⟨space, order, meet, birth, height⟩ := births.chronologyFields_limit heights prior
      rw [space, order, meet, birth, height]
      have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP0
      exact ⟨geometry.carrier_ground, geometry.order_ground, geometry.meet_ground,
        births.birth_ground, heights.height_ground⟩
    · have stamped : ∃ n, s = compressionStamp oldTimes n := by
        rcases (births.times.mem_limit_iff s).1 below with member | equal | stamped
        · exact False.elim (before (Or.inl member))
        · exact False.elim (before (Or.inr equal))
        · exact stamped
      obtain ⟨n, rfl⟩ := stamped
      obtain ⟨space, order, meet, birth, height⟩ := births.chronologyFields_stamp heights prior n
      rw [space, order, meet, birth, height]
      have fields := births.cutoff_fields data group action pairing unions powers separation infinite hG hP0 heights n
      exact ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2.1⟩

end PartitionPilot.Forcing.GroundExternalBirthData




namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (prior : GroundChronologicalHistory M T0 C D rD)
local notation "fields" => births.chronologyFields heights prior
local notation "U" => completion.algebra.union.fields 0

theorem chronology_sources_eq_below {t s : ZFSet.{u}}
    (oldTime : t ∈ oldTimes ∨ t = oldTimes) (before : s ∈ t) :
    (fields).space s = prior.space s ∧ (fields).order s = prior.order s ∧
      (fields).meetGraph s = prior.meetGraph s := by
  dsimp only [chronologyFields]
  exact ⟨compressionPrefixValue_eq_prior_below _ _ _ births.times oldTime before,
    compressionPrefixValue_eq_prior_below _ _ _ births.times oldTime before,
    compressionPrefixValue_eq_prior_below _ _ _ births.times oldTime before⟩

variable (ordinal : ordinalSetProperty T0) (hOldTimes : oldTimes ∈ T0)
include ordinal hOldTimes

noncomputable def chronology_old_layer {cutoff t : ZFSet.{u}}
    (oldCutoff : cutoff ∈ oldTimes ∨ cutoff = oldTimes) (bound : t = cutoff ∨ t ∈ cutoff) :
    CodedGrowthLayer M (fields).space (fields).order (fields).meetGraph
      ((fields).space cutoff) ((fields).order cutoff) ((fields).meetGraph cutoff) ((fields).birth cutoff) t := by
  have hc : cutoff ∈ T0 := oldCutoff.elim
    (fun member => ordinal.1 oldTimes hOldTimes cutoff member) (fun equal => equal.symm ▸ hOldTimes)
  have ht : t ∈ T0 := bound.elim (fun equal => equal.symm ▸ hc)
    (fun before => ordinal.1 cutoff hc t before)
  have oldTime : t ∈ oldTimes ∨ t = oldTimes := by
    rcases bound with equal | before
    · exact equal.symm ▸ oldCutoff
    · exact Or.inl (oldCutoff.elim
        (fun member => ordinal.2 oldTimes hOldTimes cutoff member t before) (fun equal => equal ▸ before))
  have layer := (prior.layer cutoff hc t ht bound).congr_sources_below
    (fun s hs => (births.chronology_sources_eq_below heights prior oldTime hs).1.symm)
    (fun s hs => (births.chronology_sources_eq_below heights prior oldTime hs).2.1.symm)
    (fun s hs => (births.chronology_sources_eq_below heights prior oldTime hs).2.2.symm)
  have values := births.chronologyFields_old heights prior oldCutoff
  simpa only [values.1, values.2.1, values.2.2.1, values.2.2.2.1] using layer

theorem chronology_sources_ground_below {t : ZFSet.{u}}
    (oldTime : t ∈ oldTimes ∨ t = oldTimes) : ∀ s ∈ t, (fields).space s ∈ M.sets := by
  intro s hs
  rw [(births.chronology_sources_eq_below heights prior oldTime hs).1]
  have ht : t ∈ T0 := oldTime.elim
    (fun member => ordinal.1 oldTimes hOldTimes t member) (fun equal => equal.symm ▸ hOldTimes)
  exact prior.space_mem s (ordinal.1 t ht s hs)

variable (priorSpace : prior.space oldTimes = completion.algebra.union.fields 0)
variable (priorOrder : prior.order oldTimes = completion.algebra.union.fields 1)
variable (priorMeet : prior.meetGraph oldTimes = completion.algebra.union.fields 2)
variable (priorBirth : prior.birth oldTimes = oldBirth)
include priorSpace priorOrder priorMeet priorBirth

noncomputable def chronology_base_layer (t : ZFSet.{u}) (oldTime : t ∈ oldTimes ∨ t = oldTimes) :
    CodedGrowthLayer M (fields).space (fields).order (fields).meetGraph U
      (completion.algebra.union.fields 1) (completion.algebra.union.fields 2) oldBirth t := by
  have layer := births.chronology_old_layer heights prior ordinal hOldTimes
    (Or.inr rfl : oldTimes ∈ oldTimes ∨ oldTimes = oldTimes) oldTime.symm
  have values := births.chronologyFields_old heights prior (Or.inr rfl : oldTimes ∈ oldTimes ∨ oldTimes = oldTimes)
  simpa only [values.1, values.2.1, values.2.2.1, values.2.2.2.1,
    priorSpace, priorOrder, priorMeet, priorBirth] using layer

variable {inv : ZFSet.{u}}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (oldFunction : ZFSet.IsFunc (completion.algebra.union.fields 0) oldTimes oldBirth)
include data group action pairing unions powers separation infinite hG hP0 oldFunction

noncomputable def chronology_finite_layers (n : Nat) (t : ZFSet.{u})
    (bound : t = compressionStamp oldTimes n ∨ t ∈ compressionStamp oldTimes n) :
    CodedGrowthLayer M (fields).space (fields).order (fields).meetGraph
      ((fields).space (compressionStamp oldTimes n)) ((fields).order (compressionStamp oldTimes n))
      ((fields).meetGraph (compressionStamp oldTimes n)) ((fields).birth (compressionStamp oldTimes n)) t := by
  have values := births.chronologyFields_stamp heights prior n
  rw [values.1, values.2.1, values.2.2.1, values.2.2.2.1]
  have atBase := births.chronologyFields_old heights prior (Or.inr rfl : oldTimes ∈ oldTimes ∨ oldTimes = oldTimes)
  have fresh (k : Nat) (before : k ≤ n) := data.externalBirth_cutoff_fresh_layer group action
    pairing unions powers separation infinite hG hP0 births (fields).space (fields).order (fields).meetGraph
    (atBase.1.trans priorSpace) (atBase.2.1.trans priorOrder) (atBase.2.2.1.trans priorMeet) k n before
  have original (s : ZFSet.{u}) (oldTime : s ∈ oldTimes ∨ s = oldTimes) :=
    data.externalBirth_cutoff_prior_layer group action pairing unions powers separation infinite hG hP0 births
      (births.chronology_base_layer heights prior ordinal hOldTimes priorSpace priorOrder priorMeet priorBirth s oldTime)
      (births.chronology_sources_ground_below heights prior ordinal hOldTimes oldTime) oldFunction oldTime n
  apply Classical.choice
  rcases bound with rfl | before
  · exact ⟨fresh n (Nat.le_refl n)⟩
  · rcases (mem_compressionStamp_iff oldTimes t n).1 before with old | same | ⟨k, earlier, rfl⟩
    · exact ⟨original t (Or.inl old)⟩
    · exact ⟨original t (Or.inr same)⟩
    · exact ⟨fresh k (Nat.le_of_lt earlier)⟩

noncomputable def chronology_union_layers (t : ZFSet.{u}) (bound : t = births.limit ∨ t ∈ births.limit) :
    CodedGrowthLayer M (fields).space (fields).order (fields).meetGraph
      ((fields).space births.limit) ((fields).order births.limit)
      ((fields).meetGraph births.limit) ((fields).birth births.limit) t := by
  have values := births.chronologyFields_limit heights prior
  rw [values.1, values.2.1, values.2.2.1, values.2.2.2.1]
  have atBase := births.chronologyFields_old heights prior (Or.inr rfl : oldTimes ∈ oldTimes ∨ oldTimes = oldTimes)
  have original (s : ZFSet.{u}) (oldTime : s ∈ oldTimes ∨ s = oldTimes) :=
    data.externalBirth_prior_layer group action pairing unions powers separation infinite hG hP0 births
      (births.chronology_base_layer heights prior ordinal hOldTimes priorSpace priorOrder priorMeet priorBirth s oldTime)
      (births.chronology_sources_ground_below heights prior ordinal hOldTimes oldTime) oldFunction oldTime
  apply Classical.choice
  rcases bound with rfl | before
  · exact ⟨.empty_of_no_birth ⟨births.limit, births.limit_ground⟩ (fun x _ => births.no_limit_birth x)⟩
  · rcases (births.times.mem_limit_iff t).1 before with old | same | ⟨k, rfl⟩
    · exact ⟨original t (Or.inl old)⟩
    · exact ⟨original t (Or.inr same)⟩
    · exact ⟨data.externalBirth_fresh_layer group action pairing unions powers separation infinite hG hP0 births
        (fields).space (fields).order (fields).meetGraph (atBase.1.trans priorSpace)
        (atBase.2.1.trans priorOrder) (atBase.2.2.1.trans priorMeet) k⟩

noncomputable def chronology_all_layers :
    ∀ cutoff ∈ insert births.limit births.limit, ∀ t ∈ insert births.limit births.limit,
      t = cutoff ∨ t ∈ cutoff → CodedGrowthLayer M (fields).space (fields).order (fields).meetGraph
        ((fields).space cutoff) ((fields).order cutoff) ((fields).meetGraph cutoff) ((fields).birth cutoff) t := by
  intro cutoff hc t _ bound
  apply Classical.choice
  rcases ZFSet.mem_insert_iff.1 hc with rfl | before
  · exact ⟨births.chronology_union_layers heights prior ordinal hOldTimes priorSpace priorOrder priorMeet priorBirth
      data group action pairing unions powers separation infinite hG hP0 oldFunction t bound⟩
  · rcases (births.times.mem_limit_iff cutoff).1 before with old | same | ⟨n, rfl⟩
    · exact ⟨births.chronology_old_layer heights prior ordinal hOldTimes (Or.inl old) bound⟩
    · exact ⟨births.chronology_old_layer heights prior ordinal hOldTimes (Or.inr same) bound⟩
    · exact ⟨births.chronology_finite_layers heights prior ordinal hOldTimes priorSpace priorOrder priorMeet priorBirth
        data group action pairing unions powers separation infinite hG hP0 oldFunction n t bound⟩

end PartitionPilot.Forcing.GroundExternalBirthData



namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 Filters C D rD lo hi seed : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (origin : GroundCompressionOrigin M initial P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (initialDomain : initial.D = P0) (initialOrder : initial.rD = r0)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (boundedHeights : GroundBoundedExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion heights)
variable (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
variable {b b' : ZFSet.{u}} (least : ∀ x ∈ P0, ZFSet.pair b x ∈ r0)
variable (image : ZFSet.pair b b' ∈ completion.externalOriginalEmbedding P0 r0 μ0 A0)
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)

noncomputable def externalMainStage : GroundMainStage M C D rD :=
  let geometry := data.externalBoundedGeometryData group action pairing unions powers separation infinite hG hP0
  let bottom := data.externalOriginalEmbedding_bottom origin group action pairing unions powers separation infinite
    hI hSources hReps hG hT hP0 initialDomain initialOrder least image
  { carrier := completion.externalBoundedCarrier P0 r0 μ0 A0
    order := completion.externalBoundedOrder P0 r0 μ0 A0
    meetGraph := completion.externalBoundedMeet P0 r0 μ0 A0
    actors := M.externalGroupCarrier G letters m one
    multiplication := M.externalGroupMultiplication G letters m one
    inverse := M.externalGroupInverse G letters m inv one
    identity := M.externalGroupIdentity G letters m one
    action := completion.externalBoundedAction P0 r0 μ0 A0
    bottom := b'
    top := completion.externalPointCarrier P0 r0 μ0 A0
    height := heights.boundedHeight
    carrier_ground := geometry.carrier_ground
    order_ground := geometry.order_ground
    meet_ground := geometry.meet_ground
    actors_ground := data.group.carrier_mem
    multiplication_ground := data.group.multiplication_mem
    inverse_ground := data.group.inverse_mem
    action_ground := geometry.action_ground
    height_ground := boundedHeights.height_ground
    columns_ground := hC
    coordinates_ground := hD
    coordinate_order_ground := hrD
    meet := geometry.meet
    group_code := data.group.group_code
    action_code := geometry.action
    bottom_mem := bottom.1
    least := bottom.2
    top_mem := geometry.top_mem
    greatest := geometry.greatest
    height_code := boundedHeights.code
    height_range_ground := boundedHeights.range_ground
    height_range_countable := boundedHeights.range_countable }

theorem externalMainStage_fields :
    let stage := data.externalMainStage origin group action pairing unions powers separation infinite
      hI hSources hReps hG hT hP0 initialDomain initialOrder heights boundedHeights hC hD hrD least image
    stage.carrier = completion.externalBoundedCarrier P0 r0 μ0 A0 ∧
    stage.order = completion.externalBoundedOrder P0 r0 μ0 A0 ∧
    stage.meetGraph = completion.externalBoundedMeet P0 r0 μ0 A0 ∧
    stage.actors = M.externalGroupCarrier G letters m one ∧
    stage.multiplication = M.externalGroupMultiplication G letters m one ∧
    stage.inverse = M.externalGroupInverse G letters m inv one ∧
    stage.identity = M.externalGroupIdentity G letters m one ∧
    stage.action = completion.externalBoundedAction P0 r0 μ0 A0 ∧
    stage.bottom = b' ∧ stage.top = completion.externalPointCarrier P0 r0 μ0 A0 ∧
    stage.height = heights.boundedHeight := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end GroundExternalGeometryInputs

namespace GroundChronologicalExternal
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 Filters : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable {births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion}
variable {heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion}
variable {prior : GroundChronologicalHistory M T0 C D rD}
variable (external : GroundChronologicalExternal M initial I Sources Reps G m inv one T τ
  P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 completion births heights prior)
variable (origin : GroundCompressionOrigin M initial P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (initialDomain : initial.D = P0) (initialOrder : initial.rD = r0)
variable (boundedHeights : GroundBoundedExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion heights)
variable (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
variable {b b' : ZFSet.{u}} (least : ∀ x ∈ P0, ZFSet.pair b x ∈ r0)
variable (image : ZFSet.pair b b' ∈ completion.externalOriginalEmbedding P0 r0 μ0 A0)

noncomputable def toMainStage : GroundChronologicalMainStage M C D rD where
  stage := external.inputs.externalMainStage origin group action pairing unions powers separation infinite
    hI hSources hReps hG hT hP0 initialDomain initialOrder heights boundedHeights hC hD hrD least image
  cutoff := births.limit
  cutoff_ground := births.limit_ground
  cutoff_ordinal := births.times.ordinal
  history := external.bounded_history
  carrier_eq := external.bounded_values.1
  order_eq := external.bounded_values.2.1
  meet_eq := external.bounded_values.2.2.1
  height_eq := external.bounded_values.2.2.2.2

theorem toMainStage_birth :
    (external.toMainStage origin group action pairing unions powers separation infinite hI hSources hReps
      hG hT hP0 initialDomain initialOrder boundedHeights hC hD hrD least image).birth = births.boundedBirth :=
  external.bounded_values.2.2.2.1

end GroundChronologicalExternal
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (prior : GroundChronologicalHistory M T0 C D rD)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (ordinal : ordinalSetProperty T0) (hOldTimes : oldTimes ∈ T0)
variable (priorSpace : prior.space oldTimes = completion.algebra.union.fields 0)
variable (priorOrder : prior.order oldTimes = completion.algebra.union.fields 1)
variable (priorMeet : prior.meetGraph oldTimes = completion.algebra.union.fields 2)
variable (priorBirth : prior.birth oldTimes = oldBirth)
variable (oldFunction : ZFSet.IsFunc (completion.algebra.union.fields 0) oldTimes oldBirth)

noncomputable def chronologyHistory :
    GroundChronologicalHistory M (insert births.limit births.limit) C D rD where
  space := (births.chronologyFields heights prior).space
  order := (births.chronologyFields heights prior).order
  meetGraph := (births.chronologyFields heights prior).meetGraph
  birth := (births.chronologyFields heights prior).birth
  height := (births.chronologyFields heights prior).height
  space_mem := fun _ hs => (births.chronologyFields_ground heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).1
  order_mem := fun _ hs => (births.chronologyFields_ground heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).2.1
  meet_mem := fun _ hs => (births.chronologyFields_ground heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).2.2.1
  birth_mem := fun _ hs => (births.chronologyFields_ground heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).2.2.2.1
  height_mem := fun _ hs => (births.chronologyFields_ground heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).2.2.2.2
  meet_order := fun _ hs => (births.chronologyFields_stage_laws heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).1
  birth_function := fun _ hs => (births.chronologyFields_stage_laws heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).2.1
  birth_bound := fun _ hs => (births.chronologyFields_stage_laws heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).2.2.1
  old_meet := fun _ hs => (births.chronologyFields_stage_laws heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).2.2.2.1
  strict_height := fun _ hs => (births.chronologyFields_stage_laws heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).2.2.2.2
  layer := births.chronology_all_layers heights prior ordinal hOldTimes priorSpace priorOrder priorMeet priorBirth
    data group action pairing unions powers separation infinite hG hP0 oldFunction

local notation "history" => births.chronologyHistory heights prior data group action
  pairing unions powers separation infinite hG hP0 ordinal hOldTimes
  priorSpace priorOrder priorMeet priorBirth oldFunction

theorem chronologyHistory_old {s : ZFSet.{u}} (before : s ∈ oldTimes ∨ s = oldTimes) :
    (history).space s = prior.space s ∧ (history).order s = prior.order s ∧
    (history).meetGraph s = prior.meetGraph s ∧ (history).birth s = prior.birth s ∧
    (history).height s = prior.height s := births.chronologyFields_old heights prior before

theorem chronologyHistory_stamp (n : Nat) :
    (history).space (compressionStamp oldTimes n) = births.cutoff n ∧
    (history).order (compressionStamp oldTimes n) = births.cutoffOrder n ∧
    (history).meetGraph (compressionStamp oldTimes n) = births.cutoffMeet n ∧
    (history).birth (compressionStamp oldTimes n) = births.cutoffBirth n ∧
    (history).height (compressionStamp oldTimes n) = births.cutoffHeight heights.height n :=
  births.chronologyFields_stamp heights prior n

theorem chronologyHistory_limit :
    (history).space births.limit = completion.externalPointCarrier P0 r0 μ0 A0 ∧
    (history).order births.limit = completion.externalPointOrder P0 r0 μ0 A0 ∧
    (history).meetGraph births.limit = completion.externalPointMeet P0 r0 μ0 A0 ∧
    (history).birth births.limit = births.birth ∧ (history).height births.limit = heights.height :=
  births.chronologyFields_limit heights prior

end PartitionPilot.Forcing.GroundExternalBirthData



namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (prior : GroundChronologicalHistory M T0 C D rD)

noncomputable def chronologicalData
    (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
    (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
    (ordinal : ordinalSetProperty T0) (hOldTimes : oldTimes ∈ T0)
    (priorSpace : prior.space oldTimes = completion.algebra.union.fields 0)
    (priorOrder : prior.order oldTimes = completion.algebra.union.fields 1)
    (priorMeet : prior.meetGraph oldTimes = completion.algebra.union.fields 2)
    (priorBirth : prior.birth oldTimes = oldBirth)
    (oldFunction : ZFSet.IsFunc (completion.algebra.union.fields 0) oldTimes oldBirth)
    (boundedHeights : GroundBoundedExternalHeightData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 C D rD lo hi seed completion heights) :
    GroundChronologicalExternal M initial I Sources Reps G m inv one T τ
      P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 completion births heights prior := by
  let history := births.chronologyHistory heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes
    priorSpace priorOrder priorMeet priorBirth oldFunction
  have terminal := births.chronologyFields_limit heights prior
  have space : history.space births.limit = completion.externalPointCarrier P0 r0 μ0 A0 := terminal.1
  have order : history.order births.limit = completion.externalPointOrder P0 r0 μ0 A0 := terminal.2.1
  have birth : history.birth births.limit = births.birth := terminal.2.2.2.1
  have earlier : ∀ x t, ZFSet.pair x t ∈ history.birth births.limit → t ∈ births.limit := by
    intro x t entry
    rw [birth] at entry
    exact (ZFSet.pair_mem_prod.1 (births.function.1 entry)).2
  have heightCode : StrictLexHeightCode (fixedTopCarrier (history.space births.limit)) C D
      (fixedTopOrder (history.space births.limit) (history.order births.limit)) heights.boundedHeight rD := by
    rw [space, order]
    exact boundedHeights.code
  let bounded := history.replaceTerminalFixedTop pairing unions powers separation births.times.ordinal
    births.limit_ground earlier heights.boundedHeight boundedHeights.height_ground heightCode
  refine ⟨data, history, (fun _ before => births.chronologyFields_old heights prior before),
    (fun n => births.chronologyFields_stamp heights prior n), terminal, bounded, ?_, ?_⟩
  · intro s hs
    exact history.replaceTerminalFixedTop_old pairing unions powers separation births.times.ordinal
      births.limit_ground earlier heights.boundedHeight boundedHeights.height_ground heightCode hs
  · have values := history.replaceTerminalFixedTop_terminal pairing unions powers separation births.times.ordinal
      births.limit_ground earlier heights.boundedHeight boundedHeights.height_ground heightCode
    rw [space, order, birth] at values
    exact values

end PartitionPilot.Forcing.GroundExternalBirthData



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "C" => M.groundOmegaOne pairing unions powers separation collection infinite

include choice in
theorem exists_groundInitialExternalChronology
    {P G r μ A Labels m inv one τ D rD c original base old T0 : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (hm : m ∈ M.sets) (hInv : inv ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P C D r original rD)
    (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) original) ZFSet.omega)
    (hBase : base ∈ M.sets) (prior : GroundChronologicalHistory M T0 C D rD)
    (ordinal : ordinalSetProperty T0) (baseMember : base ∈ T0)
    (priorSpace : prior.space base = P) (priorOrder : prior.order base = r)
    (priorMeet : prior.meetGraph base = μ) (priorBirth : prior.birth base = old)
    (priorHeight : prior.height base = original) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Filters := literalTaskFilterGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Targets := literalTaskTargetGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Separators := literalTaskSeparatorGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        ∃ _origin : GroundCompressionOrigin M (M.initialCompressionData P G r μ A Labels)
          P r μ A τ I Sources Reps G m inv one T Filters,
        ∃ compression : GroundChronologicalCompression M (M.initialCompressionData P G r μ A Labels)
          I Sources Reps G m one T τ P C D rD original Targets Separators Filters base old T0 prior,
          GroundExternalGeometryInputs M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m inv one T τ P r μ A compression.born.profiled.heighted.completion ∧
          GroundExternalGeometryData M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion ∧
          GroundExternalBoundedGeometryData M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion ∧
          ∃ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD ∧
            ∃ heights : GroundExternalHeightData M (M.initialCompressionData P G r μ A Labels)
              I Sources Reps G m one T τ P r μ A C D rD lo hi
              compression.born.profiled.heighted.heights.height compression.born.profiled.heighted.completion,
              GroundBoundedExternalHeightData M (M.initialCompressionData P G r μ A Labels)
                I Sources Reps G m one T τ P r μ A C D rD lo hi
                compression.born.profiled.heighted.heights.height compression.born.profiled.heighted.completion heights ∧
              ∃ births : GroundExternalBirthData M (M.initialCompressionData P G r μ A Labels)
                I Sources Reps G m one T τ P r μ A compression.born.births.limit compression.born.births.birth
                compression.born.profiled.heighted.completion,
                GroundBoundedExternalBirthData M (M.initialCompressionData P G r μ A Labels)
                  I Sources Reps G m one T τ P r μ A compression.born.births.limit compression.born.births.birth
                  compression.born.profiled.heighted.completion births ∧
                Nonempty (GroundChronologicalExternal M (M.initialCompressionData P G r μ A Labels)
                  I Sources Reps G m inv one T τ P r μ A compression.born.births.limit compression.born.births.birth
                  C D rD lo hi compression.born.profiled.heighted.heights.height
                  (insert compression.born.births.limit compression.born.births.limit)
                  compression.born.profiled.heighted.completion births heights compression.history) := by
  dsimp only
  obtain ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, data, geometry,
      boundedGeometry, lo, hlo, hi, hhi, gap, heights, boundedHeights, births, boundedBirths⟩ :=
    M.exists_groundInitialExternalBirths pairing unions powers separation collection infinite choice
      hP hG hr hμ hA hLabels hm hInv group action meet hτ top hD hrD hc hOriginal
      originalCode target above coordinateInjection originalSmall hBase prior ordinal baseMember
      priorSpace priorOrder priorMeet priorBirth priorHeight
  let chronological := births.chronologicalData heights compression.history data group action
    pairing unions powers separation infinite hG hP
    (ordinalSetProperty_succ compression.born.births.times.ordinal)
    (ZFSet.mem_insert_iff.2 (Or.inl rfl))
    compression.limit_values.1 compression.limit_values.2.1 compression.limit_values.2.2.1
    compression.limit_values.2.2.2.1 compression.born.births.function boundedHeights
  exact ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, data, geometry,
    boundedGeometry, lo, hlo, hi, hhi, gap, heights, boundedHeights, births, boundedBirths,
    ⟨chronological⟩⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
