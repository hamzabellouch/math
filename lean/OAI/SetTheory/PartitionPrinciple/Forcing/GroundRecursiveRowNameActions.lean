import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundRecursiveRefinementBinaryUnions

namespace OAI

namespace PartitionPilot.Forcing
universe u

theorem stageOneRawTests_empty (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    (lower : ZFSet.{u}) : stageOneRawTests M d ∅ lower :=
  ⟨fun _ _ _ _ _ _ member => False.elim (ZFSet.notMem_empty _ member),
    fun _ _ _ _ _ _ _ _ _ _ member _ => False.elim (ZFSet.notMem_empty _ member)⟩

theorem assignmentCut_empty_data (levels alpha : ZFSet.{u}) : assignmentCut levels alpha ∅ = ∅ :=
  assignmentCut_eq_of_lower (fun z member => False.elim (ZFSet.notMem_empty z member))

namespace RecursiveRefinementDataHistory
variable {M : TransitiveGround.{u}} {rows T stages history : ZFSet.{u}}

theorem empty_assignments (run : RecursiveRefinementDataHistory M rows T stages history)
    (ordinal : ordinalSetProperty stages) (hRows : rows ∈ M.sets)
    {row : ZFSet.{u}} (hrow : row ∈ rows) :
    ZFSet.pair row ∅ ∈ M.refinementHistoryForcing rows T stages history := by
  induction stages using ZFSet.inductionOn generalizing history with
  | h stages ih =>
    apply (M.mem_refinementHistoryForcing rows T stages history _).2
    refine ⟨M.stageOneCandidateBound_empty hRows hrow, ?_⟩
    intro beta hbeta
    obtain ⟨code, entry⟩ := run.data.function.total hbeta
    obtain ⟨d, rfl⟩ := run.data.decoded beta code entry
    refine ⟨refinementFormulaDataCode d, entry, ?_⟩
    rw [packedSuccessorConditionCode_code_iff, stageTwoConditionCode_pair_iff, assignmentCut_empty_data]
    have earlierOrdinal := ordinalSetProperty_member ordinal hbeta
    have earlier := ih beta hbeta (run.restrict earlierOrdinal (ordinal.1 beta hbeta)) earlierOrdinal
    exact ⟨(run.carrier beta d entry).symm ▸ earlier, stageOneRawTests_empty M d _⟩

end RecursiveRefinementDataHistory

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {R : Type u} (c : Presentation R)
variable {T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementDataHistory M c.carrier T stages history)
variable (ordinal : ordinalSetProperty stages) (carrier : c.carrier ∈ M.sets)
local notation "Q" => M.refinementHistoryForcing c.carrier T stages history
local notation "pres" => SetMembers.presentation Q

noncomputable def refinementHistoryRowInclusion (p : R) : SetMembers Q :=
  SetMembers.ofMem (ZFSet.pair (c.encode p) ∅)
    (run.empty_assignments ordinal carrier (c.encode_mem p))

local notation "incl" => M.refinementHistoryRowInclusion c run ordinal carrier

theorem refinementHistoryRowInclusion_encode (p : R) :
    (pres).encode (incl p) = c.pairEmpty.encode p :=
  SetMembers.raw_ofMem _ _

noncomputable def refinementHistoryRowNameLift (tau : Name c.pairEmpty) : Name (pres) :=
  Name.rename (pres) incl tau

local notation "liftName" => M.refinementHistoryRowNameLift c run ordinal carrier
include run ordinal carrier

theorem refinementHistoryRowNameLift_val (tau : Name c.pairEmpty) :
    (liftName tau).val = tau.val :=
  Name.rename_val_of_encode (pres) incl
    (M.refinementHistoryRowInclusion_encode c run ordinal carrier) tau

theorem refinementHistoryRowNameFamily_valid (X : ZFSet.{u})
    (valid : ∀ z ∈ X, IsName c.pairEmpty z) :
    ∀ z ∈ X, IsName (pres) z := by
  intro z hz
  have lifted := (liftName ⟨z, valid z hz⟩).property
  exact (congrArg (IsName (pres))
    (M.refinementHistoryRowNameLift_val c run ordinal carrier ⟨z, valid z hz⟩)).mp lifted

theorem refinementHistoryRowNameFamily_eq (X : ZFSet.{u})
    (valid : ∀ z ∈ X, IsName c.pairEmpty z) :
    Name.renamedFamily (pres) incl X valid = X := by
  apply ZFSet.ext
  intro z
  rw [Name.mem_renamedFamily]
  constructor
  · rintro ⟨tau, member, equal⟩
    have codes := M.refinementHistoryRowNameLift_val c run ordinal carrier tau
    exact (equal.trans codes).symm ▸ member
  · intro member
    exact ⟨⟨z, valid z member⟩, member,
      (M.refinementHistoryRowNameLift_val c run ordinal carrier ⟨z, valid z member⟩).symm⟩

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {R : Type u} (c : Presentation R)
variable {T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementDataHistory M c.carrier T stages history)
variable (ordinal : ordinalSetProperty stages) (carrier : c.carrier ∈ M.sets)
local notation "Q" => M.refinementHistoryForcing c.carrier T stages history
local notation "pres" => SetMembers.presentation Q
local notation "incl" => M.refinementHistoryRowInclusion c run ordinal carrier
local notation "liftName" => M.refinementHistoryRowNameLift c run ordinal carrier
variable {G : Type v} [Group G] [PartialOrder R]
variable [PartialOrder (SetMembers (M.refinementHistoryForcing c.carrier T stages history))]
variable (a : PosetAction G R)
variable (e : PosetAction G (SetMembers (M.refinementHistoryForcing c.carrier T stages history)))
variable (image : G → ZFSet.{u} → ZFSet.{u})
variable (coordinates : ∀ (g : G)
  (q : SetMembers (M.refinementHistoryForcing c.carrier T stages history)) (row : R) (A : ZFSet.{u}),
  SetMembers.raw q = ZFSet.pair (c.encode row) A →
  SetMembers.raw (e.iso g q) = ZFSet.pair (c.encode (a.iso g row)) (image g A))
variable (emptyImage : ∀ g, image g ∅ = ∅)
include run ordinal carrier coordinates emptyImage

theorem refinementHistoryRowInclusion_equivariant (g : G) (p : R) :
    e.iso g (incl p) = incl (a.iso g p) := by
  apply SetMembers.raw_injective Q
  have encoded := M.refinementHistoryRowInclusion_encode c run ordinal carrier p
  change SetMembers.raw (incl p) = ZFSet.pair (c.encode p) ∅ at encoded
  rw [coordinates g (incl p) p ∅ encoded, emptyImage]
  exact (M.refinementHistoryRowInclusion_encode c run ordinal carrier (a.iso g p)).symm

theorem refinementHistoryRowNameLift_act (g : G) (tau : Name c.pairEmpty) :
    e.act (pres) g (liftName tau) = liftName (a.act c.pairEmpty g tau) :=
  a.act_rename_of_equivariant e c.pairEmpty (pres) incl
    (fun g p => (M.refinementHistoryRowInclusion_equivariant c run ordinal carrier
      a e image coordinates emptyImage g p).symm) g tau

theorem refinementHistoryRowNameLift_stabilizer (tau : Name c.pairEmpty) :
    e.stabilizer (pres) (liftName tau) = a.stabilizer c.pairEmpty tau := by
  apply Subgroup.ext
  intro g
  change e.act (pres) g (liftName tau) = liftName tau ↔ a.act c.pairEmpty g tau = tau
  rw [M.refinementHistoryRowNameLift_act c run ordinal carrier a e image coordinates emptyImage]
  constructor
  · intro equal
    apply Subtype.ext
    have codes := congrArg Subtype.val equal
    simpa only [M.refinementHistoryRowNameLift_val c run ordinal carrier] using codes
  · intro equal
    exact congrArg liftName equal

theorem refinementHistoryRowNameLift_supported (K : Subgroup G) (tau : Name c.pairEmpty)
    (supported : K ≤ a.stabilizer c.pairEmpty tau) :
    K ≤ e.stabilizer (pres) (liftName tau) := by
  rw [M.refinementHistoryRowNameLift_stabilizer c run ordinal carrier a e image coordinates emptyImage]
  exact supported

theorem refinementHistoryRowNameLift_hs (F : NormalSubgroupFamily G) (tau : Name c.pairEmpty)
    (hs : HereditarilySymmetric a c.pairEmpty F tau) :
    HereditarilySymmetric e (pres) F (liftName tau) :=
  hs.rename e (pres) incl
    (fun g p => (M.refinementHistoryRowInclusion_equivariant c run ordinal carrier
      a e image coordinates emptyImage g p).symm)

theorem refinementHistoryRowNameFamily_transport (F : NormalSubgroupFamily G) (X : ZFSet.{u})
    (valid : ∀ z ∈ X, IsName c.pairEmpty z)
    (closed : ∀ g (tau : Name c.pairEmpty), tau.val ∈ X → (a.act c.pairEmpty g tau).val ∈ X)
    (symmetric : ∀ tau : Name c.pairEmpty, tau.val ∈ X → HereditarilySymmetric a c.pairEmpty F tau) :
    (∀ z ∈ X, IsName (pres) z) ∧
      (∀ g (tau : Name (pres)), tau.val ∈ X → (e.act (pres) g tau).val ∈ X) ∧
      (∀ tau : Name (pres), tau.val ∈ X → HereditarilySymmetric e (pres) F tau) := by
  refine ⟨M.refinementHistoryRowNameFamily_valid c run ordinal carrier X valid, ?_, ?_⟩
  · intro g tau member
    let sigma : Name c.pairEmpty := ⟨tau.val, valid tau.val member⟩
    have same : liftName sigma = tau := Subtype.ext
      (M.refinementHistoryRowNameLift_val c run ordinal carrier sigma)
    rw [← same, M.refinementHistoryRowNameLift_act c run ordinal carrier a e image coordinates emptyImage,
      M.refinementHistoryRowNameLift_val c run ordinal carrier]
    exact closed g sigma member
  · intro tau member
    let sigma : Name c.pairEmpty := ⟨tau.val, valid tau.val member⟩
    have same : liftName sigma = tau := Subtype.ext
      (M.refinementHistoryRowNameLift_val c run ordinal carrier sigma)
    rw [← same]
    exact M.refinementHistoryRowNameLift_hs c run ordinal carrier a e image coordinates emptyImage
      F sigma (symmetric sigma member)

end PartitionPilot.Forcing.TransitiveGround

end OAI
