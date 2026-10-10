import OAI.SetTheory.PartitionPrinciple.Definability.AttachmentOldCodeLaws
import OAI.SetTheory.PartitionPrinciple.Forcing.SmallCodedMeetActions
import OAI.SetTheory.PartitionPrinciple.Transfinite.FinalInsertionStages

namespace OAI


namespace PartitionPilot.Forcing.NatUnionCode
universe u

theorem partialOrder {P r : Nat → ZFSet.{u}} {L R : ZFSet.{u}}
    (carrier : NatUnionCode P L) (relation : NatUnionCode r R)
    (orders : ∀ n, PartialOrderCode (P n) (r n))
    (relationMono : ∀ n m, n ≤ m → r n ⊆ r m) : PartialOrderCode L R := by
  constructor
  · intro z hz
    obtain ⟨n, hn⟩ := (relation z).1 hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 ((orders n).relation hn)
    exact ZFSet.pair_mem_prod.2 ⟨carrier.subset n hx, carrier.subset n hy⟩
  · intro x hx
    obtain ⟨n, hn⟩ := (carrier x).1 hx
    exact relation.subset n ((orders n).refl x hn)
  · intro x _ y _ xy yx
    obtain ⟨n, hn⟩ := (relation _).1 xy
    obtain ⟨m, hm⟩ := (relation _).1 yx
    have first := relationMono n (max n m) (le_max_left n m) hn
    have second := relationMono m (max n m) (le_max_right n m) hm
    have shape := ZFSet.pair_mem_prod.1 ((orders (max n m)).relation first)
    exact (orders (max n m)).antisymm x shape.1 y shape.2 first second
  · intro x _ y _ z _ xy yz
    obtain ⟨n, hn⟩ := (relation _).1 xy
    obtain ⟨m, hm⟩ := (relation _).1 yz
    have first := relationMono n (max n m) (le_max_left n m) hn
    have second := relationMono m (max n m) (le_max_right n m) hm
    have xyShape := ZFSet.pair_mem_prod.1 ((orders (max n m)).relation first)
    have yzShape := ZFSet.pair_mem_prod.1 ((orders (max n m)).relation second)
    exact relation.subset (max n m)
      ((orders (max n m)).trans x xyShape.1 y xyShape.2 z yzShape.2 first second)

theorem order_entry_iff {P r : Nat → ZFSet.{u}} {R : ZFSet.{u}}
    (relation : NatUnionCode r R)
    (relationMono : ∀ n m, n ≤ m → r n ⊆ r m)
    (oldOrder : ∀ n m, n ≤ m → ∀ x ∈ P n, ∀ y ∈ P n,
      ZFSet.pair x y ∈ r m ↔ ZFSet.pair x y ∈ r n)
    (n : Nat) {x y : ZFSet.{u}} (hx : x ∈ P n) (hy : y ∈ P n) :
    ZFSet.pair x y ∈ R ↔ ZFSet.pair x y ∈ r n := by
  constructor
  · intro entry
    obtain ⟨m, hm⟩ := (relation _).1 entry
    exact (oldOrder n (max n m) (le_max_left n m) x hx y hy).1
      (relationMono m _ (le_max_right n m) hm)
  · exact fun entry => relation.subset n entry

theorem meetOrder {P r μ : Nat → ZFSet.{u}} {L R M : ZFSet.{u}}
    (carrier : NatUnionCode P L) (relation : NatUnionCode r R) (operation : NatUnionCode μ M)
    (codes : ∀ n, MeetOrderCode (P n) (r n) (μ n))
    (carrierMono : ∀ n m, n ≤ m → P n ⊆ P m)
    (relationMono : ∀ n m, n ≤ m → r n ⊆ r m)
    (operationMono : ∀ n m, n ≤ m → μ n ⊆ μ m) : MeetOrderCode L R M := by
  refine ⟨carrier.partialOrder relation (fun n => (codes n).order) relationMono,
    (carrier.prod carrier carrierMono carrierMono).isFunc carrier operation
      (fun n => (codes n).operation) operationMono, ?_, ?_, ?_⟩
  · intro x y z entry
    obtain ⟨n, hn⟩ := (operation _).1 entry
    exact relation.subset n ((codes n).lower_left x y z hn)
  · intro x y z entry
    obtain ⟨n, hn⟩ := (operation _).1 entry
    exact relation.subset n ((codes n).lower_right x y z hn)
  · intro x y z w _ meet wx wy
    obtain ⟨n, hn⟩ := (operation _).1 meet
    obtain ⟨i, hi⟩ := (relation _).1 wx
    obtain ⟨j, hj⟩ := (relation _).1 wy
    let k := max n (max i j)
    have nk : n ≤ k := le_max_left n (max i j)
    have ik : i ≤ k := (le_max_left i j).trans (le_max_right n (max i j))
    have jk : j ≤ k := (le_max_right i j).trans (le_max_right n (max i j))
    have meetK := operationMono n k nk hn
    have wxK := relationMono i k ik hi
    have wyK := relationMono j k jk hj
    have wK := (ZFSet.pair_mem_prod.1 ((codes k).order.relation wxK)).1
    exact relation.subset k ((codes k).greatest x y z w wK meetK wxK wyK)

theorem meet_entry_iff {P r μ : Nat → ZFSet.{u}} {L R M : ZFSet.{u}}
    (operation : NatUnionCode μ M) (unionCode : MeetOrderCode L R M)
    (codes : ∀ n, MeetOrderCode (P n) (r n) (μ n))
    (n : Nat) {x y z : ZFSet.{u}} (hx : x ∈ P n) (hy : y ∈ P n) :
    ZFSet.pair (ZFSet.pair x y) z ∈ M ↔ ZFSet.pair (ZFSet.pair x y) z ∈ μ n :=
  operation.function_entry_iff unionCode.operation (fun n => (codes n).operation) n
    (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)

end PartitionPilot.Forcing.NatUnionCode



namespace PartitionPilot.Forcing
universe u v w

def CodedInsertionProfile (L r μ c e K F : ZFSet.{u}) : Prop :=
  ∀ x ∈ L, ZFSet.pair e x ∈ r →
    ((∃ f ∈ F, ZFSet.pair f x ∈ r) → ZFSet.pair K x ∈ r) ∧
    (¬ (∃ f ∈ F, ZFSet.pair f x ∈ r) → ZFSet.pair (ZFSet.pair K x) c ∈ μ)

theorem CodedInsertionProfile.iff_profile {L r μ c e K F : ZFSet.{u}}
    (meet : MeetOrderCode L r μ) (hc : c ∈ L) (he : e ∈ L) (hK : K ∈ L)
    (subset : F ⊆ L) :
    CodedInsertionProfile L r μ c e K F ↔
      Profile meet.toMeetOrder ⟨c, hc⟩ ⟨e, he⟩ ⟨K, hK⟩ (fun f => f.val ∈ F) := by
  have positive (x : {x : ZFSet.{u} // x ∈ L}) :
      Positive meet.toMeetOrder (fun f => f.val ∈ F) x ↔
        ∃ f ∈ F, ZFSet.pair f x.val ∈ r := by
    constructor
    · rintro ⟨f, hf, lower⟩
      exact ⟨f.val, hf, lower⟩
    · rintro ⟨f, hf, lower⟩
      exact ⟨⟨f, subset hf⟩, hf, lower⟩
  constructor
  · intro profile x above
    have inherited := profile x.val x.property above
    refine ⟨fun hx => inherited.1 ((positive x).1 hx), ?_⟩
    intro negative
    have entry := inherited.2 (fun hx => negative ((positive x).2 hx))
    apply Subtype.ext
    exact (show FunctionGraphOn (ZFSet.prod L L) μ from ⟨L, meet.operation⟩).unique
      (meet.toMeetOrder_meet_entry ⟨K, hK⟩ x) entry
  · intro profile x hx above
    have inherited := profile ⟨x, hx⟩ above
    refine ⟨fun positiveRaw => inherited.1 ((positive ⟨x, hx⟩).2 positiveRaw), ?_⟩
    intro negative
    have equal := inherited.2 (fun hp => negative ((positive ⟨x, hx⟩).1 hp))
    have entry := meet.toMeetOrder_meet_entry ⟨K, hK⟩ ⟨x, hx⟩
    rw [equal] at entry
    exact entry

namespace CodedTemplateAttachment
variable {J : Type v} {P r μ N inside shadow upper c e K F : ZFSet.{u}}
variable {old : MeetOrderCode P r μ} {b : Attachment.Templates.{u+1,w,v} old.toMeetOrder J}
variable (d : CodedTemplateAttachment old b N inside shadow upper)

theorem insertion_profile_persists (hc : c ∈ P) (he : e ∈ P) (hK : K ∈ P)
    (subset : F ⊆ P) (nonempty : ∃ f, f ∈ F)
    (profile : CodedInsertionProfile P r μ c e K F)
    (separated : ZFSet.pair e K ∉ r) :
    CodedInsertionProfile d.carrier d.order d.meetGraph c e K F := by
  have nonemptyTyped : ∃ f : {f : ZFSet.{u} // f ∈ P}, f.val ∈ F := by
    obtain ⟨f, hf⟩ := nonempty
    exact ⟨⟨f, subset hf⟩, hf⟩
  have inherited := b.persistence ⟨c, hc⟩ ⟨e, he⟩ ⟨K, hK⟩ (fun f => f.val ∈ F)
    nonemptyTyped ((CodedInsertionProfile.iff_profile old hc he hK subset).1 profile) separated
  intro x hx above
  obtain ⟨q, rfl⟩ := d.encode_surjective x hx
  have positive : (∃ f ∈ F, ZFSet.pair f (d.encode q) ∈ d.order) ↔
      PositiveOver b.oldEmbedding (fun f => f.val ∈ F) q := by
    constructor
    · rintro ⟨f, hf, lower⟩
      exact ⟨⟨f, subset hf⟩, hf, (d.le_encode (.inl ⟨f, subset hf⟩) q).1 lower⟩
    · rintro ⟨f, hf, lower⟩
      exact ⟨f.val, hf, (d.le_encode (.inl f) q).2 lower⟩
  have atPoint := inherited q ((d.le_encode (.inl ⟨e, he⟩) q).1 above)
  refine ⟨fun hp => (d.le_encode (.inl ⟨K, hK⟩) q).2 (atPoint.1 (positive.1 hp)), ?_⟩
  intro negative
  have equal := atPoint.2 (fun hp => negative (positive.2 hp))
  have entry := d.encoded_meet_entry (.inl ⟨K, hK⟩) q
  change b.extension.meet (.inl ⟨K, hK⟩) q = .inl ⟨c, hc⟩ at equal
  rw [equal] at entry
  exact entry

end CodedTemplateAttachment

theorem AttachmentBatchInputs.insertion_profile_persists
    {P r μ J Qs rs μs As Es Fs Ss c e K F : ZFSet.{u}}
    (d : AttachmentBatchInputs P r μ J Qs rs μs As Es Fs Ss)
    (hc : c ∈ P) (he : e ∈ P) (hK : K ∈ P)
    (subset : F ⊆ P) (nonempty : ∃ f, f ∈ F)
    (profile : CodedInsertionProfile P r μ c e K F)
    (separated : ZFSet.pair e K ∉ r) :
    CodedInsertionProfile d.batchCarrier d.batchOrder d.batchMeetGraph c e K F :=
  d.coding.insertion_profile_persists hc he hK subset nonempty profile separated

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

structure CodedCapProfile (L r μ c e K F : ZFSet.{u}) : Prop where
  target_mem : c ∈ L
  separator_mem : e ∈ L
  cap_mem : K ∈ L
  filter_subset : F ⊆ L
  nonempty : ∃ f, f ∈ F
  profile : CodedInsertionProfile L r μ c e K F
  target_below_cap : ZFSet.pair c K ∈ r
  cap_not_below_target : ZFSet.pair K c ∉ r
  separator_not_below_cap : ZFSet.pair e K ∉ r

def CodedCompressionProfiles (L r μ Caps Targets Separators Filters : ZFSet.{u}) : Prop :=
  ∀ i c e K F, ZFSet.pair i K ∈ Caps → ZFSet.pair i c ∈ Targets →
    ZFSet.pair i e ∈ Separators → ZFSet.pair i F ∈ Filters →
      CodedCapProfile L r μ c e K F

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.NatUnionCode
universe u

theorem insertionProfile {P r μ : Nat → ZFSet.{u}} {L R M c e K F : ZFSet.{u}}
    (relation : NatUnionCode r R) (operation : NatUnionCode μ M)
    (orders : ∀ n, PartialOrderCode (P n) (r n))
    (relationMono : ∀ n m, n ≤ m → r n ⊆ r m)
    (profiles : ∀ n, CodedInsertionProfile (P n) (r n) (μ n) c e K F) :
    CodedInsertionProfile L R M c e K F := by
  intro v _ above
  obtain ⟨n, aboveN⟩ := (relation _).1 above
  constructor
  · rintro ⟨f, hf, below⟩
    obtain ⟨m, belowM⟩ := (relation _).1 below
    have aboveCommon := relationMono n (max n m) (le_max_left n m) aboveN
    have belowCommon := relationMono m (max n m) (le_max_right n m) belowM
    have hv := (ZFSet.pair_mem_prod.1 ((orders (max n m)).relation aboveCommon)).2
    exact relation.subset (max n m)
      ((profiles (max n m) v hv aboveCommon).1 ⟨f, hf, belowCommon⟩)
  · intro negative
    have hv := (ZFSet.pair_mem_prod.1 ((orders n).relation aboveN)).2
    apply operation.subset n
    apply (profiles n v hv aboveN).2
    rintro ⟨f, hf, below⟩
    exact negative ⟨f, hf, relation.subset n below⟩

end PartitionPilot.Forcing.NatUnionCode


section

namespace PartitionPilot.Forcing.CodedInsertionProfile
universe u
variable {L r μ c e K F : ZFSet.{u}}

theorem cap_iff_positive (meet : MeetOrderCode L r μ)
    (profile : CodedInsertionProfile L r μ c e K F) (different : K ≠ c)
    {x : ZFSet.{u}} (hx : x ∈ L) (above : ZFSet.pair e x ∈ r) :
    ZFSet.pair K x ∈ r ↔ ∃ f ∈ F, ZFSet.pair f x ∈ r := by
  classical
  have cases := profile x hx above
  constructor
  · intro lower
    by_contra negative
    have entry := cases.2 negative
    have hK := (ZFSet.pair_mem_prod.1 (meet.order.relation lower)).1
    have hc := (ZFSet.pair_mem_prod.1 (meet.operation.1 entry)).2
    have capBelowBase := meet.greatest K x c K hK entry (meet.order.refl K hK) lower
    exact different (meet.order.antisymm K hK c hc capBelowBase (meet.lower_left K x c entry))
  · exact cases.1

theorem negative_incomparable (meet : MeetOrderCode L r μ)
    (profile : CodedInsertionProfile L r μ c e K F) (different : K ≠ c)
    (separated : ZFSet.pair e K ∉ r)
    {x : ZFSet.{u}} (hx : x ∈ L) (above : ZFSet.pair e x ∈ r)
    (negative : ¬ (∃ f ∈ F, ZFSet.pair f x ∈ r)) :
    ZFSet.pair K x ∉ r ∧ ZFSet.pair x K ∉ r ∧ ZFSet.pair (ZFSet.pair K x) c ∈ μ := by
  refine ⟨fun lower => negative ((cap_iff_positive meet profile different hx above).1 lower),
    ?_, (profile x hx above).2 negative⟩
  intro lower
  have he := (ZFSet.pair_mem_prod.1 (meet.order.relation above)).1
  have hK := (ZFSet.pair_mem_prod.1 (meet.order.relation lower)).2
  exact separated (meet.order.trans e he x hx K hK above lower)

end PartitionPilot.Forcing.CodedInsertionProfile

namespace PartitionPilot.Forcing.CodedCapProfile
universe u
variable {L r μ c e K F : ZFSet.{u}}

theorem cap_iff_positive (profile : CodedCapProfile L r μ c e K F)
    (meet : MeetOrderCode L r μ) {x : ZFSet.{u}} (hx : x ∈ L)
    (above : ZFSet.pair e x ∈ r) :
    ZFSet.pair K x ∈ r ↔ ∃ f ∈ F, ZFSet.pair f x ∈ r := by
  apply CodedInsertionProfile.cap_iff_positive meet profile.profile ?_ hx above
  intro equal
  apply profile.cap_not_below_target
  rw [equal]
  exact meet.order.refl c profile.target_mem

theorem negative_incomparable (profile : CodedCapProfile L r μ c e K F)
    (meet : MeetOrderCode L r μ) {x : ZFSet.{u}} (hx : x ∈ L)
    (above : ZFSet.pair e x ∈ r) (negative : ¬ (∃ f ∈ F, ZFSet.pair f x ∈ r)) :
    ZFSet.pair K x ∉ r ∧ ZFSet.pair x K ∉ r ∧ ZFSet.pair (ZFSet.pair K x) c ∈ μ := by
  apply CodedInsertionProfile.negative_incomparable meet profile.profile ?_
    profile.separator_not_below_cap hx above negative
  intro equal
  apply profile.cap_not_below_target
  rw [equal]
  exact meet.order.refl c profile.target_mem

end PartitionPilot.Forcing.CodedCapProfile

end


namespace PartitionPilot.Forcing
universe u

structure FinalInsertionFamiliesCode
    (Labels P G r μ A c e d F caps actors : ZFSet.{u}) : Prop where
  cap_injection : InjectionCode Labels P caps
  actor_injection : InjectionCode Labels G actors
  fixes : ∀ label k, ZFSet.pair label k ∈ actors →
    ∀ z ∈ P, ZFSet.pair z c ∈ r → ZFSet.pair (ZFSet.pair k z) z ∈ A
  dominates : ∀ label k cap, ZFSet.pair label k ∈ actors → ZFSet.pair label cap ∈ caps →
    ∀ y ∈ P, ZFSet.pair (ZFSet.pair k d) y ∈ A → ZFSet.pair y cap ∈ r
  profiles : ∀ label cap, ZFSet.pair label cap ∈ caps → CodedCapProfile P r μ c e cap F
  meets : ∀ first second cap₁ cap₂, ZFSet.pair first cap₁ ∈ caps →
    ZFSet.pair second cap₂ ∈ caps → first ≠ second → ZFSet.pair (ZFSet.pair cap₁ cap₂) c ∈ μ

namespace FinalInsertionFamiliesCode
variable {Labels P G r μ A c e d F caps actors : ZFSet.{u}}
variable (family : FinalInsertionFamiliesCode Labels P G r μ A c e d F caps actors)
include family

theorem tests (order : PartialOrderCode P r) (filter : MeetFilterCode P r μ F)
    {label cap v : ZFSet.{u}} (entry : ZFSet.pair label cap ∈ caps)
    (hv : v ∈ P) (above : ZFSet.pair e v ∈ r) :
    (v ∈ F → ZFSet.pair cap v ∈ r) ∧
      (v ∉ F → ZFSet.pair (ZFSet.pair cap v) c ∈ μ) := by
  have profile := (family.profiles label cap entry).profile v hv above
  refine ⟨fun member => profile.1 ⟨v, member, order.refl v hv⟩, ?_⟩
  intro negative
  apply profile.2
  rintro ⟨f, hf, lower⟩
  exact negative (filter.upward f hf v hv lower)

end FinalInsertionFamiliesCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.FinalInsertionFamiliesCode
open SetRealization
universe u
variable {Labels P G r μ A c e d F caps actors : ZFSet.{u}}

noncomputable def decodedCaps
    (family : FinalInsertionFamiliesCode Labels P G r μ A c e d F caps actors) :
    SetMembers Labels → SetMembers P :=
  (SetMembers.presentation Labels).decodeFunction (SetMembers.presentation P)
    caps family.cap_injection.function

noncomputable def decodedActors
    (family : FinalInsertionFamiliesCode Labels P G r μ A c e d F caps actors) :
    SetMembers Labels → SetMembers G :=
  (SetMembers.presentation Labels).decodeFunction (SetMembers.presentation G)
    actors family.actor_injection.function

theorem decodedCaps_entry
    (family : FinalInsertionFamiliesCode Labels P G r μ A c e d F caps actors)
    (label : SetMembers Labels) :
    ZFSet.pair (SetMembers.raw label) (SetMembers.raw (family.decodedCaps label)) ∈ caps :=
  (SetMembers.presentation Labels).decodeFunction_mem (SetMembers.presentation P)
    caps family.cap_injection.function label

theorem decodedActors_entry
    (family : FinalInsertionFamiliesCode Labels P G r μ A c e d F caps actors)
    (label : SetMembers Labels) :
    ZFSet.pair (SetMembers.raw label) (SetMembers.raw (family.decodedActors label)) ∈ actors :=
  (SetMembers.presentation Labels).decodeFunction_mem (SetMembers.presentation G)
    actors family.actor_injection.function label

theorem hasInsertionFamily {m inv one : ZFSet.{u}} {c e d : SetMembers P}
    (family : FinalInsertionFamiliesCode Labels P G r μ A
      (SetMembers.raw c) (SetMembers.raw e) (SetMembers.raw d) F caps actors)
    (group : GroupCode G m inv one) (meet : MeetOrderCode P r μ)
    (action : PosetActionCode G P m one r A) (filter : MeetFilterCode P r μ F) :
    letI := group.toGroup
    Compression.RecursiveMaps.HasInsertionFamily (action.toOrderAction group meet)
      (SetMembers Labels) c e d (fun x => SetMembers.raw x ∈ F) := by
  let := group.toGroup
  refine ⟨family.decodedCaps, family.decodedActors, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro label z lower
    apply (action.toOrderAction_eq_iff group meet (family.decodedActors label) z z).2
    exact family.fixes _ _ (family.decodedActors_entry label) _ (SetMembers.raw_mem z) lower
  · intro label
    exact family.dominates _ _ _ (family.decodedActors_entry label) (family.decodedCaps_entry label)
      _ (SetMembers.raw_mem _) (action.toOrderAction_entry group meet (family.decodedActors label) d)
  · intro label
    have profile := family.profiles _ _ (family.decodedCaps_entry label)
    exact ⟨profile.target_below_cap, profile.cap_not_below_target⟩
  · intro label
    exact (family.profiles _ _ (family.decodedCaps_entry label)).separator_not_below_cap
  · intro first second different
    apply (meet.toSmallMeetOrder_meet_eq_iff _ _ _).2
    exact family.meets _ _ _ _ (family.decodedCaps_entry first) (family.decodedCaps_entry second)
      (fun equal => different ((SetMembers.raw_injective Labels) equal))
  · intro label x above
    have tests := family.tests meet.order filter (family.decodedCaps_entry label)
      (SetMembers.raw_mem x) above
    exact ⟨tests.1, fun negative => (meet.toSmallMeetOrder_meet_eq_iff _ _ _).2 (tests.2 negative)⟩

end PartitionPilot.Forcing.FinalInsertionFamiliesCode



namespace PartitionPilot.Forcing
open SetFormula
universe u

private def capExceptionTest (profiles : Bool) (r c x cap : ZFSet.{u}) : Prop :=
  if profiles then c ∉ x ∧ cap ∈ x
  else ZFSet.pair x c ∉ r ∧ ZFSet.pair x cap ∈ r

private noncomputable def capExceptionRelation
    (profiles : Bool) (S Labels P r c caps : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ S, ∃ label ∈ Labels, ∃ cap ∈ P,
    z = ZFSet.pair x label ∧ ZFSet.pair label cap ∈ caps ∧
      capExceptionTest profiles r c x cap) (ZFSet.prod S Labels)

private theorem pair_mem_capExceptionRelation
    (profiles : Bool) (S Labels P r c caps x label : ZFSet.{u}) :
    ZFSet.pair x label ∈ capExceptionRelation profiles S Labels P r c caps ↔
      x ∈ S ∧ label ∈ Labels ∧ ∃ cap ∈ P, ZFSet.pair label cap ∈ caps ∧
        capExceptionTest profiles r c x cap := by
  rw [capExceptionRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y, hy, l, hl, cap, hcap, eq, entry, test⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hy, hl, cap, hcap, entry, test⟩
  · rintro ⟨hx, hl, cap, hcap, entry, test⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hl⟩, x, hx, label, hl, cap, hcap,
      rfl, entry, test⟩

private def capExceptionEntryFormula {n}
    (profiles : Bool) (z s labels p r c caps : Fin n) : BoundedFormula n :=
  BoundedFormula.exMem s (BoundedFormula.exMem labels.succ
    (BoundedFormula.exMem p.succ.succ
      (.conj (BoundedFormula.orderedPairFormula z.succ.succ.succ 2 1)
        (.conj (BoundedFormula.pairMembershipFormula 1 0 caps.succ.succ.succ)
          (if profiles then .conj (.neg (.mem c.succ.succ.succ 2)) (.mem 0 2)
          else .conj (.neg (BoundedFormula.pairMembershipFormula 2 c.succ.succ.succ r.succ.succ.succ))
            (BoundedFormula.pairMembershipFormula 2 0 r.succ.succ.succ))))))

private theorem truth_capExceptionEntryFormula {n}
    (profiles : Bool) (z s labels p r c caps : Fin n) (env : Fin n → ZFSet.{u}) :
    BoundedFormula.Truth (capExceptionEntryFormula profiles z s labels p r c caps) env ↔
      ∃ x ∈ env s, ∃ label ∈ env labels, ∃ cap ∈ env p,
        env z = ZFSet.pair x label ∧ ZFSet.pair label cap ∈ env caps ∧
          capExceptionTest profiles (env r) (env c) x cap := by
  cases profiles <;>
    simp only [capExceptionEntryFormula, capExceptionTest, Bool.false_eq_true, ↓reduceIte,
      BoundedFormula.truth_exMem, BoundedFormula.Truth,
      BoundedFormula.truth_orderedPairFormula, BoundedFormula.truth_pairMembershipFormula] <;> rfl

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

private theorem capExceptionRelation_mem
    (profiles : Bool) {S Labels P r c caps : ZFSet.{u}}
    (hS : S ∈ M.sets) (hLabels : Labels ∈ M.sets) (hP : P ∈ M.sets)
    (hr : r ∈ M.sets) (hc : c ∈ M.sets) (hCaps : caps ∈ M.sets) :
    capExceptionRelation profiles S Labels P r c caps ∈ M.sets := by
  let params := extend S (extend Labels (extend P (extend r (extend c (extend caps Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (capExceptionEntryFormula profiles 0 1 2 3 4 5 6) params
    (Fin.cases hS (Fin.cases hLabels (Fin.cases hP (Fin.cases hr
      (Fin.cases hc (Fin.cases hCaps (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hS hLabels)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (capExceptionEntryFormula profiles 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod S Labels) = capExceptionRelation profiles S Labels P r c caps := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, capExceptionRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (truth_capExceptionEntryFormula profiles 0 1 2 3 4 5 6 _)
  exact eq ▸ selected

private theorem partial_image_countable
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {S Labels rel : ZFSet.{u}} (hS : S ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (hRel : rel ∈ M.sets) (code : PartialFunctionCode S Labels rel)
    (smallS : M.groundEmbeddable S ZFSet.omega) :
    M.groundEmbeddable (relationImage S Labels rel) ZFSet.omega := by
  have hImage := M.relationImage_mem separation hS hLabels hRel
  have restricted : PartialFunctionCode S (relationImage S Labels rel) rel := by
    refine ⟨?_, code.unique⟩
    intro z hz
    obtain ⟨x, hx, label, hl, rfl⟩ := ZFSet.mem_prod.1 (code.shape hz)
    exact ZFSet.pair_mem_prod.2 ⟨hx, (mem_relationImage _ _ _ _).2 ⟨hl, x, hx, hz⟩⟩
  obtain ⟨f, hf, injection⟩ := M.groundEmbeddable_of_partial_surjection
    pairing unions powers separation choice hS hImage hRel restricted
    (fun label member => ((mem_relationImage _ _ _ label).1 member).2)
  obtain ⟨g, hg, count⟩ := smallS
  exact ⟨relationCompose (relationImage S Labels rel) S ZFSet.omega f g,
    M.relationCompose_mem pairing unions powers separation hImage hS
      (M.omega_mem separation infinite) hf hg, injection.compose count⟩
end TransitiveGround

namespace FinalInsertionFamiliesCode

theorem exists_ground_countable_exceptions
    {Labels P G r μ A c e d F caps actors Used Profiles extra : ZFSet.{u}}
    (family : FinalInsertionFamiliesCode Labels P G r μ A c e d F caps actors)
    (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hLabels : Labels ∈ M.sets) (hP : P ∈ M.sets) (hr : r ∈ M.sets)
    (hc : c ∈ M.sets) (hCaps : caps ∈ M.sets)
    (hUsed : Used ∈ M.sets) (hProfiles : Profiles ∈ M.sets) (hExtra : extra ∈ M.sets)
    (meet : MeetOrderCode P r μ) (usedSubset : Used ⊆ P)
    (filters : ∀ profile ∈ Profiles, MeetFilterCode P r μ profile)
    (smallUsed : M.groundEmbeddable Used ZFSet.omega)
    (smallProfiles : M.groundEmbeddable Profiles ZFSet.omega)
    (smallExtra : M.groundEmbeddable extra ZFSet.omega) (extraSubset : extra ⊆ Labels) :
    ∃ bad ∈ M.sets, bad ⊆ Labels ∧ M.groundEmbeddable bad ZFSet.omega ∧ extra ⊆ bad ∧
      ∀ label cap, ZFSet.pair label cap ∈ caps → label ∉ bad →
        (∀ node ∈ Used, ZFSet.pair node cap ∈ r → ZFSet.pair node c ∈ r) ∧
        (∀ profile ∈ Profiles, c ∉ profile → cap ∉ profile) := by
  classical
  let nodes := capExceptionRelation false Used Labels P r c caps
  let profiles := capExceptionRelation true Profiles Labels P r c caps
  have hNodes : nodes ∈ M.sets := M.capExceptionRelation_mem pairing unions powers separation
    false hUsed hLabels hP hr hc hCaps
  have hProfilesRel : profiles ∈ M.sets := M.capExceptionRelation_mem pairing unions powers separation
    true hProfiles hLabels hP hr hc hCaps
  have nodesPartial : PartialFunctionCode Used Labels nodes := by
    refine ⟨fun _ entry => (ZFSet.mem_sep.1 entry).1, ?_⟩
    intro node first second one two
    obtain ⟨used, _, cap₁, _, entry₁, negative, below₁⟩ :=
      (pair_mem_capExceptionRelation false Used Labels P r c caps node first).1 one
    obtain ⟨_, _, cap₂, _, entry₂, _, below₂⟩ :=
      (pair_mem_capExceptionRelation false Used Labels P r c caps node second).1 two
    by_contra different
    exact negative (meet.greatest cap₁ cap₂ c node (usedSubset used)
      (family.meets first second cap₁ cap₂ entry₁ entry₂ different) below₁ below₂)
  have profilesPartial : PartialFunctionCode Profiles Labels profiles := by
    refine ⟨fun _ entry => (ZFSet.mem_sep.1 entry).1, ?_⟩
    intro profile first second one two
    obtain ⟨used, _, cap₁, _, entry₁, negative, positive₁⟩ :=
      (pair_mem_capExceptionRelation true Profiles Labels P r c caps profile first).1 one
    obtain ⟨_, _, cap₂, _, entry₂, _, positive₂⟩ :=
      (pair_mem_capExceptionRelation true Profiles Labels P r c caps profile second).1 two
    by_contra different
    exact negative ((filters profile used).closed_meet cap₁ positive₁ cap₂ positive₂ c
      (family.meets first second cap₁ cap₂ entry₁ entry₂ different))
  let nodeBad := relationImage Used Labels nodes
  let profileBad := relationImage Profiles Labels profiles
  have hNodeBad : nodeBad ∈ M.sets := M.relationImage_mem separation hUsed hLabels hNodes
  have hProfileBad : profileBad ∈ M.sets := M.relationImage_mem separation hProfiles hLabels hProfilesRel
  have nodeSmall := M.partial_image_countable pairing unions powers separation infinite choice
    hUsed hLabels hNodes nodesPartial smallUsed
  have profileSmall := M.partial_image_countable pairing unions powers separation infinite choice
    hProfiles hLabels hProfilesRel profilesPartial smallProfiles
  have hBoth := M.binary_union_mem pairing unions hNodeBad hProfileBad
  have smallBoth := M.groundCountable_binary_union pairing unions powers separation infinite choice
    hNodeBad hProfileBad nodeSmall profileSmall
  refine ⟨(nodeBad ∪ profileBad) ∪ extra, M.binary_union_mem pairing unions hBoth hExtra, ?_,
    M.groundCountable_binary_union pairing unions powers separation infinite choice
      hBoth hExtra smallBoth smallExtra, ?_, ?_⟩
  · intro label member
    rcases ZFSet.mem_union.1 member with both | more
    · rcases ZFSet.mem_union.1 both with node | profile
      · exact ((mem_relationImage _ _ _ _).1 node).1
      · exact ((mem_relationImage _ _ _ _).1 profile).1
    · exact extraSubset more
  · intro label member
    exact ZFSet.mem_union.2 (Or.inr member)
  · intro label cap entry good
    have bounds := ZFSet.pair_mem_prod.1 (family.cap_injection.function.1 entry)
    constructor
    · intro node used below
      by_contra negative
      apply good
      apply ZFSet.mem_union.2 ∘ Or.inl
      apply ZFSet.mem_union.2 ∘ Or.inl
      exact (mem_relationImage _ _ _ _).2 ⟨bounds.1, node, used,
        (pair_mem_capExceptionRelation false Used Labels P r c caps node label).2
          ⟨used, bounds.1, cap, bounds.2, entry, negative, below⟩⟩
    · intro profile used negative positive
      apply good
      apply ZFSet.mem_union.2 ∘ Or.inl
      apply ZFSet.mem_union.2 ∘ Or.inr
      exact (mem_relationImage _ _ _ _).2 ⟨bounds.1, profile, used,
        (pair_mem_capExceptionRelation true Profiles Labels P r c caps profile label).2
          ⟨used, bounds.1, cap, bounds.2, entry, negative, positive⟩⟩

end FinalInsertionFamiliesCode
end PartitionPilot.Forcing

end OAI
