import OAI.SetTheory.PartitionPrinciple.Geometry.GroundFinalInsertionExceptions
import OAI.SetTheory.PartitionPrinciple.Geometry.GrowthLayerSourceCongruence

namespace OAI

namespace PartitionPilot.Forcing

namespace NatUnionCode
universe u

theorem oldMeet {r μ birth : Nat → ZFSet.{u}} {R MU B : ZFSet.{u}}
    (relation : NatUnionCode r R) (operation : NatUnionCode μ MU)
    (born : NatUnionCode birth B)
    (laws : ∀ n, OldMeetCode (r n) (μ n) (birth n))
    (operationMono : ∀ n m, n ≤ m → μ n ⊆ μ m)
    (birthMono : ∀ n m, n ≤ m → birth n ⊆ birth m) : OldMeetCode R MU B := by
  intro x y z a b c ya xb ab notLower xy zc
  obtain ⟨i, hi⟩ := (born _).1 ya
  obtain ⟨j, hj⟩ := (born _).1 xb
  obtain ⟨k, hk⟩ := (operation _).1 xy
  obtain ⟨l, hl⟩ := (born _).1 zc
  let n := max (max i j) (max k l)
  have iN : i ≤ n := (le_max_left i j).trans (le_max_left (max i j) (max k l))
  have jN : j ≤ n := (le_max_right i j).trans (le_max_left (max i j) (max k l))
  have kN : k ≤ n := (le_max_left k l).trans (le_max_right (max i j) (max k l))
  have lN : l ≤ n := (le_max_right k l).trans (le_max_right (max i j) (max k l))
  exact laws n x y z a b c (birthMono i n iN hi) (birthMono j n jN hj) ab
    (fun lower => notLower (relation.subset n lower)) (operationMono k n kN hk)
    (birthMono l n lN hl)

theorem birth_bound {birth : Nat → ZFSet.{u}} {B cutoff : ZFSet.{u}}
    (born : NatUnionCode birth B)
    (bounds : ∀ n x t, ZFSet.pair x t ∈ birth n → t ∈ cutoff) :
    ∀ x t, ZFSet.pair x t ∈ B → t ∈ cutoff := by
  intro x t entry
  obtain ⟨n, hn⟩ := (born _).1 entry
  exact bounds n x t hn

theorem no_birth_at_bound {birth : Nat → ZFSet.{u}} {B cutoff : ZFSet.{u}}
    (born : NatUnionCode birth B)
    (bounds : ∀ n x t, ZFSet.pair x t ∈ birth n → t ∈ cutoff) :
    ∀ x, ZFSet.pair x cutoff ∉ B := by
  intro x entry
  exact ZFSet.mem_irrefl cutoff (born.birth_bound bounds x cutoff entry)

theorem stable_birth_entry_iff {birth : Nat → ZFSet.{u}} {B t : ZFSet.{u}}
    (born : NatUnionCode birth B) (n : Nat)
    (stable : ∀ m x, ZFSet.pair x t ∈ birth m → ZFSet.pair x t ∈ birth n)
    (x : ZFSet.{u}) : ZFSet.pair x t ∈ B ↔ ZFSet.pair x t ∈ birth n := by
  constructor
  · intro entry
    obtain ⟨m, hm⟩ := (born _).1 entry
    exact stable m x hm
  · exact fun entry => born.subset n entry

theorem stable_birth_fiber {P birth : Nat → ZFSet.{u}} {B t T : ZFSet.{u}}
    (born : NatUnionCode birth B) (n : Nat) (function : ZFSet.IsFunc (P n) T (birth n))
    (stable : ∀ m x, ZFSet.pair x t ∈ birth m → ZFSet.pair x t ∈ birth n) :
    ∀ x, ZFSet.pair x t ∈ B → x ∈ P n ∧ ZFSet.pair x t ∈ birth n := by
  intro x entry
  have old := (born.stable_birth_entry_iff n stable x).1 entry
  exact ⟨(ZFSet.pair_mem_prod.1 (function.1 old)).1, old⟩

end NatUnionCode

section

universe u

theorem MeetEmbeddingCode.enlarge_target
    {A L L' rA r r' μA μ μ' e : ZFSet.{u}}
    (embedding : MeetEmbeddingCode A L rA r μA μ e)
    (carrier : L ⊆ L') (order : r ⊆ r') (meets : μ ⊆ μ') :
    MeetEmbeddingCode A L' rA r' μA μ' e := by
  refine ⟨⟨⟨?_, embedding.injection.function.2⟩, embedding.injection.injective⟩,
    fun x y x' y' below first second => order (embedding.monotone x y x' y' below first second),
    fun x y z x' y' z' meet first second third =>
      meets (embedding.map_meet x y z x' y' z' meet first second third)⟩
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (embedding.injection.function.1 hz)
  exact ZFSet.pair_mem_prod.2 ⟨hx, carrier hy⟩

theorem relationImage_enlarge_target {A L L' e : ZFSet.{u}} (carrier : L ⊆ L') :
    relationImage A L e ⊆ relationImage A L' e := by
  intro x hx
  obtain ⟨hxL, witness⟩ := (mem_relationImage A L e x).1 hx
  exact (mem_relationImage A L' e x).2 ⟨carrier hxL, witness⟩

theorem OldBridgeCode.of_literal_extension
    {L L' r r' μ μ' birth birth' t x y : ZFSet.{u}}
    (bridge : OldBridgeCode L r μ birth t x y)
    (carrier : L ⊆ L') (order : r ⊆ r') (meets : μ ⊆ μ') (born : birth ⊆ birth') :
    OldBridgeCode L' r' μ' birth' t x y := by
  rcases bridge with ⟨z, a, meet, entry, earlier⟩ | ⟨z, hz, a, entry, earlier, between⟩
  · exact Or.inl ⟨z, a, meets meet, born entry, earlier⟩
  · exact Or.inr ⟨z, carrier hz, a, born entry, earlier,
      between.elim (fun h => Or.inl ⟨order h.1, order h.2⟩)
        (fun h => Or.inr ⟨order h.1, order h.2⟩)⟩

def CodedGrowthLayer.of_literal_extension
    {M : TransitiveGround.{u}} {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {L L' r r' μ μ' birth birth' t : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t)
    (separation : SetFormula.SeparationSchema M.sets) (hL : L ∈ M.sets)
    (carrier : L ⊆ L') (order : r ⊆ r') (meets : μ ⊆ μ') (born : birth ⊆ birth')
    (fiber : ∀ x ∈ L', ZFSet.pair x t ∈ birth' → x ∈ L ∧ ZFSet.pair x t ∈ birth) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L' r' μ' birth' t := by
  cases layer with
  | countablePoints D ground small cover =>
    exact .countablePoints D ground small (fun x hx entry =>
      cover x (fiber x hx entry).1 (fiber x hx entry).2)
  | copies I parts groundI small groundParts index e earlier groundCopy embedding cover inCopy =>
    let retained := ZFSet.sep (fun z => z ∈ ZFSet.prod I L) parts
    refine .copies I retained groundI small
      (M.injection_restriction_mem separation groundI hL groundParts) index e earlier groundCopy
      (fun i hi => (embedding i hi).enlarge_target carrier order meets)
      ?_ ?_
    · intro x hx entry
      have old := fiber x hx entry
      obtain ⟨i, hi, part⟩ := cover x old.1 old.2
      exact ⟨i, hi, ZFSet.mem_sep.2 ⟨part, ZFSet.pair_mem_prod.2 ⟨hi, old.1⟩⟩⟩
    · intro i hi x _ entry
      obtain ⟨part, bound⟩ := ZFSet.mem_sep.1 entry
      have hxL := (ZFSet.pair_mem_prod.1 bound).2
      exact relationImage_enlarge_target carrier (inCopy i hi x hxL part)
  | separated I index e earlier groundCopy embedding component cover separated =>
    let oldPoint (x : {x : ZFSet.{u} // x ∈ L' ∧ ZFSet.pair x t ∈ birth'}) :
        {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth} :=
      ⟨x.val, fiber x.val x.property.1 x.property.2⟩
    exact .separated I index e earlier groundCopy
      (fun i => (embedding i).enlarge_target carrier order meets)
      (fun x => component (oldPoint x))
      (fun x => relationImage_enlarge_target carrier (cover (oldPoint x)))
      (fun x y different => (separated (oldPoint x) (oldPoint y) different).of_literal_extension
        carrier order meets born)

noncomputable def fixedTopBirth (P birth s : ZFSet.{u}) : ZFSet.{u} :=
  insert (ZFSet.pair P s) birth

theorem pair_mem_fixedTopBirth (P birth s x t : ZFSet.{u}) :
    ZFSet.pair x t ∈ fixedTopBirth P birth s ↔
      (x = P ∧ t = s) ∨ ZFSet.pair x t ∈ birth := by
  rw [fixedTopBirth, ZFSet.mem_insert_iff, ZFSet.pair_inj]

theorem fixedTopBirth_subset (P birth s : ZFSet.{u}) : birth ⊆ fixedTopBirth P birth s :=
  fun _ h => ZFSet.mem_insert_iff.2 (Or.inr h)

theorem fixedTopBirth_old_iff {P birth s x t : ZFSet.{u}} (hx : x ∈ P) :
    ZFSet.pair x t ∈ fixedTopBirth P birth s ↔ ZFSet.pair x t ∈ birth := by
  rw [pair_mem_fixedTopBirth]
  exact ⟨fun h => h.elim (fun equal => False.elim (ZFSet.mem_irrefl P (equal.1 ▸ hx))) id,
    Or.inr⟩

theorem fixedTopBirth_top_iff {P T birth s t : ZFSet.{u}} (born : ZFSet.IsFunc P T birth) :
    ZFSet.pair P t ∈ fixedTopBirth P birth s ↔ t = s := by
  rw [pair_mem_fixedTopBirth]
  exact ⟨fun h => h.elim And.right (fun entry =>
    False.elim (ZFSet.mem_irrefl P (ZFSet.pair_mem_prod.1 (born.1 entry)).1)),
    fun equal => Or.inl ⟨rfl, equal⟩⟩

theorem fixedTopBirth_function {P T birth s : ZFSet.{u}}
    (born : ZFSet.IsFunc P T birth) (hs : s ∈ T) :
    ZFSet.IsFunc (fixedTopCarrier P) T (fixedTopBirth P birth s) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.1 hz with rfl | old
    · exact ZFSet.pair_mem_prod.2 ⟨fixedTopCarrier_top P, hs⟩
    · obtain ⟨x, hx, t, ht, rfl⟩ := ZFSet.mem_prod.1 (born.1 old)
      exact ZFSet.pair_mem_prod.2 ⟨fixedTopCarrier_old hx, ht⟩
  · intro x hx
    rcases (mem_fixedTopCarrier P x).1 hx with rfl | old
    · exact ⟨s, (fixedTopBirth_top_iff born).2 rfl, fun t entry => (fixedTopBirth_top_iff born).1 entry⟩
    · obtain ⟨t, entry, unique⟩ := born.2 x old
      exact ⟨t, (fixedTopBirth_old_iff old).2 entry,
        fun t' entry' => unique t' ((fixedTopBirth_old_iff old).1 entry')⟩

theorem fixedTopBirth_bound {P birth s : ZFSet.{u}}
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ s) :
    ∀ x t, ZFSet.pair x t ∈ fixedTopBirth P birth s → t = s ∨ t ∈ s := by
  intro x t entry
  exact ((pair_mem_fixedTopBirth P birth s x t).1 entry).elim
    (fun equal => Or.inl equal.2) (fun old => Or.inr (earlier x t old))

theorem fixedTopBirth_new_time_iff {P birth s x : ZFSet.{u}}
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ s) :
    ZFSet.pair x s ∈ fixedTopBirth P birth s ↔ x = P := by
  rw [pair_mem_fixedTopBirth]
  exact ⟨fun h => h.elim And.left (fun old => False.elim (ZFSet.mem_irrefl s (earlier x s old))),
    fun equal => Or.inl ⟨equal, rfl⟩⟩

theorem fixedTopBirth_earlier_iff {P birth s x t : ZFSet.{u}} (before : t ∈ s) :
    ZFSet.pair x t ∈ fixedTopBirth P birth s ↔ ZFSet.pair x t ∈ birth := by
  rw [pair_mem_fixedTopBirth]
  exact ⟨fun h => h.elim (fun equal => False.elim (ZFSet.mem_irrefl s (equal.2 ▸ before))) id,
    Or.inr⟩

theorem fixedTopBirth_oldMeet {P T r μ birth s : ZFSet.{u}}
    (meet : MeetOrderCode P r μ) (born : ZFSet.IsFunc P T birth)
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ s) (oldMeet : OldMeetCode r μ birth) :
    OldMeetCode (fixedTopOrder P r) (fixedTopMeet P r) (fixedTopBirth P birth s) := by
  intro x y z a b c ya xb ab notLower xy zc
  rcases (pair_mem_fixedTopBirth P birth s x b).1 xb with ⟨newx, newb⟩ | oldx
  · subst x b
    rcases (pair_mem_fixedTopBirth P birth s y a).1 ya with ⟨newy, newa⟩ | oldy
    · subst y a
      exact False.elim (ZFSet.mem_irrefl s ab)
    · have hy := (ZFSet.pair_mem_prod.1 (born.1 oldy)).1
      have equal := (fixedTopMeet_top_left meet (fixedTopCarrier_old hy)).1 xy
      subst z
      have oldc := (fixedTopBirth_old_iff hy).1 zc
      exact earlier y c oldc
  · have hx := (ZFSet.pair_mem_prod.1 (born.1 oldx)).1
    rcases (pair_mem_fixedTopBirth P birth s y a).1 ya with ⟨newy, newa⟩ | oldy
    · subst y a
      exact False.elim (ZFSet.mem_asymm (earlier x b oldx) ab)
    · have hy := (ZFSet.pair_mem_prod.1 (born.1 oldy)).1
      have oldxy := (fixedTopMeet_old_iff meet hx hy).1 xy
      have hz := (ZFSet.pair_mem_prod.1 (meet.operation.1 oldxy)).2
      exact oldMeet x y z a b c oldy oldx ab
        (fun lower => notLower ((fixedTopOrder_old_iff hy).2 lower)) oldxy
        ((fixedTopBirth_old_iff hz).1 zc)

theorem fixedTopBirth_singleton_injection (P : ZFSet.{u}) :
    InjectionCode {P} ZFSet.omega {ZFSet.pair P ∅} := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    have equal := ZFSet.mem_singleton.1 hz
    rw [equal]
    exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, ZFSet.omega_zero⟩
  · intro x hx
    have equal := ZFSet.mem_singleton.1 hx
    subst x
    refine ⟨∅, ZFSet.mem_singleton.2 rfl, ?_⟩
    intro y entry
    exact (ZFSet.pair_inj.1 (ZFSet.mem_singleton.1 entry)).2
  · intro x y z first second
    exact (ZFSet.pair_inj.1 (ZFSet.mem_singleton.1 first)).1.trans
      (ZFSet.pair_inj.1 (ZFSet.mem_singleton.1 second)).1.symm

end

namespace CodedGrowthLayer
open SetFormula
universe u

def of_natUnion {M : TransitiveGround.{u}}
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {P r μ birth : Nat → ZFSet.{u}} {L R MU B t T : ZFSet.{u}}
    (carrier : NatUnionCode P L) (relation : NatUnionCode r R)
    (operation : NatUnionCode μ MU) (born : NatUnionCode birth B)
    (n : Nat) (layer : CodedGrowthLayer M Space sourceOrder sourceMeet
      (P n) (r n) (μ n) (birth n) t)
    (separation : SeparationSchema M.sets) (ground : P n ∈ M.sets)
    (function : ZFSet.IsFunc (P n) T (birth n))
    (stable : ∀ m x, ZFSet.pair x t ∈ birth m → ZFSet.pair x t ∈ birth n) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L R MU B t :=
  layer.of_literal_extension separation ground (carrier.subset n) (relation.subset n)
    (operation.subset n) (born.subset n)
    (fun x _ entry => born.stable_birth_fiber n function stable x entry)

def empty_of_no_birth {M : TransitiveGround.{u}}
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {L r μ birth t : ZFSet.{u}} (inhabited : M.sets.Nonempty)
    (empty : ∀ x ∈ L, ZFSet.pair x t ∉ birth) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t :=
  .countablePoints ∅ (M.empty_mem inhabited) (M.empty_groundEmbeddable ZFSet.omega inhabited)
    (fun x hx entry => False.elim (empty x hx entry))

def empty_at_birth_bound {M : TransitiveGround.{u}}
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {L r μ birth cutoff : ZFSet.{u}} (inhabited : M.sets.Nonempty)
    (bounds : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ cutoff) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth cutoff :=
  empty_of_no_birth inhabited (fun x _ entry => ZFSet.mem_irrefl cutoff (bounds x cutoff entry))

end CodedGrowthLayer

namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem fixedTopBirth_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {P birth s : ZFSet.{u}} (hP : P ∈ M.sets) (hBirth : birth ∈ M.sets) (hs : s ∈ M.sets) :
    fixedTopBirth P birth s ∈ M.sets :=
  M.insert_mem pairing unions (M.orderedPair_mem pairing hP hs) hBirth

theorem fixedTopBirth_singleton_small
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {P : ZFSet.{u}} (hP : P ∈ M.sets) :
    ({P} : ZFSet.{u}) ∈ M.sets ∧ M.groundEmbeddable {P} ZFSet.omega := by
  have hSingle : ({P} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hP hP
  have hEntry := M.orderedPair_mem pairing hP (M.empty_mem ⟨P, hP⟩)
  have hGraph : ({ZFSet.pair P ∅} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hEntry hEntry
  exact ⟨hSingle, {ZFSet.pair P ∅}, hGraph, fixedTopBirth_singleton_injection P⟩

def fixedTopBirth_incoming_layer
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {P r birth s : ZFSet.{u}} (hP : P ∈ M.sets)
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ s) :
    CodedGrowthLayer M Space sourceOrder sourceMeet (fixedTopCarrier P)
      (fixedTopOrder P r) (fixedTopMeet P r) (fixedTopBirth P birth s) s :=
  .countablePoints {P} (M.fixedTopBirth_singleton_small pairing hP).1
    (M.fixedTopBirth_singleton_small pairing hP).2
    (fun _ _ entry => ZFSet.mem_singleton.2 ((fixedTopBirth_new_time_iff earlier).1 entry))

noncomputable def fixedTopBirth_earlier_layer
    (separation : SeparationSchema M.sets)
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {P T r μ birth s t : ZFSet.{u}}
    (hP : P ∈ M.sets) (meet : MeetOrderCode P r μ) (born : ZFSet.IsFunc P T birth)
    (before : t ∈ s)
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet P r μ birth t) :
    CodedGrowthLayer M Space sourceOrder sourceMeet (fixedTopCarrier P)
      (fixedTopOrder P r) (fixedTopMeet P r) (fixedTopBirth P birth s) t := by
  apply layer.of_literal_extension separation hP (fixedTopCarrier_subset P)
    (fixedTopOrder_subset P r) (fixedTopMeet_subset meet) (fixedTopBirth_subset P birth s)
  intro x _ entry
  have old := (fixedTopBirth_earlier_iff before).1 entry
  exact ⟨(ZFSet.pair_mem_prod.1 (born.1 old)).1, old⟩

noncomputable def fixedTopBirth_layers
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets)
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {P T r μ birth s : ZFSet.{u}}
    (hP : P ∈ M.sets) (meet : MeetOrderCode P r μ) (born : ZFSet.IsFunc P T birth)
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ s)
    (layers : ∀ t ∈ s, CodedGrowthLayer M Space sourceOrder sourceMeet P r μ birth t)
    (t : ZFSet.{u}) (bounded : t = s ∨ t ∈ s) :
    CodedGrowthLayer M Space sourceOrder sourceMeet (fixedTopCarrier P)
      (fixedTopOrder P r) (fixedTopMeet P r) (fixedTopBirth P birth s) t := by
  classical
  by_cases equal : t = s
  · subst t
    exact M.fixedTopBirth_incoming_layer pairing hP earlier
  · have before := bounded.resolve_left equal
    exact M.fixedTopBirth_earlier_layer separation hP meet born before (layers t before)

end TransitiveGround

namespace AttachmentBatchInputs
universe u
variable {P r μ I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss)

noncomputable abbrev batchBirth (_d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss) (birth stamp : ZFSet.{u}) : ZFSet.{u} :=
  taggedBirth P (indexedAttachmentFresh I Qs rs As) birth stamp

theorem batchBirth_function {T birth stamp : ZFSet.{u}}
    (born : ZFSet.IsFunc P T birth) (hs : stamp ∈ T) :
    ZFSet.IsFunc d.batchCarrier T (d.batchBirth birth stamp) := taggedBirth_function born hs

theorem batchBirth_fresh_entry_iff {T birth stamp t : ZFSet.{u}}
    (born : ZFSet.IsFunc P T birth) (q : d.templates.Fresh) :
    ZFSet.pair (d.coding.encode (.inr q)) t ∈ d.batchBirth birth stamp ↔ t = stamp :=
  taggedBirth_fresh_iff born (d.freshCode_mem q)

theorem batchBirth_oldMeet {T birth stamp : ZFSet.{u}}
    (born : ZFSet.IsFunc P T birth)
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp)
    (oldMeet : OldMeetCode r μ birth) :
    OldMeetCode d.batchOrder d.batchMeetGraph (d.batchBirth birth stamp) := by
  intro x y z a b c ya xb ab notLower meetEntry zc
  rcases (pair_mem_taggedBirth _ _ _ _ x b).1 xb with oldx | ⟨freshx, rfl⟩
  · have hx := (ZFSet.pair_mem_prod.1 (born.1 oldx)).1
    rcases (pair_mem_taggedBirth _ _ _ _ y a).1 ya with oldy | ⟨_, rfl⟩
    · have hy := (ZFSet.pair_mem_prod.1 (born.1 oldy)).1
      have oldEntry := (d.old_meet_iff hx hy).1 meetEntry
      have hz := (ZFSet.pair_mem_prod.1 (d.oldOrder.operation.1 oldEntry)).2
      exact oldMeet x y z a b c oldy oldx ab
        (fun lower => notLower ((d.old_order_iff hx hy).2 lower)) oldEntry
        ((taggedBirth_old_iff hz).1 zc)
    · exact False.elim (ZFSet.mem_asymm (earlier x b oldx) ab)
  · rcases (pair_mem_taggedBirth _ _ _ _ y a).1 ya with oldy | ⟨_, rfl⟩
    · have hy := (ZFSet.pair_mem_prod.1 (born.1 oldy)).1
      obtain ⟨p, hp, q, hq, equal⟩ := ZFSet.mem_prod.1 freshx
      obtain rfl := ZFSet.mem_singleton.1 hp
      subst x
      obtain ⟨q', rfl⟩ := d.freshCode_surjective q hq
      let v := d.oldOrder.toMeetOrder.meet (d.templates.shadow q') ⟨y, hy⟩
      have other : ZFSet.pair (ZFSet.pair (d.coding.encode (.inr q')) y) v.val ∈ d.batchMeetGraph :=
        d.coding.encoded_shadow_meet q' ⟨y, hy⟩ notLower
      have equal : z = v.val :=
        (show FunctionGraphOn (ZFSet.prod d.batchCarrier d.batchCarrier) d.batchMeetGraph from
          ⟨d.batchCarrier, d.batch_meetOrder.operation⟩).unique meetEntry other
      subst z
      exact earlier v.val c ((taggedBirth_old_iff v.property).1 zc)
    · exact False.elim (ZFSet.mem_irrefl _ ab)

theorem batchBirth_fresh_cases {birth stamp x : ZFSet.{u}}
    (earlier : ∀ y t, ZFSet.pair y t ∈ birth → t ∈ stamp)
    (entry : ZFSet.pair x stamp ∈ d.batchBirth birth stamp) :
    ∃ q : d.templates.Fresh, d.coding.encode (.inr q) = x := by
  have fresh := (taggedBirth_stamp_iff earlier).1 entry
  obtain ⟨p, hp, q, hq, equal⟩ := ZFSet.mem_prod.1 fresh
  obtain rfl := ZFSet.mem_singleton.1 hp
  obtain ⟨q', rfl⟩ := d.freshCode_surjective q hq
  exact ⟨q', equal.symm⟩

theorem batchBirth_different_components_bridge {T birth stamp : ZFSet.{u}}
    (born : ZFSet.IsFunc P T birth)
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp)
    (q t : d.templates.Fresh) (different : q.1 ≠ t.1) :
    OldBridgeCode d.batchCarrier d.batchOrder d.batchMeetGraph (d.batchBirth birth stamp) stamp
      (d.coding.encode (.inr q)) (d.coding.encode (.inr t)) := by
  classical
  by_cases qt : ZFSet.pair (d.coding.encode (.inr q)) (d.coding.encode (.inr t)) ∈ d.batchOrder
  · let z := d.templates.shadow t
    obtain ⟨a, entry, _⟩ := born.2 z.val z.property
    exact Or.inr ⟨z.val, old_mem_taggedExtension z.property, a, taggedBirth_subset _ _ _ _ entry,
      earlier z.val a entry, Or.inl
        ⟨(d.coding.old_upper_iff q z).2 ((d.coding.cross_lower_iff q t different).1 qt),
          (d.coding.old_lower_iff z t).2 (d.oldOrder.order.refl z.val z.property)⟩⟩
  · by_cases tq : ZFSet.pair (d.coding.encode (.inr t)) (d.coding.encode (.inr q)) ∈ d.batchOrder
    · let z := d.templates.shadow q
      obtain ⟨a, entry, _⟩ := born.2 z.val z.property
      exact Or.inr ⟨z.val, old_mem_taggedExtension z.property, a, taggedBirth_subset _ _ _ _ entry,
        earlier z.val a entry, Or.inr
          ⟨(d.coding.old_upper_iff t z).2 ((d.coding.cross_lower_iff t q different.symm).1 tq),
            (d.coding.old_lower_iff z q).2 (d.oldOrder.order.refl z.val z.property)⟩⟩
    · let z := d.oldOrder.toMeetOrder.meet (d.templates.shadow q) (d.templates.shadow t)
      obtain ⟨a, entry, _⟩ := born.2 z.val z.property
      exact Or.inl ⟨z.val, a, d.coding.encoded_cross_meet q t different qt tq,
        taggedBirth_subset _ _ _ _ entry, earlier z.val a entry⟩

end AttachmentBatchInputs

open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem taggedBirth_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P N birth stamp : ZFSet.{u}} (hP : P ∈ M.sets) (hN : N ∈ M.sets)
    (hBirth : birth ∈ M.sets) (hStamp : stamp ∈ M.sets) : taggedBirth P N birth stamp ∈ M.sets := by
  have hSingleP : ({P} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hP hP
  have hSingleStamp : ({stamp} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hStamp hStamp
  exact M.binary_union_mem pairing unions hBirth
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hSingleP hN) hSingleStamp)

end TransitiveGround

namespace AttachmentBatchInputs
variable {M : TransitiveGround.{u}}
variable {P r μ I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss)

theorem batchBirth_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {birth stamp : ZFSet.{u}} (hP : P ∈ M.sets) (hI : I ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets)
    (hBirth : birth ∈ M.sets) (hStamp : stamp ∈ M.sets) : d.batchBirth birth stamp ∈ M.sets :=
  M.taggedBirth_mem pairing unions powers separation hP
    (M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs) hBirth hStamp

noncomputable def batchBirth_earlier_layer
    (separation : SeparationSchema M.sets)
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {T birth stamp t : ZFSet.{u}} (hP : P ∈ M.sets)
    (born : ZFSet.IsFunc P T birth) (before : t ∈ stamp)
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet P r μ birth t) :
    CodedGrowthLayer M Space sourceOrder sourceMeet d.batchCarrier d.batchOrder d.batchMeetGraph
      (d.batchBirth birth stamp) t := by
  have meetSubset : μ ⊆ d.batchMeetGraph := by
    intro z hz
    obtain ⟨xy, hxy, v, hv, rfl⟩ := ZFSet.mem_prod.1 (d.oldOrder.operation.1 hz)
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    exact d.old_meet_entry hz
  apply layer.of_literal_extension separation hP (fun _ => old_mem_taggedExtension) ?_
    meetSubset (taggedBirth_subset _ _ _ _)
  · intro x _ entry
    have old := (taggedBirth_earlier_iff before).1 entry
    exact ⟨(ZFSet.pair_mem_prod.1 (born.1 old)).1, old⟩
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (d.oldOrder.order.relation hz)
    exact (d.old_order_iff hx hy).2 hz

noncomputable def batchBirth_incoming_layer
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {T birth stamp : ZFSet.{u}}
    (hP : P ∈ M.sets) (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets)
    (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets)
    (born : ZFSet.IsFunc P T birth)
    (old : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp)
    (index : SetMembers I → ZFSet.{u}) (earlier : ∀ i, index i ∈ stamp)
    (spaces : ∀ i, Space (index i) = d.space ⟨SetMembers.raw i, SetMembers.raw_mem i⟩)
    (orders : ∀ i, sourceOrder (index i) = d.rel ⟨SetMembers.raw i, SetMembers.raw_mem i⟩)
    (meets : ∀ i, sourceMeet (index i) = d.meet ⟨SetMembers.raw i, SetMembers.raw_mem i⟩) :
    CodedGrowthLayer M Space sourceOrder sourceMeet d.batchCarrier d.batchOrder d.batchMeetGraph
      (d.batchBirth birth stamp) stamp := by
  classical
  let fresh (x : {x : ZFSet.{u} // x ∈ d.batchCarrier ∧
      ZFSet.pair x stamp ∈ d.batchBirth birth stamp}) : d.templates.Fresh :=
    (d.batchBirth_fresh_cases old x.property.2).choose
  have freshEq (x : {x : ZFSet.{u} // x ∈ d.batchCarrier ∧
      ZFSet.pair x stamp ∈ d.batchBirth birth stamp}) : d.coding.encode (.inr (fresh x)) = x.val :=
    (d.batchBirth_fresh_cases old x.property.2).choose_spec
  let component (x : {x : ZFSet.{u} // x ∈ d.batchCarrier ∧
      ZFSet.pair x stamp ∈ d.batchBirth birth stamp}) : SetMembers I :=
    SetMembers.ofMem (fresh x).1.val (fresh x).1.property
  refine .separated (SetMembers I) index
    (fun i => batchTemplateGraph I P Qs rs As Es (SetMembers.raw i)) earlier
    (fun i => M.batchTemplateGraph_mem pairing unions powers separation hI hP hQs hrs hAs hEs
      (M.transitive hI (SetMembers.raw_mem i))) ?_ component ?_ ?_
  · intro i
    simpa only [spaces i, orders i, meets i] using
      d.batch_template_embedding_code ⟨SetMembers.raw i, SetMembers.raw_mem i⟩
  · intro x
    let q := fresh x
    have sameIndex : (⟨SetMembers.raw (component x), SetMembers.raw_mem (component x)⟩ :
        {i : ZFSet.{u} // i ∈ I}) = q.1 := by
      apply Subtype.ext
      exact SetMembers.raw_ofMem q.1.val q.1.property
    have rawSame : SetMembers.raw (component x) = q.1.val := congrArg Subtype.val sameIndex
    have point : q.2.val.val ∈ Space (index (component x)) := by
      rw [spaces, sameIndex]
      exact q.2.val.property
    apply (mem_relationImage _ _ _ x.val).2
    refine ⟨x.property.1, q.2.val.val, point, ?_⟩
    rw [rawSame, ← freshEq x]
    apply (pair_mem_batchTemplateGraph _ _ _ _ _ _ _ _ _).2
    apply (d.batch_template_entry_iff q.1 _ _).2
    exact Or.inr ⟨(mem_freshPart _ _ _ _).2 ⟨q.2.val.property, q.2.property⟩, rfl⟩
  · intro x y different
    have separate : (fresh x).1 ≠ (fresh y).1 := by
      intro equal
      apply different
      exact congrArg (fun i : {i : ZFSet.{u} // i ∈ I} => SetMembers.ofMem i.val i.property) equal
    have bridge := d.batchBirth_different_components_bridge born old (fresh x) (fresh y) separate
    rw [freshEq x, freshEq y] at bridge
    exact bridge

end AttachmentBatchInputs

end PartitionPilot.Forcing

end OAI
