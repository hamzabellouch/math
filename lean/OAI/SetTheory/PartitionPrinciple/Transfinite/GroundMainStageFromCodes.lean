import OAI.SetTheory.PartitionPrinciple.Definability.TaggedExtensionCodes
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundNaturalFamilyShift

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

structure MeetOrderCode (L r μ : ZFSet.{u}) : Prop where
  order : PartialOrderCode L r
  operation : ZFSet.IsFunc (ZFSet.prod L L) L μ
  lower_left : ∀ x y z, ZFSet.pair (ZFSet.pair x y) z ∈ μ → ZFSet.pair z x ∈ r
  lower_right : ∀ x y z, ZFSet.pair (ZFSet.pair x y) z ∈ μ → ZFSet.pair z y ∈ r
  greatest : ∀ x y z w, w ∈ L → ZFSet.pair (ZFSet.pair x y) z ∈ μ →
    ZFSet.pair w x ∈ r → ZFSet.pair w y ∈ r → ZFSet.pair w z ∈ r

structure MeetFilterCode (L r μ F : ZFSet.{u}) : Prop where
  subset : F ⊆ L
  nonempty : F.Nonempty
  upward : ∀ x ∈ F, ∀ y ∈ L, ZFSet.pair x y ∈ r → y ∈ F
  closed_meet : ∀ x ∈ F, ∀ y ∈ F, ∀ z,
    ZFSet.pair (ZFSet.pair x y) z ∈ μ → z ∈ F

def OldMeetCode (r μ birth : ZFSet.{u}) : Prop :=
  ∀ x y z a b c, ZFSet.pair y a ∈ birth → ZFSet.pair x b ∈ birth →
    a ∈ b → ZFSet.pair x y ∉ r → ZFSet.pair (ZFSet.pair x y) z ∈ μ →
      ZFSet.pair z c ∈ birth → c ∈ b

structure StrictLexHeightCode (L C Q r height qlt : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc L (ZFSet.prod C Q) height
  strict : ∀ x ∈ L, ∀ y ∈ L, ∀ c q d v,
    ZFSet.pair x y ∈ r → x ≠ y →
      ZFSet.pair x (ZFSet.pair c q) ∈ height →
        ZFSet.pair y (ZFSet.pair d v) ∈ height →
          c ∈ d ∨ (c = d ∧ ZFSet.pair q v ∈ qlt)

theorem birthEssential_below_earlier {L F T r μ birth x y a b : ZFSet.{u}}
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth) (oldMeet : OldMeetCode r μ birth)
    (essential : x ∈ birthEssentialSet F T r birth) (positive : y ∈ F)
    (bornY : ZFSet.pair y a ∈ birth) (bornX : ZFSet.pair x b ∈ birth)
    (earlier : a ∈ b) : ZFSet.pair x y ∈ r ∧ x ≠ y := by
  classical
  have hx := (mem_birthEssentialSet F T r birth x).1 essential
  have xL := filter.subset hx.1
  have yL := filter.subset positive
  have bT := (ZFSet.pair_mem_prod.1 (born.1 bornX)).2
  have lower : ZFSet.pair x y ∈ r := by
    by_contra notLower
    obtain ⟨z, meetXY, _⟩ := meet.operation.2 (ZFSet.pair x y)
      (ZFSet.pair_mem_prod.2 ⟨xL, yL⟩)
    have zL := (ZFSet.pair_mem_prod.1 (meet.operation.1 meetXY)).2
    obtain ⟨c, bornZ, _⟩ := born.2 z zL
    have cT := (ZFSet.pair_mem_prod.1 (born.1 bornZ)).2
    exact hx.2 z (filter.closed_meet x hx.1 y positive z meetXY) c cT b bT
      (meet.lower_left x y z meetXY) bornZ bornX
      (oldMeet x y z a b c bornY bornX earlier notLower meetXY bornZ)
  refine ⟨lower, ?_⟩
  intro equal
  subst y
  obtain ⟨t, _, unique⟩ := born.2 x xL
  have sameBirth : a = b := (unique a bornY).trans (unique b bornX).symm
  exact ZFSet.mem_irrefl b (sameBirth ▸ earlier)

theorem essentialHeightDescent_of_chronological_laws
    {L F T C Q r μ birth height qlt : ZFSet.{u}}
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth) (oldMeet : OldMeetCode r μ birth)
    (strictHeight : StrictLexHeightCode L C Q r height qlt) :
    EssentialHeightDescent (birthEssentialSet F T r birth) birth height qlt := by
  intro x hx y hy i j c q d v bornX bornY earlier heightX heightY
  have lower := birthEssential_below_earlier meet filter born oldMeet hy
    (birthEssentialSet_subset F T r birth hx) bornX bornY earlier
  exact strictHeight.strict y (filter.subset (birthEssentialSet_subset F T r birth hy))
    x (filter.subset (birthEssentialSet_subset F T r birth hx)) d v c q
    lower.1 lower.2 heightY heightX

end



section

universe u v

noncomputable def essentialBirthFiber (F T r birth t : ZFSet.{u}) : ZFSet.{u} :=
  relationFiber (birthEssentialSet F T r birth)
    (relationConverse (birthEssentialSet F T r birth) (essentialBirthIndices F T r birth) birth) t

theorem mem_essentialBirthFiber (F T r birth t x : ZFSet.{u}) :
    x ∈ essentialBirthFiber F T r birth t ↔
      x ∈ birthEssentialSet F T r birth ∧ t ∈ T ∧ ZFSet.pair x t ∈ birth := by
  rw [essentialBirthFiber, mem_relationFiber, pair_mem_relationConverse]
  constructor
  · rintro ⟨hx, _, ht, born⟩
    exact ⟨hx, ((mem_essentialBirthIndices F T r birth t).1 ht).1, born⟩
  · rintro ⟨hx, ht, born⟩
    exact ⟨hx, hx, (mem_essentialBirthIndices F T r birth t).2 ⟨ht, x, hx, born⟩, born⟩

theorem essentialBirthFiber_subset (F T r birth t : ZFSet.{u}) :
    essentialBirthFiber F T r birth t ⊆ birthEssentialSet F T r birth :=
  fun _ hx => ((mem_essentialBirthFiber F T r birth t _).1 hx).1

def OldBridgeCode (L r μ birth t x y : ZFSet.{u}) : Prop :=
  (∃ z a, ZFSet.pair (ZFSet.pair x y) z ∈ μ ∧ ZFSet.pair z a ∈ birth ∧ a ∈ t) ∨
  (∃ z ∈ L, ∃ a, ZFSet.pair z a ∈ birth ∧ a ∈ t ∧
    ((ZFSet.pair x z ∈ r ∧ ZFSet.pair z y ∈ r) ∨
      (ZFSet.pair y z ∈ r ∧ ZFSet.pair z x ∈ r)))

theorem birthEssentials_no_oldBridge {L F T r μ birth t x y : ZFSet.{u}}
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth)
    (hx : x ∈ birthEssentialSet F T r birth) (hy : y ∈ birthEssentialSet F T r birth)
    (xt : ZFSet.pair x t ∈ birth) (yt : ZFSet.pair y t ∈ birth) :
    ¬ OldBridgeCode L r μ birth t x y := by
  have xE := (mem_birthEssentialSet F T r birth x).1 hx
  have yE := (mem_birthEssentialSet F T r birth y).1 hy
  have ht := (ZFSet.pair_mem_prod.1 (born.1 xt)).2
  intro bridge
  rcases bridge with ⟨z, a, meetXY, za, old⟩ | ⟨z, hz, a, za, old, intermediate⟩
  · have ha := (ZFSet.pair_mem_prod.1 (born.1 za)).2
    exact xE.2 z (filter.closed_meet x xE.1 y yE.1 z meetXY) a ha t ht
      (meet.lower_left x y z meetXY) za xt old
  · have ha := (ZFSet.pair_mem_prod.1 (born.1 za)).2
    rcases intermediate with ⟨xz, zy⟩ | ⟨yz, zx⟩
    · exact yE.2 z (filter.upward x xE.1 z hz xz) a ha t ht zy za yt old
    · exact xE.2 z (filter.upward y yE.1 z hz yz) a ha t ht zx za xt old

theorem birthEssentials_same_component {L F T r μ birth t x y : ZFSet.{u}}
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth) {I : Type v} (component : ZFSet.{u} → I)
    (separated : ∀ x ∈ L, ∀ y ∈ L,
      ZFSet.pair x t ∈ birth → ZFSet.pair y t ∈ birth → component x ≠ component y →
        OldBridgeCode L r μ birth t x y)
    (hx : x ∈ birthEssentialSet F T r birth) (hy : y ∈ birthEssentialSet F T r birth)
    (xt : ZFSet.pair x t ∈ birth) (yt : ZFSet.pair y t ∈ birth) :
    component x = component y := by
  classical
  by_contra different
  exact birthEssentials_no_oldBridge meet filter born hx hy xt yt
    (separated x (filter.subset (birthEssentialSet_subset F T r birth hx))
      y (filter.subset (birthEssentialSet_subset F T r birth hy)) xt yt different)

theorem essentialBirthFiber_same_component {L F T r μ birth t x y : ZFSet.{u}}
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth) {I : Type v} (component : ZFSet.{u} → I)
    (separated : ∀ x ∈ L, ∀ y ∈ L,
      ZFSet.pair x t ∈ birth → ZFSet.pair y t ∈ birth → component x ≠ component y →
        OldBridgeCode L r μ birth t x y)
    (hx : x ∈ essentialBirthFiber F T r birth t) (hy : y ∈ essentialBirthFiber F T r birth t) :
    component x = component y := by
  have xE := (mem_essentialBirthFiber F T r birth t x).1 hx
  have yE := (mem_essentialBirthFiber F T r birth t y).1 hy
  exact birthEssentials_same_component meet filter born component separated xE.1 yE.1 xE.2.2 yE.2.2

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem essentialBirthFiber_mem (separation : SeparationSchema M.sets)
    {F T r birth t : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) (ht : t ∈ M.sets) :
    essentialBirthFiber F T r birth t ∈ M.sets := by
  let E := birthEssentialSet F T r birth
  let params := extend t (extend T (extend birth Fin.elim0))
  let φ : BoundedFormula 4 := .conj (.mem 1 2) (BoundedFormula.pairMembershipFormula 0 1 3)
  have selected := M.bounded_separation_mem separation φ params
    (Fin.cases ht (Fin.cases hT (Fin.cases hBirth (fun j => Fin.elim0 j))))
    (M.birthEssentialSet_mem separation hF hT hr hBirth)
  have eq : ZFSet.sep (fun x => BoundedFormula.Truth φ (extend x params)) E =
      essentialBirthFiber F T r birth t := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_essentialBirthFiber]
    exact and_congr Iff.rfl
      (and_congr Iff.rfl (BoundedFormula.truth_pairMembershipFormula 0 1 3 _))
  exact eq ▸ selected

end TransitiveGround

end



section
universe u

structure GroundMainStage (M : TransitiveGround.{u}) (C D rD : ZFSet.{u}) where
  carrier : ZFSet.{u}
  order : ZFSet.{u}
  meetGraph : ZFSet.{u}
  actors : ZFSet.{u}
  multiplication : ZFSet.{u}
  inverse : ZFSet.{u}
  identity : ZFSet.{u}
  action : ZFSet.{u}
  bottom : ZFSet.{u}
  top : ZFSet.{u}
  height : ZFSet.{u}
  carrier_ground : carrier ∈ M.sets
  order_ground : order ∈ M.sets
  meet_ground : meetGraph ∈ M.sets
  actors_ground : actors ∈ M.sets
  multiplication_ground : multiplication ∈ M.sets
  inverse_ground : inverse ∈ M.sets
  action_ground : action ∈ M.sets
  height_ground : height ∈ M.sets
  columns_ground : C ∈ M.sets
  coordinates_ground : D ∈ M.sets
  coordinate_order_ground : rD ∈ M.sets
  meet : MeetOrderCode carrier order meetGraph
  group_code : GroupCode actors multiplication inverse identity
  action_code : PosetActionCode actors carrier multiplication identity order action
  bottom_mem : bottom ∈ carrier
  least : ∀ x ∈ carrier, ZFSet.pair bottom x ∈ order
  top_mem : top ∈ carrier
  greatest : ∀ x ∈ carrier, ZFSet.pair x top ∈ order
  height_code : StrictLexHeightCode carrier C D order height rD
  height_range_ground : relationImage carrier (ZFSet.prod C D) height ∈ M.sets
  height_range_countable : M.groundEmbeddable (relationImage carrier (ZFSet.prod C D) height) ZFSet.omega

namespace GroundMainStage
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundMainStage M C D rD)

theorem bottom_ground : stage.bottom ∈ M.sets := M.transitive stage.carrier_ground stage.bottom_mem
theorem top_ground : stage.top ∈ M.sets := M.transitive stage.carrier_ground stage.top_mem
theorem identity_ground : stage.identity ∈ M.sets := M.transitive stage.actors_ground stage.group_code.identity_mem

end GroundMainStage





noncomputable def taggedBirth (P N birth stamp : ZFSet.{u}) : ZFSet.{u} :=
  birth ∪ ZFSet.prod (ZFSet.prod {P} N) {stamp}

theorem pair_mem_taggedBirth (P N birth stamp x t : ZFSet.{u}) :
    ZFSet.pair x t ∈ taggedBirth P N birth stamp ↔
      ZFSet.pair x t ∈ birth ∨ (x ∈ ZFSet.prod {P} N ∧ t = stamp) := by
  rw [taggedBirth, ZFSet.mem_union, ZFSet.pair_mem_prod, ZFSet.mem_singleton]

theorem taggedBirth_subset (P N birth stamp : ZFSet.{u}) : birth ⊆ taggedBirth P N birth stamp :=
  fun _ hx => ZFSet.mem_union.2 (Or.inl hx)

theorem taggedBirth_old_iff {P N birth stamp x t : ZFSet.{u}} (hx : x ∈ P) :
    ZFSet.pair x t ∈ taggedBirth P N birth stamp ↔ ZFSet.pair x t ∈ birth := by
  rw [pair_mem_taggedBirth]
  exact ⟨fun h => h.elim id (fun h => False.elim (taggedExtension_disjoint P N x hx h.1)), Or.inl⟩

theorem taggedBirth_fresh_iff {P N T birth stamp q t : ZFSet.{u}}
    (born : ZFSet.IsFunc P T birth) (hq : q ∈ N) :
    ZFSet.pair (ZFSet.pair P q) t ∈ taggedBirth P N birth stamp ↔ t = stamp := by
  rw [pair_mem_taggedBirth]
  constructor
  · intro h
    exact h.elim (fun old => False.elim
      (pair_tag_not_mem P q (ZFSet.pair_mem_prod.1 (born.1 old)).1)) And.right
  · intro equal
    exact Or.inr ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, hq⟩, equal⟩

theorem taggedBirth_function {P N T birth stamp : ZFSet.{u}}
    (born : ZFSet.IsFunc P T birth) (hs : stamp ∈ T) :
    ZFSet.IsFunc (taggedExtension P N) T (taggedBirth P N birth stamp) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases ZFSet.mem_union.1 hz with old | fresh
    · obtain ⟨x, hx, t, ht, rfl⟩ := ZFSet.mem_prod.1 (born.1 old)
      exact ZFSet.pair_mem_prod.2 ⟨old_mem_taggedExtension hx, ht⟩
    · obtain ⟨x, hx, t, ht, rfl⟩ := ZFSet.mem_prod.1 fresh
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_union.2 (Or.inr hx), (ZFSet.mem_singleton.1 ht).symm ▸ hs⟩
  · intro x hx
    rcases mem_taggedExtension.1 hx with old | ⟨q, hq, rfl⟩
    · obtain ⟨t, entry, unique⟩ := born.2 x old
      exact ⟨t, (taggedBirth_old_iff old).2 entry, fun s h => unique s ((taggedBirth_old_iff old).1 h)⟩
    · exact ⟨stamp, (taggedBirth_fresh_iff born hq).2 rfl,
        fun s h => (taggedBirth_fresh_iff born hq).1 h⟩

theorem taggedBirth_bound {P N birth stamp : ZFSet.{u}}
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp) :
    ∀ x t, ZFSet.pair x t ∈ taggedBirth P N birth stamp → t = stamp ∨ t ∈ stamp := by
  intro x t entry
  exact ((pair_mem_taggedBirth P N birth stamp x t).1 entry).elim
    (fun old => Or.inr (earlier x t old)) (fun fresh => Or.inl fresh.2)

theorem taggedBirth_stamp_iff {P N birth stamp x : ZFSet.{u}}
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp) :
    ZFSet.pair x stamp ∈ taggedBirth P N birth stamp ↔ x ∈ ZFSet.prod {P} N := by
  rw [pair_mem_taggedBirth]
  exact ⟨fun h => h.elim (fun old => False.elim (ZFSet.mem_irrefl stamp (earlier x stamp old))) And.left,
    fun hx => Or.inr ⟨hx, rfl⟩⟩

theorem taggedBirth_earlier_iff {P N birth stamp x t : ZFSet.{u}} (before : t ∈ stamp) :
    ZFSet.pair x t ∈ taggedBirth P N birth stamp ↔ ZFSet.pair x t ∈ birth := by
  rw [pair_mem_taggedBirth]
  exact ⟨fun h => h.elim id (fun fresh => False.elim (ZFSet.mem_irrefl stamp (fresh.2 ▸ before))), Or.inl⟩





noncomputable def mainStageCode (P r μ G m inv one A bottom top height : ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 10 (Fin.cases P (Fin.cases r (Fin.cases μ (Fin.cases G (Fin.cases m (Fin.cases inv (Fin.cases one (Fin.cases A (Fin.cases bottom (Fin.cases top (Fin.cases height (Fin.elim0))))))))))))

theorem mainStageCode_inj
    {P r μ G m inv one A bottom top height P₂ r₂ μ₂ G₂ m₂ inv₂ one₂ A₂ bottom₂ top₂ height₂ : ZFSet.{u}} :
    mainStageCode P r μ G m inv one A bottom top height = mainStageCode P₂ r₂ μ₂ G₂ m₂ inv₂ one₂ A₂ bottom₂ top₂ height₂ ↔
      P = P₂ ∧ r = r₂ ∧ μ = μ₂ ∧ G = G₂ ∧ m = m₂ ∧ inv = inv₂ ∧ one = one₂ ∧ A = A₂ ∧ bottom = bottom₂ ∧ top = top₂ ∧ height = height₂ := by
  constructor
  · intro equal
    have fields := nonemptyTupleCode_injective 10 equal
    exact ⟨congrFun fields (0 : Fin 11), congrFun fields (1 : Fin 11), congrFun fields (2 : Fin 11), congrFun fields (3 : Fin 11), congrFun fields (4 : Fin 11), congrFun fields (5 : Fin 11), congrFun fields (6 : Fin 11), congrFun fields (7 : Fin 11), congrFun fields (8 : Fin 11), congrFun fields (9 : Fin 11), congrFun fields (10 : Fin 11)⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

namespace GroundMainStage
open SetFormula
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}

def field (stage : GroundMainStage M C D rD) : Fin 11 → ZFSet.{u} :=
  Fin.cases stage.carrier (Fin.cases stage.order (Fin.cases stage.meetGraph (Fin.cases stage.actors (Fin.cases stage.multiplication (Fin.cases stage.inverse (Fin.cases stage.identity (Fin.cases stage.action (Fin.cases stage.bottom (Fin.cases stage.top (Fin.cases stage.height (Fin.elim0)))))))))))

noncomputable def code (stage : GroundMainStage M C D rD) : ZFSet.{u} :=
  nonemptyTupleCode 10 stage.field

@[ext] theorem ext {first second : GroundMainStage M C D rD}
    (carrier : first.carrier = second.carrier)
    (order : first.order = second.order)
    (meetGraph : first.meetGraph = second.meetGraph)
    (actors : first.actors = second.actors)
    (multiplication : first.multiplication = second.multiplication)
    (inverse : first.inverse = second.inverse)
    (identity : first.identity = second.identity)
    (action : first.action = second.action)
    (bottom : first.bottom = second.bottom)
    (top : first.top = second.top)
    (height : first.height = second.height) : first = second := by
  cases first
  cases second
  cases carrier
  cases order
  cases meetGraph
  cases actors
  cases multiplication
  cases inverse
  cases identity
  cases action
  cases bottom
  cases top
  cases height
  rfl

theorem field_injective : Function.Injective (field (M := M) (C := C) (D := D) (rD := rD)) := by
  intro first second equal
  exact ext (congrFun equal (0 : Fin 11)) (congrFun equal (1 : Fin 11)) (congrFun equal (2 : Fin 11)) (congrFun equal (3 : Fin 11)) (congrFun equal (4 : Fin 11)) (congrFun equal (5 : Fin 11)) (congrFun equal (6 : Fin 11)) (congrFun equal (7 : Fin 11)) (congrFun equal (8 : Fin 11)) (congrFun equal (9 : Fin 11)) (congrFun equal (10 : Fin 11))

theorem code_injective : Function.Injective (code (M := M) (C := C) (D := D) (rD := rD)) := by
  intro first second equal
  exact field_injective (nonemptyTupleCode_injective 10 equal)

theorem field_ground (stage : GroundMainStage M C D rD) : ∀ j, stage.field j ∈ M.sets :=
  Fin.cases stage.carrier_ground (Fin.cases stage.order_ground (Fin.cases stage.meet_ground (Fin.cases stage.actors_ground (Fin.cases stage.multiplication_ground (Fin.cases stage.inverse_ground (Fin.cases stage.identity_ground (Fin.cases stage.action_ground (Fin.cases stage.bottom_ground (Fin.cases stage.top_ground (Fin.cases stage.height_ground ((fun i => Fin.elim0 i))))))))))))

theorem code_mem (stage : GroundMainStage M C D rD)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) : stage.code ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 10 stage.field stage.field_ground

end GroundMainStage

namespace BoundedFormula
open SetFormula

def mainStageFormula {n} (z P r μ G m inv one A bottom top height : Fin n) : BoundedFormula n :=
  nonemptyTupleFormula 10 z (Fin.cases P (Fin.cases r (Fin.cases μ (Fin.cases G (Fin.cases m (Fin.cases inv (Fin.cases one (Fin.cases A (Fin.cases bottom (Fin.cases top (Fin.cases height (Fin.elim0))))))))))))

theorem truth_mainStageFormula {n} (z P r μ G m inv one A bottom top height : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (mainStageFormula z P r μ G m inv one A bottom top height) env ↔
      env z = mainStageCode (env P) (env r) (env μ) (env G) (env m) (env inv) (env one) (env A) (env bottom) (env top) (env height) := by
  rw [mainStageFormula, truth_nonemptyTupleFormula]
  rfl

theorem realize_mainStageFormula (M : TransitiveGround.{u}) {n}
    (z P r μ G m inv one A bottom top height : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (mainStageFormula z P r μ G m inv one A bottom top height).toFormula env ↔
      env z = mainStageCode (env P) (env r) (env μ) (env G) (env m) (env inv) (env one) (env A) (env bottom) (env top) (env height) :=
  (realize_toFormula M _ env members).trans (truth_mainStageFormula z P r μ G m inv one A bottom top height env)

end BoundedFormula

end



namespace GroundMainStage
open SetFormula
universe u
variable {M : TransitiveGround.{u}}

noncomputable def ofCodes
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A m inv one b t C D rD height : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hm : m ∈ M.sets) (hInv : inv ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hHeight : height ∈ M.sets)
    (meet : MeetOrderCode P r μ) (group : GroupCode G m inv one)
    (action : PosetActionCode G P m one r A)
    (hb : b ∈ P) (least : ∀ x ∈ P, ZFSet.pair b x ∈ r)
    (ht : t ∈ P) (greatest : ∀ x ∈ P, ZFSet.pair x t ∈ r)
    (heightCode : StrictLexHeightCode P C D r height rD)
    (heightSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) height) ZFSet.omega) :
    GroundMainStage M C D rD where
  carrier := P
  order := r
  meetGraph := μ
  actors := G
  multiplication := m
  inverse := inv
  identity := one
  action := A
  bottom := b
  top := t
  height := height
  carrier_ground := hP
  order_ground := hr
  meet_ground := hμ
  actors_ground := hG
  multiplication_ground := hm
  inverse_ground := hInv
  action_ground := hA
  height_ground := hHeight
  columns_ground := hC
  coordinates_ground := hD
  coordinate_order_ground := hrD
  meet := meet
  group_code := group
  action_code := action
  bottom_mem := hb
  least := least
  top_mem := ht
  greatest := greatest
  height_code := heightCode
  height_range_ground := M.relationImage_mem separation hP
    (M.prod_mem pairing unions powers separation hC hD) hHeight
  height_range_countable := heightSmall

end GroundMainStage

end PartitionPilot.Forcing

end OAI
