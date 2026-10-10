import OAI.SetTheory.PartitionPrinciple.Geometry.GroundSingleAttachment

namespace OAI

namespace PartitionPilot.Forcing

universe u

structure RestrictedActionCode (P r A g source target base : ZFSet.{u}) : Prop where
  shape : base ⊆ ZFSet.prod P P
  target_entry : ZFSet.pair (ZFSet.pair g source) target ∈ A
  entries : ∀ x ∈ P, ∀ y ∈ P, ZFSet.pair x y ∈ base ↔
    ZFSet.pair x source ∈ r ∧ ZFSet.pair (ZFSet.pair g x) y ∈ A

noncomputable def restrictedActionGraph (P r A g source : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ P, ∃ y ∈ P, z = ZFSet.pair x y ∧
    ZFSet.pair x source ∈ r ∧ ZFSet.pair (ZFSet.pair g x) y ∈ A) (ZFSet.prod P P)

theorem restrictedActionGraph_subset (P r A g source : ZFSet.{u}) :
    restrictedActionGraph P r A g source ⊆ ZFSet.prod P P :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem pair_mem_restrictedActionGraph (P r A g source x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ restrictedActionGraph P r A g source ↔
      x ∈ P ∧ y ∈ P ∧ ZFSet.pair x source ∈ r ∧ ZFSet.pair (ZFSet.pair g x) y ∈ A := by
  rw [restrictedActionGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hx, hy⟩, a, _, b, _, eq, lower, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hx, hy, lower, entry⟩
  · rintro ⟨hx, hy, lower, entry⟩
    exact ⟨⟨hx, hy⟩, x, hx, y, hy, rfl, lower, entry⟩

theorem restrictedActionGraph_code {P r A g source target : ZFSet.{u}}
    (target_entry : ZFSet.pair (ZFSet.pair g source) target ∈ A) :
    RestrictedActionCode P r A g source target (restrictedActionGraph P r A g source) where
  shape := restrictedActionGraph_subset P r A g source
  target_entry := target_entry
  entries x hx y hy := by simp only [pair_mem_restrictedActionGraph, hx, hy, true_and]

namespace PosetActionCode

open SetRealization

variable {G P m inv e r A : ZFSet.{u}} (action : PosetActionCode G P m e r A)
include action

theorem raw_order_iff (group : GroupCode G m inv e) (order : PartialOrderCode P r)
    {g x y x' y' : ZFSet.{u}} (hg : g ∈ G)
    (xx' : ZFSet.pair (ZFSet.pair g x) x' ∈ A)
    (yy' : ZFSet.pair (ZFSet.pair g y) y' ∈ A) :
    ZFSet.pair x' y' ∈ r ↔ ZFSet.pair x y ∈ r := by
  have sx := ZFSet.pair_mem_prod.1 (action.function.1 xx')
  have sy := ZFSet.pair_mem_prod.1 (action.function.1 yy')
  have hx := (ZFSet.pair_mem_prod.1 sx.1).2
  have hy := (ZFSet.pair_mem_prod.1 sy.1).2
  let actor : SetMembers G := SetMembers.ofMem g hg
  let X : SetMembers P := SetMembers.ofMem x hx
  let Y : SetMembers P := SetMembers.ofMem y hy
  have eqX : action.act actor X = SetMembers.ofMem x' sx.2 := by
    apply (action.act_eq_iff actor X _).2
    simpa only [actor, X, SetMembers.raw_ofMem] using xx'
  have eqY : action.act actor Y = SetMembers.ofMem y' sy.2 := by
    apply (action.act_eq_iff actor Y _).2
    simpa only [actor, Y, SetMembers.raw_ofMem] using yy'
  have law := action.act_le_iff group order actor X Y
  rw [eqX, eqY] at law
  change (ZFSet.pair (SetMembers.raw (SetMembers.ofMem x' sx.2))
      (SetMembers.raw (SetMembers.ofMem y' sy.2)) ∈ r ↔
    ZFSet.pair (SetMembers.raw X) (SetMembers.raw Y) ∈ r) at law
  simpa only [X, Y, SetMembers.raw_ofMem] using law

theorem raw_preimage (group : GroupCode G m inv e) {g y : ZFSet.{u}}
    (hg : g ∈ G) (hy : y ∈ P) :
    ∃ x ∈ P, ZFSet.pair (ZFSet.pair g x) y ∈ A := by
  let := group.toGroup
  let actor : SetMembers G := SetMembers.ofMem g hg
  let Y : SetMembers P := SetMembers.ofMem y hy
  let X := action.act actor⁻¹ Y
  refine ⟨SetMembers.raw X, SetMembers.raw_mem X, ?_⟩
  simpa only [actor, Y, SetMembers.raw_ofMem] using
    (action.act_eq_iff actor X Y).1 (action.act_inv_right group actor Y)

theorem raw_map_meet {meetGraph : ZFSet.{u}}
    (group : GroupCode G m inv e) (meet : MeetOrderCode P r meetGraph)
    {g x y z x' y' z' : ZFSet.{u}} (hg : g ∈ G)
    (xyz : ZFSet.pair (ZFSet.pair x y) z ∈ meetGraph)
    (xx' : ZFSet.pair (ZFSet.pair g x) x' ∈ A)
    (yy' : ZFSet.pair (ZFSet.pair g y) y' ∈ A)
    (zz' : ZFSet.pair (ZFSet.pair g z) z' ∈ A) :
    ZFSet.pair (ZFSet.pair x' y') z' ∈ meetGraph := by
  have hx' := (ZFSet.pair_mem_prod.1 (action.function.1 xx')).2
  have hy' := (ZFSet.pair_mem_prod.1 (action.function.1 yy')).2
  have hz' := (ZFSet.pair_mem_prod.1 (action.function.1 zz')).2
  apply meet.pair_iff.2
  refine ⟨hx', hy', hz',
    (action.raw_order_iff group meet.order hg zz' xx').2 (meet.lower_left x y z xyz),
    (action.raw_order_iff group meet.order hg zz' yy').2 (meet.lower_right x y z xyz), ?_⟩
  intro w hw wx' wy'
  obtain ⟨v, hv, vw⟩ := action.raw_preimage group hg hw
  exact (action.raw_order_iff group meet.order hg vw zz').2
    (meet.greatest x y z v hv xyz
      ((action.raw_order_iff group meet.order hg vw xx').1 wx')
      ((action.raw_order_iff group meet.order hg vw yy').1 wy'))

end PosetActionCode

namespace RestrictedActionCode

variable {P r A g source target base : ZFSet.{u}}
variable (code : RestrictedActionCode P r A g source target base)
include code

theorem eq_graph : base = restrictedActionGraph P r A g source := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (code.shape hz)
    exact (pair_mem_restrictedActionGraph P r A g source x y).2
      ⟨hx, hy, (code.entries x hx y hy).1 hz⟩
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1
      (restrictedActionGraph_subset P r A g source hz)
    exact (code.entries x hx y hy).2
      ((pair_mem_restrictedActionGraph P r A g source x y).1 hz).2.2

theorem entry_action {x y : ZFSet.{u}} (entry : ZFSet.pair x y ∈ base) :
    ZFSet.pair (ZFSet.pair g x) y ∈ A := by
  have shape := ZFSet.pair_mem_prod.1 (code.shape entry)
  exact ((code.entries x shape.1 y shape.2).1 entry).2

theorem base_function {G m e : ZFSet.{u}} (action : PosetActionCode G P m e r A)
    (hg : g ∈ G) : ZFSet.IsFunc (attachmentIdeal P r source) P base := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (code.shape hz)
    exact ZFSet.pair_mem_prod.2
      ⟨(mem_attachmentIdeal P r source x).2 ⟨hx, ((code.entries x hx y hy).1 hz).1⟩, hy⟩
  · intro x hx
    have parts := (mem_attachmentIdeal P r source x).1 hx
    obtain ⟨y, entry, unique⟩ := action.function.2 (ZFSet.pair g x)
      (ZFSet.pair_mem_prod.2 ⟨hg, parts.1⟩)
    have hy := (ZFSet.pair_mem_prod.1 (action.function.1 entry)).2
    exact ⟨y, (code.entries x parts.1 y hy).2 ⟨parts.2, entry⟩,
      fun z hz => unique z (code.entry_action hz)⟩

theorem source_entry (order : PartialOrderCode P r) (hsource : source ∈ P)
    (htarget : target ∈ P) : ZFSet.pair source target ∈ base :=
  (code.entries source hsource target htarget).2
    ⟨order.refl source hsource, code.target_entry⟩

theorem base_order {G m inv e : ZFSet.{u}} (group : GroupCode G m inv e)
    (action : PosetActionCode G P m e r A) (order : PartialOrderCode P r) (hg : g ∈ G)
    {x y x' y' : ZFSet.{u}} (xx' : ZFSet.pair x x' ∈ base)
    (yy' : ZFSet.pair y y' ∈ base) :
    ZFSet.pair x' y' ∈ r ↔ ZFSet.pair x y ∈ r :=
  action.raw_order_iff group order hg (code.entry_action xx') (code.entry_action yy')

theorem base_meet {G m inv e μ : ZFSet.{u}} (group : GroupCode G m inv e)
    (action : PosetActionCode G P m e r A) (meet : MeetOrderCode P r μ) (hg : g ∈ G)
    {x y z x' y' z' : ZFSet.{u}} (xyz : ZFSet.pair (ZFSet.pair x y) z ∈ μ)
    (xx' : ZFSet.pair x x' ∈ base) (yy' : ZFSet.pair y y' ∈ base)
    (zz' : ZFSet.pair z z' ∈ base) : ZFSet.pair (ZFSet.pair x' y') z' ∈ μ :=
  action.raw_map_meet group meet hg xyz (code.entry_action xx')
    (code.entry_action yy') (code.entry_action zz')

theorem image_iff {G m inv e : ZFSet.{u}} (group : GroupCode G m inv e)
    (action : PosetActionCode G P m e r A) (order : PartialOrderCode P r)
    (hg : g ∈ G) {y : ZFSet.{u}} :
    (∃ x ∈ attachmentIdeal P r source, ZFSet.pair x y ∈ base) ↔
      y ∈ attachmentIdeal P r target := by
  constructor
  · rintro ⟨x, hx, entry⟩
    have hy := (ZFSet.pair_mem_prod.1 (code.shape entry)).2
    exact (mem_attachmentIdeal P r target y).2 ⟨hy,
      (action.raw_order_iff group order hg (code.entry_action entry) code.target_entry).2
        ((mem_attachmentIdeal P r source x).1 hx).2⟩
  · intro hy
    have parts := (mem_attachmentIdeal P r target y).1 hy
    obtain ⟨x, hx, entry⟩ := action.raw_preimage group hg parts.1
    have lower := (action.raw_order_iff group order hg entry code.target_entry).1 parts.2
    exact ⟨x, (mem_attachmentIdeal P r source x).2 ⟨hx, lower⟩,
      (code.entries x hx y parts.1).2 ⟨lower, entry⟩⟩

theorem singleAttachmentInputs {G m inv e μ F separator : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hg : g ∈ G) (hsource : source ∈ P)
    (htarget : target ∈ P) (filter : MeetFilterCode P r μ F)
    (hseparator : separator ∈ P) (lower : ZFSet.pair target separator ∈ r)
    (strict : ZFSet.pair separator target ∉ r)
    (upper : ∀ y ∈ F, ZFSet.pair separator y ∈ r) :
    SingleAttachmentInputs P P r r μ μ base F source separator := by
  have function := code.base_function action hg
  have targetEntry := code.source_entry meet.order hsource htarget
  have value_eq (b : ZFSet.{u}) (entry : ZFSet.pair source b ∈ base) : b = target := by
    obtain ⟨v, _, unique⟩ := function.2 source
      ((mem_attachmentIdeal P r source source).2 ⟨hsource, meet.order.refl source hsource⟩)
    exact (unique b entry).trans (unique target targetEntry).symm
  exact {
    oldOrder := meet
    templateOrder := meet
    anchor_mem := hsource
    base_function := function
    base_order := fun _ _ _ _ xx' yy' => code.base_order group action meet.order hg xx' yy'
    base_meet := fun _ _ _ _ _ _ xyz xx' yy' zz' => code.base_meet group action meet hg xyz xx' yy' zz'
    filter := filter
    separator_mem := hseparator
    base_le_separator := fun b entry => (value_eq b entry).symm ▸ lower
    separator_not_le_base := fun b entry => (value_eq b entry).symm ▸ strict
    separator_le_upper := upper }

end RestrictedActionCode

noncomputable def actionPostcompose (P A g base : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun v => ∃ x ∈ P, ∃ z ∈ P, v = ZFSet.pair x z ∧
    ∃ y ∈ P, ZFSet.pair x y ∈ base ∧ ZFSet.pair (ZFSet.pair g y) z ∈ A) (ZFSet.prod P P)

theorem actionPostcompose_subset (P A g base : ZFSet.{u}) :
    actionPostcompose P A g base ⊆ ZFSet.prod P P :=
  fun _ hv => (ZFSet.mem_sep.1 hv).1

theorem pair_mem_actionPostcompose (P A g base x z : ZFSet.{u}) :
    ZFSet.pair x z ∈ actionPostcompose P A g base ↔
      x ∈ P ∧ z ∈ P ∧ ∃ y ∈ P,
        ZFSet.pair x y ∈ base ∧ ZFSet.pair (ZFSet.pair g y) z ∈ A := by
  rw [actionPostcompose, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hx, hz⟩, a, _, b, _, equal, witness⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx, hz, witness⟩
  · rintro ⟨hx, hz, witness⟩
    exact ⟨⟨hx, hz⟩, x, hx, z, hz, rfl, witness⟩

theorem PosetActionCode.raw_mul_iff {G P m e r A g h k x z : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (hg : g ∈ G) (hh : h ∈ G) (hk : k ∈ G)
    (product : ZFSet.pair (ZFSet.pair g h) k ∈ m) (hx : x ∈ P) (hz : z ∈ P) :
    ZFSet.pair (ZFSet.pair k x) z ∈ A ↔
      ∃ y ∈ P, ZFSet.pair (ZFSet.pair h x) y ∈ A ∧ ZFSet.pair (ZFSet.pair g y) z ∈ A := by
  constructor
  · intro entry
    obtain ⟨y, first, _⟩ := action.function.2 (ZFSet.pair h x)
      (ZFSet.pair_mem_prod.2 ⟨hh, hx⟩)
    have hy := (ZFSet.pair_mem_prod.1 (action.function.1 first)).2
    obtain ⟨w, second, _⟩ := action.function.2 (ZFSet.pair g y)
      (ZFSet.pair_mem_prod.2 ⟨hg, hy⟩)
    have hw := (ZFSet.pair_mem_prod.1 (action.function.1 second)).2
    have composed := action.mul g hg h hh k hk x hx y hy w hw product first second
    obtain ⟨v, _, unique⟩ := action.function.2 (ZFSet.pair k x)
      (ZFSet.pair_mem_prod.2 ⟨hk, hx⟩)
    have equal : w = z := (unique w composed).trans (unique z entry).symm
    exact ⟨y, hy, first, equal ▸ second⟩
  · rintro ⟨y, hy, first, second⟩
    exact action.mul g hg h hh k hk x hx y hy z hz product first second

theorem actionPostcompose_one {G P m e r A base : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (shape : base ⊆ ZFSet.prod P P) :
    actionPostcompose P A e base = base := by
  apply ZFSet.ext
  intro v
  constructor
  · intro hv
    obtain ⟨x, _, z, _, rfl⟩ := ZFSet.mem_prod.1 (actionPostcompose_subset P A e base hv)
    obtain ⟨_, _, y, hy, entry, acted⟩ := (pair_mem_actionPostcompose P A e base x z).1 hv
    have identity := action.one y hy
    obtain ⟨w, _, unique⟩ := action.function.2 (ZFSet.pair e y)
      (ZFSet.pair_mem_prod.1 (action.function.1 identity)).1
    have equal : z = y := (unique z acted).trans (unique y identity).symm
    exact equal.symm ▸ entry
  · intro hv
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (shape hv)
    exact (pair_mem_actionPostcompose P A e base x y).2
      ⟨hx, hy, y, hy, hv, action.one y hy⟩

theorem actionPostcompose_mul {G P m e r A base g h k : ZFSet.{u}}
    (action : PosetActionCode G P m e r A)
    (hg : g ∈ G) (hh : h ∈ G) (hk : k ∈ G)
    (product : ZFSet.pair (ZFSet.pair g h) k ∈ m) :
    actionPostcompose P A k base = actionPostcompose P A g (actionPostcompose P A h base) := by
  apply ZFSet.ext
  intro v
  constructor
  · intro hv
    obtain ⟨x, _, z, _, rfl⟩ := ZFSet.mem_prod.1 (actionPostcompose_subset P A k base hv)
    obtain ⟨hx, hz, y, hy, entry, acted⟩ := (pair_mem_actionPostcompose P A k base x z).1 hv
    obtain ⟨w, hw, first, second⟩ := (action.raw_mul_iff hg hh hk product hy hz).1 acted
    exact (pair_mem_actionPostcompose P A g (actionPostcompose P A h base) x z).2
      ⟨hx, hz, w, hw, (pair_mem_actionPostcompose P A h base x w).2
        ⟨hx, hw, y, hy, entry, first⟩, second⟩
  · intro hv
    obtain ⟨x, _, z, _, rfl⟩ := ZFSet.mem_prod.1
      (actionPostcompose_subset P A g (actionPostcompose P A h base) hv)
    obtain ⟨hx, hz, w, hw, entry, acted⟩ :=
      (pair_mem_actionPostcompose P A g (actionPostcompose P A h base) x z).1 hv
    obtain ⟨_, _, y, hy, first, second⟩ := (pair_mem_actionPostcompose P A h base x w).1 entry
    exact (pair_mem_actionPostcompose P A k base x z).2
      ⟨hx, hz, y, hy, first, (action.raw_mul_iff hg hh hk product hy hz).2
        ⟨w, hw, second, acted⟩⟩

theorem actionPostcompose_inverse {G P m inv e r A base g h : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (shape : base ⊆ ZFSet.prod P P) (hg : g ∈ G) (hh : h ∈ G)
    (inverse : ZFSet.pair g h ∈ inv) :
    actionPostcompose P A h (actionPostcompose P A g base) = base := by
  rw [← actionPostcompose_mul action hh hg group.identity_mem (group.inv_mul g hg h hh inverse)]
  exact actionPostcompose_one action shape

theorem RestrictedActionCode.transport {G P m e r A g δ k source target target' base : ZFSet.{u}}
    (code : RestrictedActionCode P r A g source target base)
    (action : PosetActionCode G P m e r A)
    (hg : g ∈ G) (hδ : δ ∈ G) (hk : k ∈ G)
    (product : ZFSet.pair (ZFSet.pair δ g) k ∈ m)
    (targetEntry : ZFSet.pair (ZFSet.pair δ target) target' ∈ A) :
    RestrictedActionCode P r A k source target' (actionPostcompose P A δ base) := by
  have firstShape := ZFSet.pair_mem_prod.1 (action.function.1 code.target_entry)
  have hsource := (ZFSet.pair_mem_prod.1 firstShape.1).2
  have htarget := firstShape.2
  have htarget' := (ZFSet.pair_mem_prod.1 (action.function.1 targetEntry)).2
  refine ⟨actionPostcompose_subset P A δ base,
    action.mul δ hδ g hg k hk source hsource target htarget target' htarget'
      product code.target_entry targetEntry, ?_⟩
  intro x hx z hz
  rw [pair_mem_actionPostcompose]
  constructor
  · rintro ⟨_, _, y, hy, entry, acted⟩
    have old := (code.entries x hx y hy).1 entry
    exact ⟨old.1, (action.raw_mul_iff hδ hg hk product hx hz).2 ⟨y, hy, old.2, acted⟩⟩
  · rintro ⟨lower, entry⟩
    obtain ⟨y, hy, first, second⟩ := (action.raw_mul_iff hδ hg hk product hx hz).1 entry
    exact ⟨hx, hz, y, hy, (code.entries x hx y hy).2 ⟨lower, first⟩, second⟩

end PartitionPilot.Forcing

end OAI
