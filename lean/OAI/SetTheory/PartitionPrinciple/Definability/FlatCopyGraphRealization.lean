import OAI.SetTheory.PartitionPrinciple.Forcing.PresentedMeetActionCodes
import OAI.SetTheory.PartitionPrinciple.Models.ExternalCopyQuotient

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : TileRequests.Family P R) (a : OrderAction J P)
variable (s : Presentation (External J f.Letters)) (t : Presentation A) (q : Presentation (f.Node a))
variable {classifier r : ZFSet.{u}}
variable (classed : ∀ w x z, ZFSet.pair (ZFSet.pair (s.encode w) (t.encode x)) (q.encode z) ∈ classifier ↔
  (f.copy a w).toFun x = z)
variable (related : ∀ x y, ZFSet.pair (t.encode x) (t.encode y) ∈ r ↔ P.le x y)

include classed related in
theorem flatCopy_order_iff (x y : f.Node a) :
    ZFSet.pair (q.encode x) (q.encode y) ∈
      flatCopyOrderGraph s.carrier t.carrier q.carrier classifier r ↔ (f.gluedOrder a).le x y := by
  rw [pair_mem_flatCopyOrderGraph]
  constructor
  · rintro ⟨_, _, w, hw, b, hb, c, hc, bc, bx, cy⟩
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    obtain ⟨b, rfl⟩ := (t.mem_carrier b).1 hb
    obtain ⟨c, rfl⟩ := (t.mem_carrier c).1 hc
    rw [← (classed w b x).1 bx, ← (classed w c y).1 cy]
    exact ((f.copy a w).le_iff b c).2 ((related b c).1 bc)
  · intro xy
    obtain ⟨w, b, c, bx, cy, bc⟩ := f.comparison_in_copy a x y xy
    exact ⟨q.encode_mem x, q.encode_mem y, s.encode w, s.encode_mem w,
      t.encode b, t.encode_mem b, t.encode c, t.encode_mem c,
      (related b c).2 bc, (classed w b x).2 bx, (classed w c y).2 cy⟩

include classed in
theorem flatCopy_action_iff (g : External J f.Letters) (x y : f.Node a) :
    ZFSet.pair (ZFSet.pair (s.encode g) (q.encode x)) (q.encode y) ∈
      flatCopyActionGraph s.carrier t.carrier q.carrier classifier
        ((s.product s).graph s (fun gh => gh.1 * gh.2)) ↔ f.translate a g x = y := by
  rw [pair_mem_flatCopyActionGraph]
  constructor
  · rintro ⟨_, _, _, w, hw, v, hv, b, hb, gw, wx, vy⟩
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    obtain ⟨v, rfl⟩ := (s.mem_carrier v).1 hv
    obtain ⟨b, rfl⟩ := (t.mem_carrier b).1 hb
    have product := ((s.product s).pair_mem_graph s _ (g, w) v).1 gw
    rw [← (classed w b x).1 wx, f.translate_copy, product]
    exact (classed v b y).1 vy
  · intro xy
    obtain ⟨w, b, rfl⟩ := f.copy_cover a x
    refine ⟨s.encode_mem g, q.encode_mem _, q.encode_mem y, s.encode w, s.encode_mem w,
      s.encode (g * w), s.encode_mem _, t.encode b, t.encode_mem b,
      ((s.product s).pair_mem_graph s _ (g, w) (g * w)).2 rfl, (classed w b _).2 rfl, ?_⟩
    exact (classed (g * w) b y).2 ((f.translate_copy a g w b).symm.trans xy)

include classed in
theorem flatCopy_action_eq_graph :
    flatCopyActionGraph s.carrier t.carrier q.carrier classifier
      ((s.product s).graph s (fun gh => gh.1 * gh.2)) =
      (s.product q).graph q (fun gx => f.translate a gx.1 gx.2) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨g, hg, x, hx, y, hy, rfl, _⟩ := (mem_flatCopyActionGraph _ _ _ _ _ z).1 hz
    obtain ⟨g, rfl⟩ := (s.mem_carrier g).1 hg
    obtain ⟨x, rfl⟩ := (q.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (q.mem_carrier y).1 hy
    exact ((s.product q).pair_mem_graph q _ (g, x) y).2
      ((flatCopy_action_iff f a s t q classed g x y).1 hz)
  · intro hz
    obtain ⟨⟨g, x⟩, rfl⟩ := ((s.product q).mem_graph q _ z).1 hz
    exact (flatCopy_action_iff f a s t q classed g x _).2 rfl

include classed related in
theorem flatCopy_meetOrder :
    MeetOrderCode q.carrier (flatCopyOrderGraph s.carrier t.carrier q.carrier classifier r)
      (canonicalMeetGraph q.carrier (flatCopyOrderGraph s.carrier t.carrier q.carrier classifier r)) :=
  q.canonicalMeetOrderCode (f.gluedOrder a) (fun _ hz => (ZFSet.mem_sep.1 hz).1)
    (flatCopy_order_iff f a s t q classed related)

include classed related in
theorem flatCopy_actionCode :
    PosetActionCode s.carrier q.carrier ((s.product s).graph s (fun gh => gh.1 * gh.2)) (s.encode 1)
      (flatCopyOrderGraph s.carrier t.carrier q.carrier classifier r)
      (flatCopyActionGraph s.carrier t.carrier q.carrier classifier
        ((s.product s).graph s (fun gh => gh.1 * gh.2))) := by
  rw [flatCopy_action_eq_graph f a s t q classed]
  exact q.posetActionCode (f.gluedOrder a) (flatCopy_order_iff f a s t q classed related) s (f.externalAction a)

end PartitionPilot.Forcing

end

end OAI
