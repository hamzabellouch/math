import OAI.SetTheory.PartitionPrinciple.Definability.FixedTopCodes

namespace OAI

section

namespace PartitionPilot.SetRealization.Presentation
open Forcing Compression.RecursiveMaps.CosetGeometry
universe u
variable {A : Type u} (s : Presentation A) (P : MeetOrder A) {r : ZFSet.{u}}
variable (shape : r ⊆ ZFSet.prod s.carrier s.carrier)
variable (related : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ r ↔ P.le x y)

include shape related in
theorem partialOrderCode : PartialOrderCode s.carrier r := by
  refine ⟨shape, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    exact (related x x).2 (P.refl x)
  · intro x hx y hy xy yx
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    exact congrArg s.encode (P.antisymm ((related x y).1 xy) ((related y x).1 yx))
  · intro x hx y hy z hz xy yz
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    obtain ⟨z, rfl⟩ := (s.mem_carrier z).1 hz
    exact (related x z).2 (P.trans ((related x y).1 xy) ((related y z).1 yz))

include shape related in
theorem canonicalMeetOrderCode : MeetOrderCode s.carrier r (canonicalMeetGraph s.carrier r) := by
  apply canonicalMeetGraph_code (s.partialOrderCode P shape related)
  intro x hx y hy
  obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
  obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
  refine ⟨s.encode (P.meet x y), s.encode_mem _, (related _ _).2 (P.meet_le_left x y),
    (related _ _).2 (P.meet_le_right x y), ?_⟩
  intro w hw wx wy
  obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
  exact (related _ _).2 (P.le_meet ((related _ _).1 wx) ((related _ _).1 wy))

include related in
theorem canonicalMeetGraph_iff (x y z : A) :
    ZFSet.pair (ZFSet.pair (s.encode x) (s.encode y)) (s.encode z) ∈
      canonicalMeetGraph s.carrier r ↔ P.meet x y = z := by
  rw [pair_mem_canonicalMeetGraph]
  constructor
  · rintro ⟨_, _, _, left, right, greatest⟩
    apply P.antisymm
    · exact (related _ _).1 (greatest (s.encode (P.meet x y)) (s.encode_mem _)
        ((related _ _).2 (P.meet_le_left x y)) ((related _ _).2 (P.meet_le_right x y)))
    · exact P.le_meet ((related _ _).1 left) ((related _ _).1 right)
  · rintro rfl
    refine ⟨s.encode_mem _, s.encode_mem _, s.encode_mem _,
      (related _ _).2 (P.meet_le_left x y), (related _ _).2 (P.meet_le_right x y), ?_⟩
    intro w hw wx wy
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    exact (related _ _).2 (P.le_meet ((related _ _).1 wx) ((related _ _).1 wy))

variable {G : Type u} [Group G] (t : Presentation G) (a : OrderAction G P)
include related in
theorem posetActionCode : PosetActionCode t.carrier s.carrier
    ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1) r
    ((t.product s).graph s (fun gx => (a.iso gx.1).toFun gx.2)) := by
  refine ⟨(t.product s).graph_isFunc s _, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    exact ((t.product s).pair_mem_graph s _ (1, x) x).2 (a.one x)
  · intro g hg h hh k hk x hx y hy z hz gh xy yz
    obtain ⟨g, rfl⟩ := (t.mem_carrier g).1 hg
    obtain ⟨h, rfl⟩ := (t.mem_carrier h).1 hh
    obtain ⟨k, rfl⟩ := (t.mem_carrier k).1 hk
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    obtain ⟨z, rfl⟩ := (s.mem_carrier z).1 hz
    have product := ((t.product t).pair_mem_graph t _ (g, h) k).1 gh
    have first := ((t.product s).pair_mem_graph s _ (h, x) y).1 xy
    have second := ((t.product s).pair_mem_graph s _ (g, y) z).1 yz
    apply ((t.product s).pair_mem_graph s _ (k, x) z).2
    rw [← product, a.mul, first, second]
  · intro g hg x hx y hy z hz w hw xz yw xy
    obtain ⟨g, rfl⟩ := (t.mem_carrier g).1 hg
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    obtain ⟨z, rfl⟩ := (s.mem_carrier z).1 hz
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    have first := ((t.product s).pair_mem_graph s _ (g, x) z).1 xz
    have second := ((t.product s).pair_mem_graph s _ (g, y) w).1 yw
    apply (related z w).2
    rw [← first, ← second]
    exact ((a.iso g).le_iff x y).2 ((related x y).1 xy)

end PartitionPilot.SetRealization.Presentation

end

end OAI
