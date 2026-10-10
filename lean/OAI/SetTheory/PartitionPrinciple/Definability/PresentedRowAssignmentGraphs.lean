import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRawRefinementStageWitnesses

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {G R : Type u} [Group G] [PartialOrder R]
variable (a : PosetAction G R) (c : Presentation R) (t : Presentation G)
variable (Q J B : ZFSet.{u})

theorem presentedRowAssignmentGraph_entry (g : G) (r q : R) (A D : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (t.encode g) (ZFSet.pair (c.encode r) A)) (ZFSet.pair (c.encode q) D) ∈
      rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q) J (a.actionGraph c t) B ↔
    ZFSet.pair (c.encode r) A ∈ Q ∧ ZFSet.pair (c.encode q) D ∈ Q ∧
      a.iso g r = q ∧ D = relationImage A J (rawActionSection (t.encode g) B J) := by
  rw [pair_mem_rawRowAssignmentActionGraph]
  constructor
  · rintro ⟨_, first, second, _, _, _, _, row, image⟩
    exact ⟨first, second, (a.triple_mem_actionGraph c t g r q).1 row, image⟩
  · rintro ⟨first, second, row, image⟩
    exact ⟨t.encode_mem g, first, second, c.encode_mem r, pair_second_mem_doubleUnion first,
      c.encode_mem q, pair_second_mem_doubleUnion second,
      (a.triple_mem_actionGraph c t g r q).2 row, image⟩

theorem presentedRowAssignmentGraph_bound :
    rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q) J (a.actionGraph c t) B ⊆
      ZFSet.prod (ZFSet.prod t.carrier Q) Q := by
  intro z hz
  unfold rawRowAssignmentActionGraph rowAssignmentActionGraph at hz
  exact (ZFSet.mem_sep.1 hz).1

omit [PartialOrder R] in
theorem exists_presentedRowAssignmentCoordinates
    {Q V z : ZFSet.{u}} (shape : Q ⊆ ZFSet.prod c.carrier V) (member : z ∈ Q) :
    ∃ r : R, ∃ A ∈ V, z = ZFSet.pair (c.encode r) A := by
  obtain ⟨r, hr, A, hA, rfl⟩ := ZFSet.mem_prod.1 (shape member)
  obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
  exact ⟨r, A, hA, rfl⟩

theorem presentedRowAssignmentGraph_function {V : ZFSet.{u}}
    (shape : Q ⊆ ZFSet.prod c.carrier V)
    (preserves : ∀ g : G, ∀ r : R, ∀ A,
      ZFSet.pair (c.encode r) A ∈ Q →
      ZFSet.pair (c.encode (a.iso g r)) (relationImage A J (rawActionSection (t.encode g) B J)) ∈ Q) :
    ZFSet.IsFunc (ZFSet.prod t.carrier Q) Q
      (rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q) J (a.actionGraph c t) B) := by
  refine ⟨presentedRowAssignmentGraph_bound a c t Q J B, ?_⟩
  intro z hz
  obtain ⟨g, hg, p, hp, rfl⟩ := ZFSet.mem_prod.1 hz
  obtain ⟨g, rfl⟩ := (t.mem_carrier g).1 hg
  obtain ⟨r, A, _, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hp
  refine ⟨ZFSet.pair (c.encode (a.iso g r)) (relationImage A J (rawActionSection (t.encode g) B J)),
    (presentedRowAssignmentGraph_entry a c t Q J B g r _ A _).2
      ⟨hp, preserves g r A hp, rfl, rfl⟩, ?_⟩
  intro y edge
  have hy := (ZFSet.pair_mem_prod.1 (presentedRowAssignmentGraph_bound a c t Q J B edge)).2
  obtain ⟨q, D, _, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hy
  obtain ⟨_, _, row, rfl⟩ := (presentedRowAssignmentGraph_entry a c t Q J B g r q A D).1 edge
  rw [row]

end PartitionPilot.Forcing

end

end OAI
