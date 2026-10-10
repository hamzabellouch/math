import OAI.SetTheory.PartitionPrinciple.Definability.PresentedGroupCodes

namespace OAI

section

namespace PartitionPilot.SetRealization.Presentation

universe u
variable {A B : Type u} (s : Presentation A) (t : Presentation B)

theorem exists_graph_value (f : ZFSet.{u}) (h : ZFSet.IsFunc s.carrier t.carrier f) (a : A) :
    ∃ b, ZFSet.pair (s.encode a) (t.encode b) ∈ f := by
  obtain ⟨y, rel, _⟩ := h.2 (s.encode a) (s.encode_mem a)
  have hy := (ZFSet.pair_mem_prod.1 (h.1 rel)).2
  obtain ⟨b, rfl⟩ := (t.mem_carrier y).1 hy
  exact ⟨b, rel⟩

noncomputable def decodeFunction (f : ZFSet.{u}) (h : ZFSet.IsFunc s.carrier t.carrier f) : A → B :=
  fun a => Classical.choose (s.exists_graph_value t f h a)

theorem decodeFunction_mem (f : ZFSet.{u}) (h : ZFSet.IsFunc s.carrier t.carrier f) (a : A) :
    ZFSet.pair (s.encode a) (t.encode (s.decodeFunction t f h a)) ∈ f :=
  Classical.choose_spec (s.exists_graph_value t f h a)

theorem decodeFunction_iff (f : ZFSet.{u}) (h : ZFSet.IsFunc s.carrier t.carrier f) (a : A) (b : B) :
    s.decodeFunction t f h a = b ↔ ZFSet.pair (s.encode a) (t.encode b) ∈ f := by
  constructor
  · intro eq
    simpa only [eq] using s.decodeFunction_mem t f h a
  · intro rel
    obtain ⟨y, _, unique⟩ := h.2 (s.encode a) (s.encode_mem a)
    apply t.injective
    exact (unique _ (s.decodeFunction_mem t f h a)).trans (unique _ rel).symm

theorem graph_decodeFunction (f : ZFSet.{u}) (h : ZFSet.IsFunc s.carrier t.carrier f) :
    s.graph t (s.decodeFunction t f h) = f := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨a, eq⟩ := (s.mem_graph t (s.decodeFunction t f h) z).1 hz
    exact eq ▸ s.decodeFunction_mem t f h a
  · intro hz
    obtain ⟨x, hx, y, hy, eq⟩ := ZFSet.mem_prod.1 (h.1 hz)
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (t.mem_carrier y).1 hy
    rw [eq, s.pair_mem_graph]
    exact (s.decodeFunction_iff t f h a b).2 (eq ▸ hz)

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization
universe u
variable (M : TransitiveGround.{u}) {A B : Type u}

theorem decoded_function_graph_mem (s : Presentation A) (t : Presentation B) {f : ZFSet.{u}}
    (hf : f ∈ M.sets) (h : ZFSet.IsFunc s.carrier t.carrier f) :
    s.graph t (s.decodeFunction t f h) ∈ M.sets := by
  rw [s.graph_decodeFunction]
  exact hf

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
