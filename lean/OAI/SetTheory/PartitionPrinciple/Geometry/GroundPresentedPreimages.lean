import OAI.SetTheory.PartitionPrinciple.Definability.GroundFlatCopyGraphs

namespace OAI

section

namespace PartitionPilot.SetRealization.Presentation
open Forcing
universe u
variable {P Q : Type u} (s : Presentation P) (t : Presentation Q) (f : P → Q)

theorem preimageCode_eq (X : ZFSet.{u}) :
    s.subset (fun point => t.encode (f point) ∈ X) =
      relationImage X s.carrier (relationConverse s.carrier t.carrier (s.graph t f)) := by
  apply ZFSet.ext
  intro z
  rw [s.mem_subset, mem_relationImage]
  constructor
  · rintro ⟨p, member, rfl⟩
    exact ⟨s.encode_mem p, t.encode (f p), member,
      (pair_mem_relationConverse _ _ _ _ _).2
        ⟨s.encode_mem p, t.encode_mem (f p), (s.pair_mem_graph t f p (f p)).2 rfl⟩⟩
  · rintro ⟨_, y, member, entry⟩
    have raw := (pair_mem_relationConverse _ _ _ _ _).1 entry
    obtain ⟨p, equal⟩ := (s.mem_graph t f _).1 raw.2.2
    obtain ⟨left, right⟩ := ZFSet.pair_inj.1 equal
    exact ⟨p, by rw [right]; exact member, left⟩

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P Q : Type u}

theorem presentedPreimage_mem (s : Presentation P) (t : Presentation Q) (f : P → Q)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets) (graph : s.graph t f ∈ M.sets)
    {X : ZFSet.{u}} (hX : X ∈ M.sets) :
    s.subset (fun point => t.encode (f point) ∈ X) ∈ M.sets := by
  rw [s.preimageCode_eq t f X]
  exact M.relationImage_mem separation hX hs
    (M.relationConverse_mem pairing unions powers separation hs ht graph)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
