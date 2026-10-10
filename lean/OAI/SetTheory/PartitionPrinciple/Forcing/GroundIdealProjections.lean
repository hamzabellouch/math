import OAI.SetTheory.PartitionPrinciple.Definability.MapFamilyApplicationGraphs

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression Compression.RecursiveMaps SetFormula
universe u

noncomputable def idealProjectionGraph (P L ν e cap : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose L L P (indexedRelationSection L L ν cap) (relationConverse P L e)

namespace TransitiveGround

theorem idealProjectionGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P L ν e cap : ZFSet.{u}} (hP : P ∈ M.sets) (hL : L ∈ M.sets)
    (hν : ν ∈ M.sets) (he : e ∈ M.sets) (hcap : cap ∈ M.sets) :
    idealProjectionGraph P L ν e cap ∈ M.sets :=
  M.relationCompose_mem pairing unions powers separation hL hL hP
    (M.indexedRelationSection_mem pairing unions powers separation hL hL hν hcap)
    (M.relationConverse_mem pairing unions powers separation hP hL he)

end TransitiveGround

variable {A B : Type u} (s : Presentation A) (t : Presentation B)
variable {P : MeetOrder A} {Q : MeetOrder B} (embedding : IdealEmbedding P Q) (top : A)
variable {ν : ZFSet.{u}}
variable (function : ZFSet.IsFunc (ZFSet.prod t.carrier t.carrier) t.carrier ν)
variable (entries : ∀ x y, ZFSet.pair (ZFSet.pair (t.encode x) (t.encode y))
  (t.encode (Q.meet x y)) ∈ ν)
include function entries

theorem idealProjectionGraph_pair_iff (x : B) (a : A) :
    ZFSet.pair (t.encode x) (s.encode a) ∈ idealProjectionGraph s.carrier t.carrier ν
      (s.graph t embedding.toFun) (t.encode (embedding.toFun top)) ↔
        embedding.projection top x = a := by
  constructor
  · intro entry
    obtain ⟨_, _, z, hz, meet, inverse⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    have image := ((pair_mem_relationConverse _ _ _ _ _).1 inverse).2.2
    obtain ⟨z', rfl⟩ := (t.mem_carrier z).1 hz
    have imageEq := (s.pair_mem_graph t embedding.toFun a z').1 image
    have rawMeet := ((pair_mem_indexedRelationSection _ _ _ _ _ _).1 meet).2.2
    obtain ⟨v, _, unique⟩ := function.2
      (ZFSet.pair (t.encode (embedding.toFun top)) (t.encode x))
      (ZFSet.pair_mem_prod.2 ⟨t.encode_mem _, t.encode_mem _⟩)
    have eq := t.injective ((unique _ rawMeet).trans (unique _ (entries _ _)).symm)
    apply embedding_injective embedding.toMeetEmbedding
    rw [embedding.projection_spec, imageEq, eq, meet_comm]
  · intro equal
    subst a
    apply (pair_mem_relationCompose _ _ _ _ _ _ _).2
    refine ⟨t.encode_mem x, s.encode_mem _, t.encode (embedding.toFun (embedding.projection top x)),
      t.encode_mem _, ?_, ?_⟩
    · apply (pair_mem_indexedRelationSection _ _ _ _ _ _).2
      refine ⟨t.encode_mem _, t.encode_mem _, ?_⟩
      rw [embedding.projection_spec, meet_comm Q x]
      exact entries _ _
    · exact (pair_mem_relationConverse _ _ _ _ _).2
        ⟨s.encode_mem _, t.encode_mem _, (s.pair_mem_graph t embedding.toFun _ _).2 rfl⟩

theorem idealProjectionGraph_eq :
    idealProjectionGraph s.carrier t.carrier ν (s.graph t embedding.toFun)
      (t.encode (embedding.toFun top)) = t.graph s (embedding.projection top) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, _, _, a, ha, rfl, _, _⟩ := (mem_relationCompose _ _ _ _ _ _).1 hz
    obtain ⟨x, rfl⟩ := (t.mem_carrier x).1 hx
    obtain ⟨a, rfl⟩ := (s.mem_carrier a).1 ha
    exact (t.pair_mem_graph s _ _ _).2 ((idealProjectionGraph_pair_iff s t embedding top function entries x a).1 hz)
  · intro hz
    obtain ⟨x, rfl⟩ := (t.mem_graph s (embedding.projection top) z).1 hz
    exact (idealProjectionGraph_pair_iff s t embedding top function entries _ _).2 rfl

namespace TransitiveGround

theorem idealProjection_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hP : s.carrier ∈ M.sets) (hL : t.carrier ∈ M.sets) (hν : ν ∈ M.sets)
    (he : s.graph t embedding.toFun ∈ M.sets) :
    t.graph s (embedding.projection top) ∈ M.sets := by
  rw [← idealProjectionGraph_eq s t embedding top function entries]
  exact M.idealProjectionGraph_mem pairing unions powers separation hP hL hν he
    (M.transitive hL (t.encode_mem _))

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
