import OAI.SetTheory.PartitionPrinciple.Geometry.GroundFiniteWordLaws

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem finiteWordMapGraph_injection
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {A B e : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (code : InjectionCode A B e) :
    InjectionCode (M.finiteWords A) (M.finiteWords B) (M.finiteWordMapGraph A B e) := by
  let s := SetMembers.presentation A
  let t := SetMembers.presentation B
  let map := s.decodeFunction t e code.function
  have graph : s.graph t map = e := s.graph_decodeFunction t e code.function
  rw [← graph]
  change InjectionCode (M.finiteWords s.carrier) (M.finiteWords t.carrier)
    (M.finiteWordMapGraph s.carrier t.carrier (s.graph t map))
  rw [M.finiteWordMapGraph_eq_graph pairing unions separation infinite s t map hA hB]
  exact (finiteWordPresentation s M pairing unions separation infinite hA).graph_injection
    (finiteWordPresentation t M pairing unions separation infinite hB) (List.map map)
      (List.map_injective_iff.2 code.decoded_injective)

theorem finiteWordMapGraph_ground_injection
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {A B e : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (he : e ∈ M.sets)
    (code : InjectionCode A B e) :
    M.finiteWordMapGraph A B e ∈ M.sets ∧
      InjectionCode (M.finiteWords A) (M.finiteWords B) (M.finiteWordMapGraph A B e) :=
  ⟨M.finiteWordMapGraph_mem pairing unions powers separation infinite hA hB he,
    M.finiteWordMapGraph_injection pairing unions separation infinite hA hB code⟩

theorem groundEmbeddable_finiteWords
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (injection : M.groundEmbeddable A B) :
    M.groundEmbeddable (M.finiteWords A) (M.finiteWords B) := by
  obtain ⟨e, he, code⟩ := injection
  exact ⟨M.finiteWordMapGraph A B e,
    M.finiteWordMapGraph_ground_injection pairing unions powers separation infinite hA hB he code⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
