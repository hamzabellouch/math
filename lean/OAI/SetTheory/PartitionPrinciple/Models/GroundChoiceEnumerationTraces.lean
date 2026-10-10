import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundOrdinalEnumerationFamilies

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_choiceEnumerationTrace
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {A c T : ZFSet.{u}} (hA : A ∈ M.sets) (hc : c ∈ M.sets)
    (hT : T ∈ M.sets) (ordinal : ordinalSetProperty T)
    (code : ChoiceFunctionCode (M.nonemptyGroundSubsets A) c) :
    ∃ f ∈ M.sets,
      OrdinalRecursionTrace (ChoiceEnumerationStep A (M.nonemptyGroundSubsets A) c) T f := by
  let F := M.nonemptyGroundSubsets A
  have hF : F ∈ M.sets := M.nonemptyGroundSubsets_mem powers separation hA
  let params := extend A (extend F (extend c Fin.elim0))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hA (Fin.cases hF (Fin.cases hc (fun i => Fin.elim0 i)))
  let formula : BoundedFormula 6 := BoundedFormula.choiceEnumerationStepFormula 3 4 5 0 1 2
  have recognize (a p y : ZFSet.{u}) (ha : a ∈ M.sets) (hp : p ∈ M.sets)
      (hy : y ∈ M.sets) :
      Realize M.sets formula.toFormula (extend a (extend p (extend y params))) ↔
        ChoiceEnumerationStep A F c a p y :=
    (BoundedFormula.realize_toFormula M formula _
      (Fin.cases ha (Fin.cases hp (Fin.cases hy members)))).trans
      (BoundedFormula.truth_choiceEnumerationStepFormula 3 4 5 0 1 2 _)
  have closure : GroundOrdinalStepClosure M T formula.toFormula params := by
    intro a ha p hp _
    have haM := M.transitive hT ha
    obtain ⟨y, hy, step, unique⟩ :=
      M.choiceEnumerationStep_exists_unique separation hA haM hp code
    exact ⟨y, hy, (recognize a p y haM hp hy).2 step,
      fun z hz relation => unique z ((recognize a p z haM hp hz).1 relation)⟩
  obtain ⟨f, hf, trace⟩ := M.exists_ordinalRecursionTrace pairing unions separation collection
    hT ordinal formula.toFormula params members closure
  refine ⟨f, hf, trace.1, ?_⟩
  intro a ha y entry
  have step := trace.2 a ha y entry
  exact (recognize a _ y (M.transitive hT ha) step.1 step.2.1).1 step.2.2

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
