import OAI.SetTheory.PartitionPrinciple.Forcing.GroundProjectedRowChooserWitnesses

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]

theorem exists_ordinalPartialMapCover
    (s : Presentation P) (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets)
    {W f : ZFSet.{u}} (hW : W ∈ M.sets) (hf : f ∈ M.sets)
    (function : FunctionGraphOn W f) (names : ∀ i, IsName s (function.value i))
    (fixed : ∀ g i, a.act s g ⟨function.value i, names i⟩ = ⟨function.value i, names i⟩)
    (children : ∀ i, HereditarilySymmetric a s F ⟨function.value i, names i⟩)
    (H : ConditionFilter P) (Trow X : ZFSet.{u})
    (partialMaps : ∀ i : W.toSet,
      let hi := Name.eval {p | H.mem p} (⟨function.value i, names i⟩ : Name s)
      PartialFunctionCode Trow (⋃₀ ⋃₀ hi) hi)
    (covers : ∀ x ∈ X, ∃ i : W.toSet, ∃ u ∈ Trow,
      ZFSet.pair u x ∈ Name.eval {p | H.mem p} (⟨function.value i, names i⟩ : Name s)) :
    let N := M.symmetricExtension s a F H
    ∃ delta ∈ N.sets, ordinalSetProperty delta ∧
      ∃ h ∈ N.sets, FunctionGraphOn delta h ∧
        (∀ i hi, ZFSet.pair i hi ∈ h → PartialFunctionCode Trow (⋃₀ ⋃₀ hi) hi) ∧
        ∀ x ∈ X, ∃ i ∈ delta, ∃ hi, ZFSet.pair i hi ∈ h ∧
          ∃ u ∈ Trow, ZFSet.pair u x ∈ hi := by
  intro N
  obtain ⟨delta, hDelta, ordinal, q, _hq, qFunction, qNames, _fixed, _children,
    forward, backward, sequences⟩ := M.exists_groundOrdinalFixedNameSequence s a F
      pairing unions powers separation collection choice carrier hW hf function names fixed children
  have sequenceData := sequences H
  dsimp only at sequenceData
  let sequence := Name.indexedGraphName (s := s) (⊤ : P) qFunction qNames
  let h := Name.eval {p | H.mem p} sequence
  have hFunction : FunctionGraphOn delta h := ⟨_, sequenceData.2.2.1⟩
  have groundSubset := M.ground_subset_symmetricExtension s a F
    pairing unions powers separation collection carrier H
  refine ⟨delta, groundSubset hDelta, ordinal, h, sequenceData.2.2.2, hFunction, ?_, ?_⟩
  · intro i hi entry
    let j : delta.toSet := ⟨i, hFunction.pair_source entry⟩
    have value := (Name.pair_mem_eval_indexedTuple {p | H.mem p} (⊤ : P) H.top_mem delta
      (fun j => ⟨qFunction.value j, qNames j⟩) j hi).1 entry
    obtain ⟨k, same⟩ := backward j
    have equal := (congrArg (Name.eval {p | H.mem p}) same).symm.trans value
    exact Eq.mp (congrArg (fun v => PartialFunctionCode Trow (⋃₀ ⋃₀ v) v) equal) (partialMaps k)
  · intro x member
    obtain ⟨i, u, inRow, edge⟩ := covers x member
    obtain ⟨j, same⟩ := forward i
    let hi := Name.eval {p | H.mem p} (⟨qFunction.value j, qNames j⟩ : Name s)
    refine ⟨j.val, j.property, hi,
      (Name.pair_mem_eval_indexedTuple {p | H.mem p} (⊤ : P) H.top_mem delta
        (fun j => ⟨qFunction.value j, qNames j⟩) j hi).2 rfl, u, inRow, ?_⟩
    exact Eq.mpr (congrArg (fun v => ZFSet.pair u x ∈ v)
      (congrArg (Name.eval {p | H.mem p}) same)) edge

end PartitionPilot.Forcing.TransitiveGround

end OAI
