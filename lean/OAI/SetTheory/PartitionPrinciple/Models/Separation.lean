import OAI.SetTheory.PartitionPrinciple.Definability.PartitionPrincipleFormula
import OAI.SetTheory.PartitionPrinciple.Models.GroundMainFinalPartitionModel

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem exists_partitionPrinciple_without_choice
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    ∃ N : TransitiveGround.{u}, M.sets ⊆ N.sets ∧ ZFRealization N.sets ∧
      (∀ X ∈ N.sets, ∀ Y ∈ N.sets, ∀ f ∈ N.sets, ZFSet.IsFunc X Y f →
        (∀ y ∈ Y, ∃ x ∈ X, ZFSet.pair x y ∈ f) → N.groundEmbeddable Y X) ∧
      ¬ Realize N.sets SetFormula.choice Fin.elim0 := by
  obtain ⟨data, ordinalC, original⟩ :=
    M.exists_groundMainFinalSupport pairing unions powers separation collection infinite choice hK standard
  let := ordinalMainIndexPreorder ordinalC
  obtain ⟨run, _indices, _profiles, _terminal, _extension, _unique, indexBound, _rank,
    i0, _zero, fulfilled, _geometryProperties⟩ := original
  exact fulfilled.exists_partitionPrinciple_not_choice collection infinite choice small hK standard
    indexBound rfl ⟨data.seed.coordinateInjection, data.seed.injection_ground, data.seed.injection_code⟩
    data.seed.dense.irrefl

theorem exists_model_partitionPrinciple_without_choice
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    ∃ N : TransitiveGround.{u}, M.sets ⊆ N.sets ∧ ZFRealization N.sets ∧
      Realize N.sets partitionPrinciple Fin.elim0 ∧
      ¬ Realize N.sets SetFormula.choice Fin.elim0 := by
  obtain ⟨N, includes, zf, pp, notChoice⟩ := M.exists_partitionPrinciple_without_choice
    pairing unions powers separation collection infinite choice small hK standard
  exact ⟨N, includes, zf, (N.realize_partitionPrinciple).2 pp, notChoice⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
