import OAI.SetTheory.PartitionPrinciple.Forcing.GroundSizeWitnesses

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_surjectionFormula {n : Nat} (a b f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (surjectionFormula a b f) env ↔ ZFSet.IsFunc (env a) (env b) (env f) ∧
      ∀ y ∈ env b, ∃ x ∈ env a, ZFSet.pair x y ∈ env f := by
  simp only [surjectionFormula, Truth, truth_functionFormula, truth_exMem,
    truth_pairMembershipFormula]
  rfl

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.SetFormula

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u

theorem realize_partitionPrinciple (M : TransitiveGround.{u}) :
    Realize M.sets partitionPrinciple Fin.elim0 ↔
      ∀ X ∈ M.sets, ∀ Y ∈ M.sets, ∀ f ∈ M.sets, ZFSet.IsFunc X Y f →
        (∀ y ∈ Y, ∃ x ∈ X, ZFSet.pair x y ∈ f) → M.groundEmbeddable Y X := by
  change (∀ X ∈ M.sets, ∀ Y ∈ M.sets, ∀ f ∈ M.sets,
    Realize M.sets (imp (BoundedFormula.surjectionFormula (n := 3) 2 1 0).toFormula
      (hasInjectionFormula (n := 3) 1 2)) (extend f (extend Y (extend X Fin.elim0)))) ↔ _
  apply forall_congr' fun X => forall_congr' fun hX =>
    forall_congr' fun Y => forall_congr' fun hY =>
    forall_congr' fun f => forall_congr' fun hf => ?_
  let env := extend f (extend Y (extend X Fin.elim0))
  have members : ∀ j, env j ∈ M.sets :=
    Fin.cases hf (Fin.cases hY (Fin.cases hX (fun j => Fin.elim0 j)))
  rw [realize_imp, M.realize_hasInjectionFormula 1 2 env members,
    BoundedFormula.realize_toFormula M _ env members, BoundedFormula.truth_surjectionFormula]
  exact ⟨fun h function onto => h ⟨function, onto⟩,
    fun h ⟨function, onto⟩ => h function onto⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
