import OAI.SetTheory.PartitionPrinciple.Forcing.GroundSharedConditionalNames

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (J : Fin 3 → ZFSet.{u}) (hJ : ∀ i, J i ∈ M.sets)
variable (valid : ∀ i, ∀ z ∈ J i, IsName s z)
variable (env : Assignment (M.nameDomain s) 4)

noncomputable def refinementConditionAssignment : Assignment (M.nameDomain s) 4 :=
  let names : Fin 3 → (M.nameDomain s).names := fun i =>
    ⟨Name.refinementConditionNames (M.nameDomain s) env J valid i,
      M.sharedConditionName_mem s pairing unions powers separation collection carrier order
        BoundedFormula.refinementValidityFormula.toFormula env i.castSucc (hJ i) (valid i)⟩
  ![names 0, names 1, names 2, env 3]

theorem refinementConditionAssignment_entry (i : Fin 3) :
    ((M.refinementConditionAssignment s pairing unions powers separation collection
      carrier order J hJ valid env) i.castSucc).val =
      Name.refinementConditionNames (M.nameDomain s) env J valid i := by
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i

theorem refinementConditionAssignment_last :
    (M.refinementConditionAssignment s pairing unions powers separation collection
      carrier order J hJ valid env) 3 = env 3 := rfl

include pairing unions powers separation collection carrier order hJ in
theorem sharedRefinementValidity_top (small : M.sets.Countable)
    (shape : ∀ i : Fin 3, (env i.castSucc).val.val ⊆ ZFSet.prod (J i) s.carrier) :
    Forces (M.nameDomain s) BoundedFormula.refinementValidityFormula.toFormula
      (M.refinementConditionAssignment s pairing unions powers separation collection
        carrier order J hJ valid env) ⊤ := by
  apply (M.ordinaryForces_iff_all_generics s small carrier _ _ ⊤).2
  intro H _ generic
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {p | H.mem p},
      (M.nameDomain s).values_transitive {p | H.mem p}⟩
  let newEnv := M.refinementConditionAssignment s pairing unions powers separation collection
    carrier order J hJ valid env
  apply (evaluated.realize_refinementValidityFormula
    (evalAssignment {p | H.mem p} newEnv) (fun i => ⟨newEnv i, rfl⟩)).2
  have family : ∀ i, Name.familySet ⊤ (J i) (valid i) ∈ (M.nameDomain s).names :=
    fun i => M.familySet_mem s ⊤ pairing unions powers separation (hJ i)
      (M.transitive carrier (s.encode_mem ⊤)) (valid i)
  exact Name.eval_refinementConditionNames_valid (M.nameDomain s) env J valid
    family H generic shape

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
