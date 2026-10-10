import OAI.SetTheory.PartitionPrinciple.Definability.RefinementValidityCodes

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace SetFormula

def refinementValidityForcingFormula {n : Nat}
    (U Rf Rc T carrier order condition : Fin n) : SetFormula n :=
  forcingTranslation (ordinaryGroundPrimitives (0 : Fin 2) 1)
    BoundedFormula.refinementValidityFormula.toFormula
    (extend carrier (extend order Fin.elim0)) condition
    (extend U (extend Rf (extend Rc (extend T Fin.elim0))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_refinementValidityForcing
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {n : Nat} (ui fi ci ti pi oi qi : Fin n) (env : Fin n → ZFSet.{u})
    (nameEnv : Assignment (M.nameDomain s) 4) (p : P)
    (hU : env ui = (nameEnv 0).val.val) (hRf : env fi = (nameEnv 1).val.val)
    (hRc : env ci = (nameEnv 2).val.val) (hT : env ti = (nameEnv 3).val.val)
    (hP : env pi = s.carrier) (hO : env oi = s.conditionOrder) (hQ : env qi = s.encode p) :
    Realize M.sets (refinementValidityForcingFormula ui fi ci ti pi oi qi) env ↔
      Forces (M.nameDomain s) BoundedFormula.refinementValidityFormula.toFormula nameEnv p := by
  exact M.realize_ordinaryGroundForcing s pairing unions powers separation collection carrier order
    (0 : Fin 2) 1 BoundedFormula.refinementValidityFormula.toFormula
    (extend pi (extend oi Fin.elim0)) qi
    (extend ui (extend fi (extend ci (extend ti Fin.elim0)))) env hP hO p nameEnv hQ
    (Fin.cases hU (Fin.cases hRf (Fin.cases hRc (Fin.cases hT (fun i => Fin.elim0 i)))))

theorem refinementValidity_eval (env : Assignment (M.nameDomain s) 4)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    {p : P} (hp : H.mem p)
    (forced : Forces (M.nameDomain s) BoundedFormula.refinementValidityFormula.toFormula env p) :
    RefinementValidityCode
      (Name.eval {q | H.mem q} (env 3).val) (Name.eval {q | H.mem q} (env 0).val)
      (Name.eval {q | H.mem q} (env 1).val) (Name.eval {q | H.mem q} (env 2).val) := by
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive {q | H.mem q}⟩
  have truth := forces_sound (M.nameDomain s) H generic _ env hp forced
  exact (evaluated.realize_refinementValidityFormula
    (evalAssignment {q | H.mem q} env) (fun j => ⟨env j, rfl⟩)).1 truth

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
