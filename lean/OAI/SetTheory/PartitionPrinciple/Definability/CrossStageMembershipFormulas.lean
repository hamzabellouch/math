import OAI.SetTheory.PartitionPrinciple.Forcing.NamePresentationEquivalences
import OAI.SetTheory.PartitionPrinciple.Forcing.NameRenameSteps

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace SetFormula

def crossStageMembershipEntryFormula {n : Nat}
    (entry terms lowerCarrier upperCarrier upperOrder tau : Fin n) : SetFormula n :=
  exConditions terms (exConditions lowerCarrier.succ
    (.conj (orderedPairFormula entry.succ.succ 1 0)
      (forcingTranslation (ordinaryGroundPrimitives (0 : Fin 2) 1) (.mem 0 1)
        (extend upperCarrier.succ.succ (extend upperOrder.succ.succ Fin.elim0)) 0
        (extend 1 (extend tau.succ.succ Fin.elim0)))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {Upper Lower : Type u} [PartialOrder Upper]
variable (s : Presentation Upper) (t : Presentation Lower) (inclusion : Lower → Upper)

theorem realize_crossStageMembershipEntryFormula
    (unchanged : ∀ p, s.encode (inclusion p) = t.encode p)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (upperGround : s.carrier ∈ M.sets) (upperOrderGround : s.conditionOrder ∈ M.sets)
    (lowerGround : t.carrier ∈ M.sets)
    {J : ZFSet.{u}} (hJ : J ∈ M.sets) (valid : ∀ u ∈ J, IsName t u)
    (tau : Name s) (hTau : tau.val ∈ M.sets)
    {n : Nat} (zi ji li ui oi ti : Fin n) (env : Fin n → ZFSet.{u})
    (hz : env zi ∈ M.sets) (hj : env ji = J) (hl : env li = t.carrier)
    (hu : env ui = s.carrier) (ho : env oi = s.conditionOrder) (ht : env ti = tau.val) :
    Realize M.sets (crossStageMembershipEntryFormula zi ji li ui oi ti) env ↔
      ∃ sigma : Name t, sigma.val ∈ J ∧ ∃ p : Lower,
        env zi = ZFSet.pair sigma.val (t.encode p) ∧
          Name.ForcesMem (inclusion p) (Name.rename s inclusion sigma) tau := by
  rw [crossStageMembershipEntryFormula, exConditions, realize_ex]
  constructor
  · rintro ⟨u, uGround, member, body⟩
    change u ∈ env ji at member
    rw [hj] at member
    let sigma : Name t := ⟨u, valid u member⟩
    obtain ⟨p, shape, forced⟩ :=
      (M.realize_exConditions t li.succ _ (extend u env) lowerGround hl).1 body
    have hp := M.transitive lowerGround (t.encode_mem p)
    have code := Name.rename_val_of_encode s inclusion unchanged sigma
    have liftGround : (Name.rename s inclusion sigma).val ∈ M.sets := code.symm ▸ uGround
    let names : Assignment (M.nameDomain s) 2 :=
      extend ⟨Name.rename s inclusion sigma, liftGround⟩ (extend ⟨tau, hTau⟩ Fin.elim0)
    have pair := (M.realize_orderedPairFormula pairing zi.succ.succ 1 0
      (extend (t.encode p) (extend u env)) hz uGround hp).1 shape
    have atom := (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
      upperGround upperOrderGround (0 : Fin 2) 1 (.mem 0 1)
      (extend ui.succ.succ (extend oi.succ.succ Fin.elim0)) 0
      (extend 1 (extend ti.succ.succ Fin.elim0)) _ hu ho (inclusion p) names (unchanged p).symm
      (Fin.cases code.symm (Fin.cases ht (fun i => Fin.elim0 i)))).1 forced
    exact ⟨sigma, member, p, pair, atom⟩
  · rintro ⟨sigma, member, p, pair, forced⟩
    have hs := M.transitive hJ member
    have hp := M.transitive lowerGround (t.encode_mem p)
    have code := Name.rename_val_of_encode s inclusion unchanged sigma
    have liftGround : (Name.rename s inclusion sigma).val ∈ M.sets := code.symm ▸ hs
    let names : Assignment (M.nameDomain s) 2 :=
      extend ⟨Name.rename s inclusion sigma, liftGround⟩ (extend ⟨tau, hTau⟩ Fin.elim0)
    refine ⟨sigma.val, hs, ?_, ?_⟩
    · change sigma.val ∈ env ji
      exact hj.symm ▸ member
    · apply (M.realize_exConditions t li.succ _ (extend sigma.val env) lowerGround hl).2
      refine ⟨p, ?_, ?_⟩
      · exact (M.realize_orderedPairFormula pairing zi.succ.succ 1 0
          (extend (t.encode p) (extend sigma.val env)) hz hs hp).2 pair
      · exact (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
          upperGround upperOrderGround (0 : Fin 2) 1 (.mem 0 1)
          (extend ui.succ.succ (extend oi.succ.succ Fin.elim0)) 0
          (extend 1 (extend ti.succ.succ Fin.elim0)) _ hu ho (inclusion p) names (unchanged p).symm
          (Fin.cases code.symm (Fin.cases ht (fun i => Fin.elim0 i)))).2 forced

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
