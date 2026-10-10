import OAI.SetTheory.PartitionPrinciple.Models.GroundCountableQuotients

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

def RefinementValidityCode (T U Rf Rc : ZFSet.{u}) : Prop :=
  U ⊆ T ∧ EquivalenceRelationCode U Rf ∧ EquivalenceRelationCode U Rc ∧ Rf ⊆ Rc

namespace BoundedFormula
open SetFormula

def equivalenceRelationFormula {n} (S R : Fin n) : BoundedFormula n :=
  .conj (relationBetweenFormula S S R)
    (.conj (.allMem S (pairMembershipFormula 0 0 R.succ))
      (.conj
        (.allMem S (.allMem S.succ
          (imp (pairMembershipFormula 1 0 R.succ.succ)
            (pairMembershipFormula 0 1 R.succ.succ))))
        (.allMem S (.allMem S.succ (.allMem S.succ.succ
          (imp (.conj (pairMembershipFormula 2 1 R.succ.succ.succ)
              (pairMembershipFormula 1 0 R.succ.succ.succ))
            (pairMembershipFormula 2 0 R.succ.succ.succ)))))))

theorem truth_equivalenceRelationFormula {n} (S R : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (equivalenceRelationFormula S R) env ↔ EquivalenceRelationCode (env S) (env R) := by
  simp only [equivalenceRelationFormula, Truth, truth_relationBetweenFormula,
    truth_pairMembershipFormula, truth_imp]
  constructor
  · rintro ⟨shape, refl, symm, trans⟩
    refine ⟨shape, refl, ?_, ?_⟩
    · intro x y xy
      obtain ⟨hx, hy⟩ := ZFSet.pair_mem_prod.1 (shape xy)
      exact symm x hx y hy xy
    · intro x y z xy yz
      obtain ⟨hx, hy⟩ := ZFSet.pair_mem_prod.1 (shape xy)
      have hz := (ZFSet.pair_mem_prod.1 (shape yz)).2
      exact trans x hx y hy z hz ⟨xy, yz⟩
  · intro relation
    exact ⟨relation.shape, relation.refl,
      fun x _ y _ xy => relation.symm x y xy,
      fun x _ y _ z _ h => relation.trans x y z h.1 h.2⟩

def refinementValidityFormula : BoundedFormula 4 :=
  .conj (subsetFormula 0 3)
    (.conj (equivalenceRelationFormula 0 1)
      (.conj (equivalenceRelationFormula 0 2) (subsetFormula 1 2)))

theorem truth_refinementValidityFormula (env : Fin 4 → ZFSet.{u}) :
    Truth refinementValidityFormula env ↔
      RefinementValidityCode (env 3) (env 0) (env 1) (env 2) := by
  simp only [refinementValidityFormula, Truth, truth_subsetFormula,
    truth_equivalenceRelationFormula, RefinementValidityCode]

end BoundedFormula

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_refinementValidityFormula (env : Fin 4 → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets BoundedFormula.refinementValidityFormula.toFormula env ↔
      RefinementValidityCode (env 3) (env 0) (env 1) (env 2) :=
  (BoundedFormula.realize_toFormula M _ _ members).trans
    (BoundedFormula.truth_refinementValidityFormula env)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
