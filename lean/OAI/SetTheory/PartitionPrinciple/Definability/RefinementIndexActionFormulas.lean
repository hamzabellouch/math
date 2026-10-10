import OAI.SetTheory.PartitionPrinciple.Forcing.GroundProductActions

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula

def refinementIndexActionRawFormula {n}
    (x y g P maps nodeMaps : Fin n) (w : Fin 13 → Fin n) : SetFormula n :=
  .conj (BoundedFormula.nonemptyTupleFormula 5 x (fun j => w (j.castAdd 7))).toFormula
  (.conj (BoundedFormula.nonemptyTupleFormula 5 y (fun j => w ((Fin.natAdd 6 j).castAdd 1))).toFormula
  (.conj (.equal (w 0) (w 6))
  (.conj (pairMembershipFormula g (w 12) nodeMaps)
  (.conj (pairMembershipFormula (w 1) (w 7) (w 12))
  (.conj (pairMembershipFormula (w 2) (w 8) (w 12))
  (.conj (atomicApplication nameActionFormula (extend P (extend maps Fin.elim0)) g (w 3) (w 9))
  (.conj (atomicApplication nameActionFormula (extend P (extend maps Fin.elim0)) g (w 4) (w 10))
    (atomicApplication nameActionFormula (extend P (extend maps Fin.elim0)) g (w 5) (w 11)))))))))

def refinementIndexActionFormula {n} (x y g P maps nodeMaps : Fin n) : SetFormula n :=
  let old := suffixIndex n 13
  exBlock 13 (refinementIndexActionRawFormula (old x) (old y) (old g) (old P)
    (old maps) (old nodeMaps) (prefixIndex n 13))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_refinementIndexActionRawFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (x y g P maps nodeMaps : Fin n) (w : Fin 13 → Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (refinementIndexActionRawFormula x y g P maps nodeMaps w) env ↔
      env x = nonemptyTupleCode 5 (fun j => env (w (j.castAdd 7))) ∧
      env y = nonemptyTupleCode 5 (fun j => env (w ((Fin.natAdd 6 j).castAdd 1))) ∧
      env (w 0) = env (w 6) ∧ ZFSet.pair (env g) (env (w 12)) ∈ env nodeMaps ∧
      ZFSet.pair (env (w 1)) (env (w 7)) ∈ env (w 12) ∧
      ZFSet.pair (env (w 2)) (env (w 8)) ∈ env (w 12) ∧
      Realize M.sets nameActionFormula (extend (env g) (extend (env (w 3))
        (extend (env (w 9)) (extend (env P) (extend (env maps) Fin.elim0))))) ∧
      Realize M.sets nameActionFormula (extend (env g) (extend (env (w 4))
        (extend (env (w 10)) (extend (env P) (extend (env maps) Fin.elim0))))) ∧
      Realize M.sets nameActionFormula (extend (env g) (extend (env (w 5))
        (extend (env (w 11)) (extend (env P) (extend (env maps) Fin.elim0))))) := by
  simp only [refinementIndexActionRawFormula, Realize,
    BoundedFormula.realize_toFormula M _ env members, BoundedFormula.truth_nonemptyTupleFormula,
    M.realize_pairMembershipFormula pairing _ _ _ env (members _) (members _) (members _),
    realize_atomicApplication, map_extend, map_empty]

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
