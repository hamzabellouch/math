import OAI.SetTheory.PartitionPrinciple.Geometry.RowAssignmentTransitionFamilies

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace BoundedFormula
private def cutGraphProductMember {n : Nat} (z upper lower : Fin n) : BoundedFormula n :=
  exMem upper (exMem lower.succ (orderedPairFormula z.succ.succ 1 0))

private theorem truth_cutGraphProductMember {n : Nat} (z upper lower : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (cutGraphProductMember z upper lower) env ↔ env z ∈ ZFSet.prod (env upper) (env lower) := by
  simp only [cutGraphProductMember, truth_exMem, truth_orderedPairFormula]
  constructor
  · rintro ⟨x, hx, y, hy, equal⟩
    change env z = ZFSet.pair x y at equal
    rw [equal]
    exact ZFSet.pair_mem_prod.2 ⟨hx, hy⟩
  · intro hz
    obtain ⟨x, hx, y, hy, equal⟩ := ZFSet.mem_prod.1 hz
    exact ⟨x, hx, y, hy, equal⟩
end BoundedFormula

namespace SetFormula
def rowAssignmentCutGraphFormula {n : Nat} (output upper lower levels alpha : Fin n) : SetFormula n :=
  exactSetFormula output
    (.conj (BoundedFormula.cutGraphProductMember 0 upper.succ lower.succ).toFormula
      (rowAssignmentCutFormula 0 levels.succ alpha.succ))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_rowAssignmentCutGraphFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {n : Nat} (output upper lower levels alpha : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (rowAssignmentCutGraphFormula output upper lower levels alpha) env ↔
      env output = rowAssignmentCutGraph (env upper) (env lower) (env levels) (env alpha) := by
  have ground := M.rowAssignmentCutGraph_mem pairing unions powers separation
    (members upper) (members lower) (members levels) (members alpha)
  apply M.realize_exactSetFormula output _ env (members output) (fun _ hz => M.transitive ground hz)
  intro z hz
  have allGround : ∀ j, (extend z env) j ∈ M.sets := Fin.cases hz members
  change (Realize M.sets (BoundedFormula.cutGraphProductMember 0 upper.succ lower.succ).toFormula
      (extend z env) ∧ Realize M.sets (rowAssignmentCutFormula 0 levels.succ alpha.succ)
      (extend z env)) ↔ _
  rw [BoundedFormula.realize_toFormula M _ _ allGround,
    BoundedFormula.truth_cutGraphProductMember,
    M.realize_rowAssignmentCutFormula 0 levels.succ alpha.succ _ allGround]
  exact (mem_rowAssignmentCutGraph _ _ _ _ z).symm

end TransitiveGround

namespace SetFormula
private def rowTransitionBody {n : Nat} (z stages history W : Fin n) : BoundedFormula (n + 5) :=
  let old := suffixIndex n 5
  let v := prefixIndex n 5
  .conj (.mem (v 0) (old stages))
    (.conj (.mem (v 1) (old stages))
      (.conj (.mem (v 4) (old W))
        (.conj (BoundedFormula.orderedTripleFormula (old z) (v 0) (v 1) (v 4))
          (.conj (BoundedFormula.pairMembershipFormula (v 0) (v 2) (old history))
            (BoundedFormula.pairMembershipFormula (v 1) (v 3) (old history))))))

def rowAssignmentTransitionFormula {n : Nat} (z stages history levels W : Fin n) : SetFormula n :=
  let old := suffixIndex n 5
  let v := prefixIndex n 5
  exBlock 5 (.conj (rowTransitionBody z stages history W).toFormula
    (rowAssignmentCutGraphFormula (v 4) (v 2) (v 3) (old levels) (v 1)))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_rowAssignmentTransitionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {n : Nat} (z stages history levels W : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (rowAssignmentTransitionFormula z stages history levels W) env ↔
      ∃ i ∈ env stages, ∃ j ∈ env stages, ∃ Qi Qj R,
        R ∈ env W ∧ env z = ZFSet.pair (ZFSet.pair i j) R ∧
        ZFSet.pair i Qi ∈ env history ∧ ZFSet.pair j Qj ∈ env history ∧
        R = rowAssignmentCutGraph Qi Qj (env levels) j := by
  rw [rowAssignmentTransitionFormula, realize_exBlock]
  have actual (f : Fin 5 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (.conj (SetFormula.rowTransitionBody z stages history W).toFormula
        (rowAssignmentCutGraphFormula (prefixIndex n 5 4) (prefixIndex n 5 2)
          (prefixIndex n 5 3) (suffixIndex n 5 levels) (prefixIndex n 5 1)))
        (extendMany 5 f env) ↔
      (f 0 ∈ env stages ∧ f 1 ∈ env stages ∧ f 4 ∈ env W ∧
        env z = ZFSet.pair (ZFSet.pair (f 0) (f 1)) (f 4) ∧
        ZFSet.pair (f 0) (f 2) ∈ env history ∧ ZFSet.pair (f 1) (f 3) ∈ env history) ∧
        f 4 = rowAssignmentCutGraph (f 2) (f 3) (env levels) (f 1) := by
    change (Realize M.sets (SetFormula.rowTransitionBody z stages history W).toFormula _ ∧
      Realize M.sets (rowAssignmentCutGraphFormula _ _ _ _ _) _) ↔ _
    rw [BoundedFormula.realize_toFormula M _ _ (extendMany_members 5 f env ground members),
      M.realize_rowAssignmentCutGraphFormula pairing unions powers separation _ _ _ _ _ _
        (extendMany_members 5 f env ground members)]
    simp only [SetFormula.rowTransitionBody, BoundedFormula.Truth,
      BoundedFormula.truth_orderedTripleFormula, BoundedFormula.truth_pairMembershipFormula,
      extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, body⟩
    obtain ⟨⟨hi, hj, hR, equal, first, second⟩, output⟩ := (actual f ground).1 body
    exact ⟨f 0, hi, f 1, hj, f 2, f 3, f 4, hR, equal, first, second, output⟩
  · rintro ⟨i, hi, j, hj, Qi, Qj, R, hR, equal, first, second, output⟩
    let f : Fin 5 → ZFSet.{u} := ![i, j, Qi, Qj, R]
    have ground : ∀ k, f k ∈ M.sets :=
      Fin.cases (M.transitive (members stages) hi)
        (Fin.cases (M.transitive (members stages) hj)
          (Fin.cases (M.pair_right (M.transitive (members history) first))
            (Fin.cases (M.pair_right (M.transitive (members history) second))
              (Fin.cases (M.transitive (members W) hR) (fun k => Fin.elim0 k)))))
    exact ⟨f, ground, (actual f ground).2 ⟨⟨hi, hj, hR, equal, first, second⟩, output⟩⟩

end TransitiveGround
end PartitionPilot.Forcing

end OAI
