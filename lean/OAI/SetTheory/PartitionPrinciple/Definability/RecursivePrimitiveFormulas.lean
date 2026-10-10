import OAI.SetTheory.PartitionPrinciple.Transfinite.RecursiveLiftAgreement

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula
def recursiveIndicesSetFormula {n} (output i j p bound sources filters : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.recursiveAttachmentIndexFormula 0 i.succ j.succ
    p.succ bound.succ sources.succ filters.succ).toFormula

def pairFieldSetFormula {n} (left : Bool) (output i j k bound family : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.pairFieldEntryFormula left 0 k.succ i.succ j.succ
    bound.succ family.succ).toFormula

def indexedFreshSetFormula {n} (output i qs rs anchors qb rb ab : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.indexedAttachmentFreshEntryFormula 0 i.succ qs.succ
    rs.succ anchors.succ qb.succ rb.succ ab.succ).toFormula

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_recursiveIndicesSetFormula {n} (output i j p bound sources filters : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ x, env x ∈ M.sets) :
    Realize M.sets (recursiveIndicesSetFormula output i j p bound sources filters) env ↔
      env output = recursiveAttachmentIndices (env i) (env j) (env p) (env bound)
        (env sources) (env filters) := by
  apply M.realize_exactBoundedSetFormula output _ env members
    (M.recursiveAttachmentIndices_mem pairing unions powers separation (members i) (members j)
      (members p) (members bound) (members sources) (members filters))
  intro z
  rw [BoundedFormula.truth_recursiveAttachmentIndexFormula]
  change (∃ x ∈ env i, ∃ y ∈ env j, ∃ a ∈ env p, ∃ F ∈ env bound,
    z = ZFSet.pair x y ∧ ZFSet.pair x a ∈ env sources ∧
      ZFSet.pair y F ∈ env filters ∧ a ∉ F) ↔ _
  rw [recursiveAttachmentIndices, ZFSet.mem_sep]
  constructor
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨x, hx, y, hy, _, _, _, _, equal, _⟩ := witness
    rw [equal]
    exact ZFSet.pair_mem_prod.2 ⟨hx, hy⟩
  · exact And.right

theorem realize_pairFieldSetFormula {n} (left : Bool) (output i j k bound family : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ x, env x ∈ M.sets) :
    Realize M.sets (pairFieldSetFormula left output i j k bound family) env ↔
      env output = pairFieldGraph left (env i) (env j) (env k) (env bound) (env family) := by
  apply M.realize_exactBoundedSetFormula output _ env members
    (M.pairFieldGraph_mem pairing unions powers separation left (members i) (members j)
      (members k) (members bound) (members family))
  intro z
  rw [BoundedFormula.truth_pairFieldEntryFormula]
  change (∃ t ∈ env k, ∃ x ∈ env i, ∃ y ∈ env j, ∃ v ∈ env bound,
    z = ZFSet.pair t v ∧ t = ZFSet.pair x y ∧
      ZFSet.pair (if left then x else y) v ∈ env family) ↔ _
  rw [pairFieldGraph, ZFSet.mem_sep]
  constructor
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨t, ht, _, _, _, _, v, hv, equal, _⟩ := witness
    rw [equal]
    exact ZFSet.pair_mem_prod.2 ⟨ht, hv⟩
  · exact And.right

theorem realize_pairSecondFieldSetFormula {n} (output i j k bound family : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ x, env x ∈ M.sets)
    (bound_eq : env bound = ZFSet.sUnion (ZFSet.sUnion (env family))) :
    Realize M.sets (pairFieldSetFormula false output i j k bound family) env ↔
      env output = pairSecondField (env i) (env j) (env k) (env family) := by
  rw [M.realize_pairFieldSetFormula pairing unions powers separation false output i j k bound family
    env members, bound_eq]
  rfl

theorem realize_indexedFreshSetFormula {n} (output i qs rs anchors qb rb ab : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ x, env x ∈ M.sets)
    (qBound : env qb = ZFSet.sUnion (ZFSet.sUnion (env qs)))
    (rBound : env rb = ZFSet.sUnion (ZFSet.sUnion (env rs)))
    (aBound : env ab = ZFSet.sUnion (ZFSet.sUnion (env anchors))) :
    Realize M.sets (indexedFreshSetFormula output i qs rs anchors qb rb ab) env ↔
      env output = indexedAttachmentFresh (env i) (env qs) (env rs) (env anchors) := by
  apply M.realize_exactBoundedSetFormula output _ env members
    (M.indexedAttachmentFresh_mem pairing unions powers separation (members i) (members qs)
      (members rs) (members anchors))
  intro z
  rw [BoundedFormula.truth_indexedAttachmentFreshEntryFormula]
  change (∃ j ∈ env i, ∃ Q ∈ env qb, ∃ r ∈ env rb, ∃ a ∈ env ab, ∃ q ∈ Q,
    ZFSet.pair j Q ∈ env qs ∧ ZFSet.pair j r ∈ env rs ∧ ZFSet.pair j a ∈ env anchors ∧
      z = ZFSet.pair j q ∧ ZFSet.pair q a ∉ r) ↔ _
  rw [qBound, rBound, aBound, indexedAttachmentFresh, ZFSet.mem_sep]
  constructor
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨j, hj, Q, _, _, _, _, _, q, hq, entry, _, _, equal, _⟩ := witness
    rw [equal]
    exact (pair_mem_indexedAttachmentDomain (env i) (env qs) j q).2 ⟨hj, Q, entry, hq⟩
  · exact And.right

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
