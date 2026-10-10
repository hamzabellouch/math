import OAI.SetTheory.PartitionPrinciple.Definability.BatchAttachmentRealization

namespace OAI


namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem codedAttachmentOrder_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P N r inside shadow upper : ZFSet.{u}}
    (hP : P ∈ M.sets) (hN : N ∈ M.sets) (hr : r ∈ M.sets)
    (hi : inside ∈ M.sets) (hs : shadow ∈ M.sets) (hu : upper ∈ M.sets) :
    codedAttachmentOrder P N r inside shadow upper ∈ M.sets := by
  let L := taggedExtension P N
  have hL := M.taggedExtension_mem pairing unions powers separation hP hN
  let params := extend L (extend P (extend N (extend r (extend inside
    (extend shadow (extend upper Fin.elim0))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.codedAttachmentOrderEntryFormula 0 1 2 3 4 5 6 7) params
    (Fin.cases hL (Fin.cases hP (Fin.cases hN (Fin.cases hr (Fin.cases hi
      (Fin.cases hs (Fin.cases hu (fun i => Fin.elim0 i))))))))
    (M.prod_mem pairing unions powers separation hL hL)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.codedAttachmentOrderEntryFormula 0 1 2 3 4 5 6 7)
      (extend z params)) (ZFSet.prod L L) = codedAttachmentOrder P N r inside shadow upper := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, codedAttachmentOrder, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_codedAttachmentOrderEntryFormula 0 1 2 3 4 5 6 7 _)
  exact eq ▸ selected

end TransitiveGround



open SetFormula
universe u

namespace SetFormula

def sUnionSetFormula {n} (output source : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.exMem source.succ (.mem 1 0)).toFormula

def taggedExtensionSetFormula {n} (output p fresh : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.disj (.mem 0 p.succ)
    (BoundedFormula.attachmentTagFormula 0 p.succ fresh.succ)).toFormula

def canonicalMeetSetFormula {n} (output carrier order : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.canonicalMeetEntryFormula 0 carrier.succ order.succ).toFormula

def codedAttachmentOrderSetFormula {n} (output carrier p fresh order inside shadow upper : Fin n) :
    SetFormula n :=
  exactSetFormula output (BoundedFormula.codedAttachmentOrderEntryFormula 0 carrier.succ
    p.succ fresh.succ order.succ inside.succ shadow.succ upper.succ).toFormula

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_exactBoundedSetFormula {n} (output : Fin n) (entry : BoundedFormula (n + 1))
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    {target : ZFSet.{u}} (ground : target ∈ M.sets)
    (meaning : ∀ z, BoundedFormula.Truth entry (extend z env) ↔ z ∈ target) :
    Realize M.sets (exactSetFormula output entry.toFormula) env ↔ env output = target :=
  M.realize_exactSetFormula output entry.toFormula env (members output)
    (fun _ hz => M.transitive ground hz) (fun z hz =>
      (BoundedFormula.realize_toFormula M entry (extend z env) (Fin.cases hz members)).trans (meaning z))

theorem realize_sUnionSetFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {n} (output source : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (sUnionSetFormula output source) env ↔ env output = ZFSet.sUnion (env source) := by
  apply M.realize_exactBoundedSetFormula output _ env members (M.union_mem unions (members source))
  intro z
  simp only [BoundedFormula.truth_exMem, BoundedFormula.Truth, ZFSet.mem_sUnion]
  rfl

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_taggedExtensionSetFormula {n} (output p fresh : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (taggedExtensionSetFormula output p fresh) env ↔
      env output = taggedExtension (env p) (env fresh) := by
  apply M.realize_exactBoundedSetFormula output _ env members
    (M.taggedExtension_mem pairing unions powers separation (members p) (members fresh))
  intro z
  simp only [BoundedFormula.truth_disj, BoundedFormula.Truth,
    BoundedFormula.attachmentTagFormula, BoundedFormula.truth_exMem,
    BoundedFormula.truth_orderedPairFormula, mem_taggedExtension]
  rfl

theorem realize_canonicalMeetSetFormula {n} (output carrier order : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (canonicalMeetSetFormula output carrier order) env ↔
      env output = canonicalMeetGraph (env carrier) (env order) := by
  apply M.realize_exactBoundedSetFormula output _ env members
    (M.canonicalMeetGraph_mem pairing unions powers separation (members carrier) (members order))
  intro z
  exact BoundedFormula.truth_canonicalMeetEntryFormula 0 carrier.succ order.succ (extend z env)

theorem realize_codedAttachmentOrderSetFormula {n}
    (output carrier p fresh order inside shadow upper : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (carrier_eq : env carrier = taggedExtension (env p) (env fresh)) :
    Realize M.sets (codedAttachmentOrderSetFormula output carrier p fresh order inside shadow upper) env ↔
      env output = codedAttachmentOrder (env p) (env fresh) (env order)
        (env inside) (env shadow) (env upper) := by
  apply M.realize_exactBoundedSetFormula output _ env members
    (M.codedAttachmentOrder_mem pairing unions powers separation (members p) (members fresh)
      (members order) (members inside) (members shadow) (members upper))
  intro z
  rw [BoundedFormula.truth_codedAttachmentOrderEntryFormula]
  change (∃ x ∈ env carrier, ∃ y ∈ env carrier, z = ZFSet.pair x y ∧ _) ↔ _
  rw [carrier_eq, codedAttachmentOrder, ZFSet.mem_sep]
  constructor
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨x, hx, y, hy, equal, _⟩ := witness
    rw [equal]
    exact ZFSet.pair_mem_prod.2 ⟨hx, hy⟩
  · exact And.right

end TransitiveGround




namespace SetFormula
def batchInsideSetFormula {n} (output i qs rs qb rb : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.batchAttachmentInsideEntryFormula
    0 i.succ qs.succ rs.succ qb.succ rb.succ).toFormula

def batchUpperSetFormula {n} (output i p qs fs qb fb : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.batchAttachmentUpperEntryFormula
    0 i.succ p.succ qs.succ fs.succ qb.succ fb.succ).toFormula

def batchShadowSetFormula {n} (output i p qs ms anchors es qb mb ab eb : Fin n) : SetFormula n :=
  exactSetFormula output (reindex
    (Fin.cases 0 (Fin.cases i.succ (Fin.cases p.succ (Fin.cases qs.succ
      (Fin.cases ms.succ (Fin.cases anchors.succ (Fin.cases es.succ (Fin.cases qb.succ
        (Fin.cases mb.succ (Fin.cases ab.succ (Fin.cases eb.succ Fin.elim0)))))))))))
    BoundedFormula.batchShadowGraphFormula.toFormula)

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_exactReindexedBoundedSetFormula {n k} (output : Fin n) (entry : BoundedFormula k)
    (slots : Fin k → Fin (n + 1)) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    {target : ZFSet.{u}} (ground : target ∈ M.sets)
    (meaning : ∀ z, BoundedFormula.Truth entry (fun i => extend z env (slots i)) ↔ z ∈ target) :
    Realize M.sets (exactSetFormula output (reindex slots entry.toFormula)) env ↔ env output = target := by
  apply M.realize_exactSetFormula output _ env (members output) (fun _ hz => M.transitive ground hz)
  intro z hz
  rw [realize_reindex]
  have extended : ∀ i : Fin (n + 1), extend z env i ∈ M.sets := Fin.cases hz members
  exact (BoundedFormula.realize_toFormula M entry _
    (fun i => extended (slots i))).trans (meaning z)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_batchInsideSetFormula {n} (output i qs rs qb rb : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ x, env x ∈ M.sets)
    (qBound : env qb = ZFSet.sUnion (ZFSet.sUnion (env qs)))
    (rBound : env rb = ZFSet.sUnion (ZFSet.sUnion (env rs))) :
    Realize M.sets (batchInsideSetFormula output i qs rs qb rb) env ↔
      env output = batchAttachmentInsideGraph (env i) (env qs) (env rs) := by
  apply M.realize_exactBoundedSetFormula output _ env members
    (M.batchAttachmentInsideGraph_mem pairing unions powers separation (members i) (members qs) (members rs))
  intro z
  rw [BoundedFormula.truth_batchAttachmentInsideEntryFormula]
  change (∃ j ∈ env i, ∃ Q ∈ env qb, ∃ r ∈ env rb, ∃ q ∈ Q, ∃ t ∈ Q,
    z = ZFSet.pair (ZFSet.pair j q) (ZFSet.pair j t) ∧ ZFSet.pair j Q ∈ env qs ∧
      ZFSet.pair j r ∈ env rs ∧ ZFSet.pair q t ∈ r) ↔ _
  rw [qBound, rBound, batchAttachmentInsideGraph, ZFSet.mem_sep]
  constructor
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨j, hj, Q, _, _, _, q, hq, t, ht, equal, entry, _⟩ := witness
    rw [equal]
    exact ZFSet.pair_mem_prod.2
      ⟨(pair_mem_indexedAttachmentDomain (env i) (env qs) j q).2 ⟨hj, Q, entry, hq⟩,
        (pair_mem_indexedAttachmentDomain (env i) (env qs) j t).2 ⟨hj, Q, entry, ht⟩⟩
  · exact And.right

theorem realize_batchUpperSetFormula {n} (output i p qs fs qb fb : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ x, env x ∈ M.sets)
    (qBound : env qb = ZFSet.sUnion (ZFSet.sUnion (env qs)))
    (fBound : env fb = ZFSet.sUnion (ZFSet.sUnion (env fs))) :
    Realize M.sets (batchUpperSetFormula output i p qs fs qb fb) env ↔
      env output = batchAttachmentUpperGraph (env i) (env p) (env qs) (env fs) := by
  apply M.realize_exactBoundedSetFormula output _ env members
    (M.batchAttachmentUpperGraph_mem pairing unions powers separation
      (members i) (members p) (members qs) (members fs))
  intro z
  rw [BoundedFormula.truth_batchAttachmentUpperEntryFormula]
  change (∃ j ∈ env i, ∃ Q ∈ env qb, ∃ F ∈ env fb, ∃ q ∈ Q, ∃ v ∈ env p,
    z = ZFSet.pair (ZFSet.pair j q) v ∧ ZFSet.pair j Q ∈ env qs ∧
      ZFSet.pair j F ∈ env fs ∧ v ∈ F) ↔ _
  rw [qBound, fBound, batchAttachmentUpperGraph, ZFSet.mem_sep]
  constructor
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨j, hj, Q, _, _, _, q, hq, v, hv, equal, entry, _⟩ := witness
    rw [equal]
    exact ZFSet.pair_mem_prod.2
      ⟨(pair_mem_indexedAttachmentDomain (env i) (env qs) j q).2 ⟨hj, Q, entry, hq⟩, hv⟩
  · exact And.right

theorem realize_batchShadowSetFormula {n} (output i p qs ms anchors es qb mb ab eb : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ x, env x ∈ M.sets)
    (qBound : env qb = ZFSet.sUnion (ZFSet.sUnion (env qs)))
    (mBound : env mb = ZFSet.sUnion (ZFSet.sUnion (env ms)))
    (aBound : env ab = ZFSet.sUnion (ZFSet.sUnion (env anchors)))
    (eBound : env eb = ZFSet.sUnion (ZFSet.sUnion (env es))) :
    Realize M.sets (batchShadowSetFormula output i p qs ms anchors es qb mb ab eb) env ↔
      env output = batchAttachmentShadowGraph (env i) (env p) (env qs) (env ms) (env anchors) (env es) := by
  apply M.realize_exactReindexedBoundedSetFormula output _ _ env members
    (M.batchAttachmentShadowGraph_mem pairing unions powers separation
      (members i) (members p) (members qs) (members ms) (members anchors) (members es))
  intro z
  rw [BoundedFormula.truth_batchShadowGraphFormula]
  change (∃ j ∈ env i, ∃ Q ∈ env qb, ∃ μ ∈ env mb, ∃ a ∈ env ab, ∃ ell ∈ env eb,
    ∃ q ∈ Q, ∃ v ∈ env p, z = ZFSet.pair (ZFSet.pair j q) v ∧
      ZFSet.pair j Q ∈ env qs ∧ ZFSet.pair j μ ∈ env ms ∧
      ZFSet.pair j a ∈ env anchors ∧ ZFSet.pair j ell ∈ env es ∧
      ∃ c ∈ Q, ZFSet.pair (ZFSet.pair q a) c ∈ μ ∧ ZFSet.pair c v ∈ ell) ↔ _
  rw [qBound, mBound, aBound, eBound, batchAttachmentShadowGraph, ZFSet.mem_sep]
  constructor
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨j, hj, Q, _, _, _, _, _, _, _, q, hq, v, hv, equal, entry, _⟩ := witness
    rw [equal]
    exact ZFSet.pair_mem_prod.2
      ⟨(pair_mem_indexedAttachmentDomain (env i) (env qs) j q).2 ⟨hj, Q, entry, hq⟩, hv⟩
  · exact And.right

end TransitiveGround

end PartitionPilot.Forcing

end OAI
