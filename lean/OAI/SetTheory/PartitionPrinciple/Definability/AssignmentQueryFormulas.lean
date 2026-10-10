import OAI.SetTheory.PartitionPrinciple.Geometry.RepresentativeIndexSteps

namespace OAI

namespace PartitionPilot.Forcing
universe u

noncomputable def assignmentQueryRelation (I T C D : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ row L A,
    z = ZFSet.pair (ZFSet.pair row L) (ZFSet.pair row A) ∧
    assignmentOnIndices (assignmentIndices I T L) T A = L) (ZFSet.prod C D)

theorem assignmentQueryRelation_entry (I T C D row L other A : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair row L) (ZFSet.pair other A) ∈ assignmentQueryRelation I T C D ↔
      ZFSet.pair row L ∈ C ∧ ZFSet.pair other A ∈ D ∧ row = other ∧
      assignmentOnIndices (assignmentIndices I T L) T A = L := by
  rw [assignmentQueryRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hq, hp⟩, r, L', A', eq, matchList⟩
    obtain ⟨first, second⟩ := ZFSet.pair_inj.1 eq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 first
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 second
    exact ⟨hq, hp, rfl, matchList⟩
  · rintro ⟨hq, hp, rfl, matchList⟩
    exact ⟨⟨hq, hp⟩, row, L, A, rfl, matchList⟩

noncomputable def realizedAssignmentQueries (I T C D : ZFSet.{u}) : ZFSet.{u} :=
  relationImage D C (relationConverse C D (assignmentQueryRelation I T C D))

theorem mem_realizedAssignmentQueries (I T C D q : ZFSet.{u}) :
    q ∈ realizedAssignmentQueries I T C D ↔
      q ∈ C ∧ ∃ p ∈ D, ZFSet.pair q p ∈ assignmentQueryRelation I T C D := by
  rw [realizedAssignmentQueries, mem_relationImage]
  constructor
  · rintro ⟨hq, p, hp, entry⟩
    exact ⟨hq, p, hp, ((pair_mem_relationConverse C D _ q p).1 entry).2.2⟩
  · rintro ⟨hq, p, hp, entry⟩
    exact ⟨hq, p, hp, (pair_mem_relationConverse C D _ q p).2 ⟨hq, hp, entry⟩⟩

theorem assignmentIndexOverlap_iff (I T L z : ZFSet.{u}) :
    (∃ i ∈ I, ∃ w ∈ L,
      ZFSet.pair z i ∈ productFirst I (ZFSet.prod T T) ∧
      ZFSet.pair w i ∈ productFirst I (ZFSet.prod T T)) ↔
    z ∈ stageOneAssignments (assignmentIndices I T L) T := by
  constructor
  · rintro ⟨i, hi, w, hw, first, second⟩
    obtain ⟨j, _, rest, hr, equal⟩ := (mem_productFirst I (ZFSet.prod T T) _).1 first
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ZFSet.pair_mem_prod.2
      ⟨(mem_relationImage L I _ _).2 ⟨hi, w, hw, second⟩, hr⟩
  · intro member
    obtain ⟨i, hi, rest, hr, rfl⟩ := ZFSet.mem_prod.1 member
    obtain ⟨hi, w, hw, second⟩ := (mem_relationImage L I _ i).1 hi
    exact ⟨i, hi, w, hw, (mem_productFirst I (ZFSet.prod T T) _).2
      ⟨i, hi, rest, hr, rfl⟩, second⟩

namespace BoundedFormula
open SetFormula

def assignmentQueryOverlapFormula {n} (z I L f : Fin n) : BoundedFormula n :=
  exMem I (exMem L.succ (.conj (pairMembershipFormula z.succ.succ 1 f.succ.succ)
    (pairMembershipFormula 0 1 f.succ.succ)))

theorem truth_assignmentQueryOverlapFormula {n} (z I L f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (assignmentQueryOverlapFormula z I L f) env ↔
      ∃ i ∈ env I, ∃ w ∈ env L,
        ZFSet.pair (env z) i ∈ env f ∧ ZFSet.pair w i ∈ env f := by
  simp only [assignmentQueryOverlapFormula, truth_exMem, Truth, truth_pairMembershipFormula]
  rfl

def assignmentQueryMatchFormula {n} (I L A f : Fin n) : BoundedFormula n :=
  .conj (.allMem L (.conj (.mem 0 A.succ)
    (assignmentQueryOverlapFormula 0 I.succ L.succ f.succ)))
    (.allMem A (.imp (assignmentQueryOverlapFormula 0 I.succ L.succ f.succ) (.mem 0 L.succ)))

theorem truth_assignmentQueryMatchFormula {n} (I L A f : Fin n)
    (env : Fin n → ZFSet.{u}) (T : ZFSet.{u})
    (projection : env f = productFirst (env I) (ZFSet.prod T T)) :
    Truth (assignmentQueryMatchFormula I L A f) env ↔
      assignmentOnIndices (assignmentIndices (env I) T (env L)) T (env A) = env L := by
  simp only [assignmentQueryMatchFormula, Truth, truth_imp, truth_assignmentQueryOverlapFormula]
  change ((∀ z ∈ env L, z ∈ env A ∧ ∃ i ∈ env I, ∃ w ∈ env L,
    ZFSet.pair z i ∈ env f ∧ ZFSet.pair w i ∈ env f) ∧
    (∀ z ∈ env A, (∃ i ∈ env I, ∃ w ∈ env L,
    ZFSet.pair z i ∈ env f ∧ ZFSet.pair w i ∈ env f) → z ∈ env L)) ↔ _
  simp only [projection, assignmentIndexOverlap_iff]
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    rw [mem_assignmentOnIndices]
    exact ⟨fun hz => h.2 z hz.1 hz.2, fun hz => h.1 z hz⟩
  · intro equal
    constructor
    · intro z hz
      exact (mem_assignmentOnIndices _ _ _ z).1 (equal.symm ▸ hz)
    · intro z hz hi
      exact equal ▸ (mem_assignmentOnIndices _ _ _ z).2 ⟨hz, hi⟩

def assignmentQueryRelationFormula {n} (z I f : Fin n) : BoundedFormula n :=
  exPairFields z (exPairFields 1 (exPairFields 2
    (.conj (.equal 3 1) (assignmentQueryMatchFormula I.succ.succ.succ.succ.succ.succ
      2 0 f.succ.succ.succ.succ.succ.succ))))

theorem truth_assignmentQueryRelationFormula {n} (z I f : Fin n)
    (env : Fin n → ZFSet.{u}) (T : ZFSet.{u})
    (projection : env f = productFirst (env I) (ZFSet.prod T T)) :
    Truth (assignmentQueryRelationFormula z I f) env ↔
      ∃ row L A, env z = ZFSet.pair (ZFSet.pair row L) (ZFSet.pair row A) ∧
        assignmentOnIndices (assignmentIndices (env I) T L) T A = L := by
  simp only [assignmentQueryRelationFormula, truth_exPairFields]
  constructor
  · rintro ⟨q, p, hz, row, L, hq, other, A, hp, same, matchList⟩
    change q = ZFSet.pair row L at hq
    change p = ZFSet.pair other A at hp
    change row = other at same
    have eq := (truth_assignmentQueryMatchFormula I.succ.succ.succ.succ.succ.succ 2 0
      f.succ.succ.succ.succ.succ.succ
      (extend A (extend other (extend L (extend row (extend p (extend q env)))))) T projection).1 matchList
    exact ⟨row, L, A, by rw [hz, hq, hp, ← same], eq⟩
  · rintro ⟨row, L, A, hz, matchList⟩
    exact ⟨ZFSet.pair row L, ZFSet.pair row A, hz, row, L, rfl, row, A, rfl,
      rfl, (truth_assignmentQueryMatchFormula I.succ.succ.succ.succ.succ.succ 2 0
        f.succ.succ.succ.succ.succ.succ
        (extend A (extend row (extend L (extend row
          (extend (ZFSet.pair row A) (extend (ZFSet.pair row L) env)))))) T projection).2 matchList⟩

end BoundedFormula

end PartitionPilot.Forcing

end OAI
