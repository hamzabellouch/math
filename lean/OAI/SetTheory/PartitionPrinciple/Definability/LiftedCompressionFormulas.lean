import OAI.SetTheory.PartitionPrinciple.Geometry.LiftedCompressionFunctions

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def rightTripleFormula {n} (z a b c : Fin n) : BoundedFormula n :=
  exMem z (exMem 0 (.conj (orderedPairFormula 0 b.succ.succ c.succ.succ)
    (orderedPairFormula z.succ.succ a.succ.succ 0)))

theorem truth_rightTripleFormula {n} (z a b c : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (rightTripleFormula z a b c) env ↔
      env z = ZFSet.pair (env a) (ZFSet.pair (env b) (env c)) := by
  simp only [rightTripleFormula, truth_exMem, Truth, truth_orderedPairFormula]
  change (∃ s ∈ env z, ∃ t ∈ s, t = ZFSet.pair (env b) (env c) ∧
    env z = ZFSet.pair (env a) t) ↔ _
  constructor
  · rintro ⟨_, _, _, _, rfl, equal⟩
    exact equal
  · intro equal
    refine ⟨{env a, ZFSet.pair (env b) (env c)}, ?_, ZFSet.pair (env b) (env c),
      ZFSet.mem_pair.2 (Or.inr rfl), rfl, equal⟩
    rw [equal]
    exact ZFSet.mem_pair.2 (Or.inr rfl)

def taggedPairTripleFormula {n} (z l i j q : Fin n) : BoundedFormula n :=
  exMem z (exMem 0 (.conj (orderedTripleFormula 0 i.succ.succ j.succ.succ q.succ.succ)
    (orderedPairFormula z.succ.succ l.succ.succ 0)))

theorem truth_taggedPairTripleFormula {n} (z l i j q : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (taggedPairTripleFormula z l i j q) env ↔
      env z = ZFSet.pair (env l) (ZFSet.pair (ZFSet.pair (env i) (env j)) (env q)) := by
  simp only [taggedPairTripleFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_orderedPairFormula]
  change (∃ s ∈ env z, ∃ t ∈ s, t = ZFSet.pair (ZFSet.pair (env i) (env j)) (env q) ∧
    env z = ZFSet.pair (env l) t) ↔ _
  constructor
  · rintro ⟨_, _, _, _, rfl, equal⟩
    exact equal
  · intro equal
    refine ⟨{env l, ZFSet.pair (ZFSet.pair (env i) (env j)) (env q)}, ?_,
      ZFSet.pair (ZFSet.pair (env i) (env j)) (env q),
      ZFSet.mem_pair.2 (Or.inr rfl), rfl, equal⟩
    rw [equal]
    exact ZFSet.mem_pair.2 (Or.inr rfl)

def liftOldEntryFormula {n} (d maps bound i x y : Fin n) : BoundedFormula n :=
  .conj (.mem x d) (exMem bound (.conj (pairMembershipFormula i.succ 0 maps.succ)
    (pairMembershipFormula x.succ y.succ 0)))

theorem truth_liftOldEntryFormula {n} (d maps bound i x y : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (liftOldEntryFormula d maps bound i x y) env ↔
      env x ∈ env d ∧ ∃ S ∈ env bound,
        ZFSet.pair (env i) S ∈ env maps ∧ ZFSet.pair (env x) (env y) ∈ S := by
  simp only [liftOldEntryFormula, Truth, truth_exMem, truth_pairMembershipFormula]
  rfl

def liftFreshEntryFormula {n} (d l j b ns sources fs bound reps g action i x y : Fin n) : BoundedFormula n :=
  let up (t : Fin n) := t.succ.succ.succ.succ
  exMem j (exMem b.succ (exMem d.succ.succ (exMem bound.succ.succ.succ
    (.conj (rightTripleFormula (up x) (up d) 3 2)
      (.conj (pairMembershipFormula 3 2 (up ns))
        (.conj (pairMembershipFormula (up i) 1 (up sources))
          (.conj (pairMembershipFormula 3 0 (up fs))
            (disj (.conj (.mem 1 0) (exMem (up g)
              (.conj (pairMembershipFormula (up i).succ 0 (up reps).succ)
                (tripleMembershipFormula 0 (up x).succ (up y).succ (up action).succ))))
              (.conj (.neg (.mem 1 0)) (taggedPairTripleFormula (up y) (up l) (up i) 3 2))))))))))

theorem truth_liftFreshEntryFormula {n} (d l j b ns sources fs bound reps g action i x y : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (liftFreshEntryFormula d l j b ns sources fs bound reps g action i x y) env ↔
      ∃ h ∈ env j, ∃ q ∈ env b, ∃ a ∈ env d, ∃ F ∈ env bound,
        env x = ZFSet.pair (env d) (ZFSet.pair h q) ∧ ZFSet.pair h q ∈ env ns ∧
        ZFSet.pair (env i) a ∈ env sources ∧ ZFSet.pair h F ∈ env fs ∧
        ((a ∈ F ∧ ∃ actor ∈ env g, ZFSet.pair (env i) actor ∈ env reps ∧
          ZFSet.pair (ZFSet.pair actor (env x)) (env y) ∈ env action) ∨
          (a ∉ F ∧ env y = ZFSet.pair (env l) (ZFSet.pair (ZFSet.pair (env i) h) q))) := by
  simp only [liftFreshEntryFormula, truth_exMem, Truth, truth_disj,
    truth_rightTripleFormula, truth_pairMembershipFormula, truth_tripleMembershipFormula,
    truth_taggedPairTripleFormula]
  rfl

def liftedCompressionEntryFormula {n} (z i j d l c ns b maps sources fs reps g action v w : Fin n) :
    BoundedFormula n :=
  let up (t : Fin n) := t.succ.succ.succ
  exMem i (exMem l.succ (exMem c.succ.succ
    (.conj (orderedTripleFormula (up z) 2 1 0)
      (disj (liftOldEntryFormula (up d) (up maps) (up v) 2 1 0)
        (liftFreshEntryFormula (up d) (up l) (up j) (up b) (up ns)
          (up sources) (up fs) (up w) (up reps) (up g) (up action) 2 1 0)))))

theorem truth_liftedCompressionEntryFormula {n} (z i j d l c ns b maps sources fs reps g action v w : Fin n)
    (env : Fin n → ZFSet.{u}) (mapsBound : env v = ZFSet.sUnion (ZFSet.sUnion (env maps)))
    (filterBound : env w = ZFSet.sUnion (ZFSet.sUnion (env fs))) :
    Truth (liftedCompressionEntryFormula z i j d l c ns b maps sources fs reps g action v w) env ↔
      ∃ task ∈ env i, ∃ x ∈ env l, ∃ y ∈ env c,
        env z = ZFSet.pair (ZFSet.pair task x) y ∧
          (liftOldEntry (env d) (env maps) task x y ∨
            liftFreshEntry (env d) (env l) (env j) (env b) (env ns)
              (env sources) (env fs) (env reps) (env g) (env action) task x y) := by
  simp only [liftedCompressionEntryFormula, truth_exMem, Truth, truth_disj,
    truth_orderedTripleFormula, truth_liftOldEntryFormula, truth_liftFreshEntryFormula]
  simp only [liftOldEntry, liftFreshEntry, extend, Fin.cases_succ, Fin.cases_zero,
    mapsBound, filterBound]
  rfl

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
