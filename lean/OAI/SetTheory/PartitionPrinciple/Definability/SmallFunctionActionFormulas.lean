import OAI.SetTheory.PartitionPrinciple.Forcing.GroundFlatSuccessorFullActionGraph

namespace OAI

section

namespace PartitionPilot.Forcing

open SetRealization SetFormula
universe u

def RenameActionRelation (X Y A g p q : ZFSet.{u}) : Prop :=
  ∀ x ∈ X, ∀ x' ∈ X, ∀ y ∈ Y,
    ZFSet.pair (ZFSet.pair g x) x' ∈ A → (ZFSet.pair x y ∈ p ↔ ZFSet.pair x' y ∈ q)

theorem renameActionRelation_iff {X Y G : Type u} [Group G] [PartialOrder X]
    (a : PosetAction G X) (s : Presentation X) (t : Presentation Y) (b : Presentation G)
    (g : G) {p q : ZFSet.{u}} (shapeQ : q ⊆ ZFSet.prod s.carrier t.carrier) :
    RenameActionRelation s.carrier t.carrier (a.actionGraph s b) (b.encode g) p q ↔
      graphRename s t (a.iso g).toEquiv p = q := by
  constructor
  · intro h
    apply s.relation_ext t (graphRename_shape s t _ _) shapeQ
    intro x y
    rw [pair_mem_graphRename]
    exact h _ (s.encode_mem ((a.iso g).symm x)) _ (s.encode_mem x) _ (t.encode_mem y)
      ((a.triple_mem_actionGraph s b g ((a.iso g).symm x) x).2 ((a.iso g).apply_symm_apply x))
  · intro eq i hi j hj v hv rel
    obtain ⟨x, rfl⟩ := (s.mem_carrier i).1 hi
    obtain ⟨x', rfl⟩ := (s.mem_carrier j).1 hj
    obtain ⟨y, rfl⟩ := (t.mem_carrier v).1 hv
    have same := (a.triple_mem_actionGraph s b g x x').1 rel
    rw [← eq, pair_mem_graphRename]
    rw [← same]
    change ZFSet.pair (s.encode x) (t.encode y) ∈ p ↔
      ZFSet.pair (s.encode ((a.iso g).toEquiv.symm ((a.iso g).toEquiv x))) (t.encode y) ∈ p
    rw [(a.iso g).toEquiv.symm_apply_apply]

namespace BoundedFormula

def renameActionFormula {n} (p q g x y a : Fin n) : BoundedFormula n :=
  .allMem x (.allMem x.succ (.allMem y.succ.succ
    (imp (tripleMembershipFormula g.succ.succ.succ 2 1 a.succ.succ.succ)
      (.conj (imp (pairMembershipFormula 2 0 p.succ.succ.succ) (pairMembershipFormula 1 0 q.succ.succ.succ))
        (imp (pairMembershipFormula 1 0 q.succ.succ.succ) (pairMembershipFormula 2 0 p.succ.succ.succ))))))

theorem truth_renameActionFormula {n} (p q g x y a : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (renameActionFormula p q g x y a) env ↔
      RenameActionRelation (env x) (env y) (env a) (env g) (env p) (env q) := by
  simp only [renameActionFormula, Truth, truth_imp, truth_tripleMembershipFormula, truth_pairMembershipFormula]
  constructor
  · intro h i hi j hj v hv rel
    exact ⟨(h i hi j hj v hv rel).1, (h i hi j hj v hv rel).2⟩
  · intro h i hi j hj v hv rel
    exact ⟨(h i hi j hj v hv rel).1, (h i hi j hj v hv rel).2⟩

def smallActionEntryFormula {n} (z g p x y a : Fin n) : BoundedFormula n :=
  exMem g (exMem p.succ (exMem p.succ.succ
    (.conj (orderedTripleFormula z.succ.succ.succ 2 1 0)
      (renameActionFormula 1 0 2 x.succ.succ.succ y.succ.succ.succ a.succ.succ.succ))))

theorem truth_smallActionEntryFormula {n} (z g p x y a : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (smallActionEntryFormula z g p x y a) env ↔
      ∃ h ∈ env g, ∃ r ∈ env p, ∃ s ∈ env p,
        env z = ZFSet.pair (ZFSet.pair h r) s ∧
          RenameActionRelation (env x) (env y) (env a) h r s := by
  simp only [smallActionEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula, truth_renameActionFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
