import OAI.SetTheory.PartitionPrinciple.Forcing.FinitePrincipalNameSupports

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula SetRealization
universe u

def principalSupportFormula {n} (g c l r a : Fin n) : BoundedFormula n :=
  .allMem l (imp (pairMembershipFormula 0 c.succ r.succ)
    (tripleMembershipFormula g.succ 0 0 a.succ))

def principalSupportEntryFormula {n} (z l g r a : Fin n) : BoundedFormula n :=
  exMem l (exMem g.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (principalSupportFormula 0 1 l.succ.succ r.succ.succ a.succ.succ)))

theorem truth_principalSupportFormula {n} (g c l r a : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (principalSupportFormula g c l r a) env ↔
      ∀ x ∈ env l, ZFSet.pair x (env c) ∈ env r → ZFSet.pair (ZFSet.pair (env g) x) x ∈ env a := by
  simp only [principalSupportFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula]
  rfl

theorem truth_principalSupportEntryFormula {n} (z l g r a : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (principalSupportEntryFormula z l g r a) env ↔
      ∃ c ∈ env l, ∃ h ∈ env g, env z = ZFSet.pair c h ∧
        ∀ x ∈ env l, ZFSet.pair x c ∈ env r → ZFSet.pair (ZFSet.pair h x) x ∈ env a := by
  simp only [principalSupportEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_principalSupportFormula]
  rfl

variable {G I : Type u} [Group G] [PartialOrder I]

theorem principalSupport_correct (d : PosetAction G I) (b : Presentation I) (t : Presentation G)
    (C : I) (g : G) :
    Truth (principalSupportFormula 0 1 2 3 4)
      (extend (t.encode g) (extend (b.encode C) (extend b.carrier
        (extend b.conditionOrder (extend (d.actionGraph b t) Fin.elim0))))) ↔ g ∈ d.principalFix C := by
  rw [truth_principalSupportFormula]
  constructor
  · intro fixed x lower
    exact (d.triple_mem_actionGraph b t g x x).1
      (fixed _ (b.encode_mem x) ((b.pair_mem_conditionOrder x C).2 lower))
  · intro fixed x hx lower
    obtain ⟨y, rfl⟩ := (b.mem_carrier x).1 hx
    exact (d.triple_mem_actionGraph b t g y y).2 (fixed y ((b.pair_mem_conditionOrder y C).1 lower))

theorem principalSupportEntry_correct (d : PosetAction G I) (b : Presentation I) (t : Presentation G)
    (z : ZFSet.{u}) :
    Truth (principalSupportEntryFormula 0 1 2 3 4)
      (extend z (extend b.carrier (extend t.carrier
        (extend b.conditionOrder (extend (d.actionGraph b t) Fin.elim0))))) ↔
      z ∈ supportBasisCode b t d.principalFix := by
  rw [truth_principalSupportEntryFormula, supportBasisCode, Presentation.mem_subset]
  constructor
  · rintro ⟨c, hc, h, hh, eq, fixed⟩
    obtain ⟨C, rfl⟩ := (b.mem_carrier c).1 hc
    obtain ⟨g, rfl⟩ := (t.mem_carrier h).1 hh
    refine ⟨(C, g), ?_, eq.symm⟩
    intro x lower
    exact (d.triple_mem_actionGraph b t g x x).1
      (fixed _ (b.encode_mem x) ((b.pair_mem_conditionOrder x C).2 lower))
  · rintro ⟨⟨C, g⟩, fixed, eq⟩
    refine ⟨b.encode C, b.encode_mem C, t.encode g, t.encode_mem g, eq.symm, ?_⟩
    intro x hx lower
    obtain ⟨y, rfl⟩ := (b.mem_carrier x).1 hx
    exact (d.triple_mem_actionGraph b t g y y).2 (fixed y ((b.pair_mem_conditionOrder y C).1 lower))

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
