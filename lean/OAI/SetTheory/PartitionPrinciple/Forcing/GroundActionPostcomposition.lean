import OAI.SetTheory.PartitionPrinciple.Definability.TaskRepresentativeCodes

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def actionPostcomposeEntryFormula {n} (v P A g base : Fin n) : BoundedFormula n :=
  exMem P (exMem P.succ (.conj (orderedPairFormula v.succ.succ 1 0)
    (exMem P.succ.succ (.conj (pairMembershipFormula 2 0 base.succ.succ.succ)
      (tripleMembershipFormula g.succ.succ.succ 0 1 A.succ.succ.succ)))))

theorem truth_actionPostcomposeEntryFormula {n} (v P A g base : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (actionPostcomposeEntryFormula v P A g base) env ↔
      ∃ x ∈ env P, ∃ z ∈ env P, env v = ZFSet.pair x z ∧
        ∃ y ∈ env P, ZFSet.pair x y ∈ env base ∧
          ZFSet.pair (ZFSet.pair (env g) y) z ∈ env A := by
  simp only [actionPostcomposeEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

def actionPostcomposeFormula {n} (P A g base output : Fin n) : BoundedFormula n :=
  let entry := pairMembershipFormula 1 0 output.succ.succ
  let composed := exMem P.succ.succ
    (.conj (pairMembershipFormula 2 0 base.succ.succ.succ)
      (tripleMembershipFormula g.succ.succ.succ 0 1 A.succ.succ.succ))
  .conj (relationBetweenFormula P P output) (.allMem P (.allMem P.succ
    (.conj (imp entry composed) (imp composed entry))))

theorem truth_actionPostcomposeFormula {n} (P A g base output : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (actionPostcomposeFormula P A g base output) env ↔
      env output = actionPostcompose (env P) (env A) (env g) (env base) := by
  simp only [actionPostcomposeFormula, Truth, truth_relationBetweenFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula, truth_imp, truth_exMem, ← iff_def]
  constructor
  · rintro ⟨shape, entries⟩
    apply ZFSet.ext
    intro v
    constructor
    · intro hv
      obtain ⟨x, hx, z, hz, rfl⟩ := ZFSet.mem_prod.1 (shape hv)
      exact (pair_mem_actionPostcompose _ _ _ _ x z).2 ⟨hx, hz, (entries x hx z hz).1 hv⟩
    · intro hv
      obtain ⟨x, hx, z, hz, rfl⟩ := ZFSet.mem_prod.1 (actionPostcompose_subset _ _ _ _ hv)
      exact (entries x hx z hz).2 ((pair_mem_actionPostcompose _ _ _ _ x z).1 hv).2.2
  · intro equal
    refine ⟨equal ▸ actionPostcompose_subset _ _ _ _, ?_⟩
    intro x hx z hz
    change ZFSet.pair x z ∈ env output ↔ ∃ y ∈ env P,
      ZFSet.pair x y ∈ env base ∧ ZFSet.pair (ZFSet.pair (env g) y) z ∈ env A
    rw [equal, pair_mem_actionPostcompose]
    exact ⟨fun h => h.2.2, fun h => ⟨hx, hz, h⟩⟩

theorem realize_actionPostcomposeFormula (M : TransitiveGround.{u}) {n}
    (P A g base output : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (actionPostcomposeFormula P A g base output).toFormula env ↔
      env output = actionPostcompose (env P) (env A) (env g) (env base) :=
  (realize_toFormula M _ env members).trans (truth_actionPostcomposeFormula P A g base output env)

end BoundedFormula

namespace TransitiveGround

open SetFormula

theorem actionPostcompose_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P A g base : ZFSet.{u}} (hP : P ∈ M.sets) (hA : A ∈ M.sets)
    (hg : g ∈ M.sets) (hbase : base ∈ M.sets) : actionPostcompose P A g base ∈ M.sets := by
  let params := extend P (extend A (extend g (extend base Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.actionPostcomposeEntryFormula 0 1 2 3 4) params
    (Fin.cases hP (Fin.cases hA (Fin.cases hg (Fin.cases hbase (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation hP hP)
  have equal : ZFSet.sep (fun v => BoundedFormula.Truth
      (BoundedFormula.actionPostcomposeEntryFormula 0 1 2 3 4) (extend v params))
      (ZFSet.prod P P) = actionPostcompose P A g base := by
    apply ZFSet.ext
    intro v
    rw [ZFSet.mem_sep, actionPostcompose, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_actionPostcomposeEntryFormula 0 1 2 3 4 _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
