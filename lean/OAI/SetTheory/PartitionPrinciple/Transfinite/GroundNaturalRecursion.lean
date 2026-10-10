import OAI.SetTheory.PartitionPrinciple.Geometry.FiniteIterationTraces

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def iterationTraceFormula {k} (n d b step base t zero : Fin k) : BoundedFormula k :=
  .conj (functionFormula d b t) (.conj (pairMembershipFormula zero base t)
    (.allMem n (.allMem d.succ (.allMem b.succ.succ (.allMem b.succ.succ.succ
      (imp (.conj (successorFormula 2 3) (.conj (pairMembershipFormula 3 1 t.succ.succ.succ.succ)
        (pairMembershipFormula 2 0 t.succ.succ.succ.succ)))
        (pairMembershipFormula 1 0 step.succ.succ.succ.succ)))))))

theorem truth_iterationTraceFormula {k} (n d b step base t zero : Fin k)
    (env : Fin k → ZFSet.{u}) (hzero : env zero = ∅) :
    Truth (iterationTraceFormula n d b step base t zero) env ↔
      IterationTraceCode (env n) (env d) (env b) (env step) (env base) (env t) := by
  simp only [iterationTraceFormula, Truth, truth_functionFormula, truth_pairMembershipFormula,
    truth_imp, truth_successorFormula]
  change (ZFSet.IsFunc (env d) (env b) (env t) ∧ ZFSet.pair (env zero) (env base) ∈ env t ∧
    ∀ i ∈ env n, ∀ j ∈ env d, ∀ x ∈ env b, ∀ y ∈ env b,
      (j = insert i i ∧ ZFSet.pair i x ∈ env t ∧ ZFSet.pair j y ∈ env t) →
        ZFSet.pair x y ∈ env step) ↔ _
  rw [hzero]
  exact ⟨fun ⟨func, seed, next⟩ => ⟨func, seed,
    fun i hi j hj x hx y hy succ prev after => next i hi j hj x hx y hy ⟨succ, prev, after⟩⟩,
    fun trace => ⟨trace.function, trace.seed,
      fun i hi j hj x hx y hy h => trace.next i hi j hj x hx y hy h.1 h.2.1 h.2.2⟩⟩

def iterationEntryFormula {k} (z w b step base traces zero : Fin k) : BoundedFormula k :=
  exMem w (exMem b.succ (exMem w.succ.succ (exMem traces.succ.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ.succ 3 2)
      (.conj (successorFormula 1 3)
        (.conj (iterationTraceFormula 3 1 b.succ.succ.succ.succ step.succ.succ.succ.succ
          base.succ.succ.succ.succ 0 zero.succ.succ.succ.succ)
          (pairMembershipFormula 3 2 0)))))))

theorem truth_iterationEntryFormula {k} (z w b step base traces zero : Fin k)
    (env : Fin k → ZFSet.{u}) (hzero : env zero = ∅) :
    Truth (iterationEntryFormula z w b step base traces zero) env ↔
      ∃ n ∈ env w, ∃ y ∈ env b, ∃ d ∈ env w, ∃ t ∈ env traces,
        env z = ZFSet.pair n y ∧ d = insert n n ∧
          IterationTraceCode n d (env b) (env step) (env base) t ∧ ZFSet.pair n y ∈ t := by
  simp only [iterationEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_successorFormula, truth_pairMembershipFormula]
  apply exists_congr
  intro n
  apply and_congr_right
  intro _
  apply exists_congr
  intro y
  apply and_congr_right
  intro _
  apply exists_congr
  intro d
  apply and_congr_right
  intro _
  apply exists_congr
  intro t
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr
    (truth_iterationTraceFormula _ _ _ _ _ _ _ _ (by exact hzero)) Iff.rfl))

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula SetRealization
universe u

theorem natural_recursion_graph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {B : Type u} (s : Presentation B) (f : B → B) (b : B)
    (hB : s.carrier ∈ M.sets) (hf : s.graph s f ∈ M.sets) :
    natPresentation.graph s (fun n => natIterate f b n.down) ∈ M.sets := by
  have hw := M.omega_mem separation infinite
  have hb := M.transitive hB (s.encode_mem b)
  have hzero := M.empty_mem ⟨s.carrier, hB⟩
  let P := ZFSet.prod ZFSet.omega s.carrier
  have hP := M.prod_mem pairing unions powers separation hw hB
  let T := M.groundPower P
  have hT := M.groundPower_mem powers hP
  let params := extend ZFSet.omega (extend s.carrier (extend (s.graph s f)
    (extend (s.encode b) (extend T (extend ∅ Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.iterationEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hw (Fin.cases hB (Fin.cases hf (Fin.cases hb (Fin.cases hT
      (Fin.cases hzero (fun i => Fin.elim0 i))))))) hP
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.iterationEntryFormula 0 1 2 3 4 5 6) (extend z params)) P =
      natPresentation.graph s (fun n => natIterate f b n.down) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_iterationEntryFormula _ _ _ _ _ _ _ _ rfl]
    change (z ∈ P ∧ ∃ n ∈ ZFSet.omega, ∃ y ∈ s.carrier, ∃ d ∈ ZFSet.omega, ∃ t ∈ T,
      z = ZFSet.pair n y ∧ d = insert n n ∧
        IterationTraceCode n d s.carrier (s.graph s f) (s.encode b) t ∧ ZFSet.pair n y ∈ t) ↔ _
    constructor
    · rintro ⟨_, n, hn, y, _, d, _, t, _, eq, succ, trace, out⟩
      obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
      have dcode : d = natSetCode (k + 1) := succ
      have value := (dcode ▸ trace).output s f b out
      rw [eq, value]
      exact (natPresentation.pair_mem_graph s (fun n => natIterate f b n.down) ⟨k⟩ _).2 rfl
    · intro hz
      have shape := (natPresentation.graph_isFunc s (fun n => natIterate f b n.down)).1 hz
      obtain ⟨k, eq⟩ := (natPresentation.mem_graph s (fun n => natIterate f b n.down) z).1 hz
      let t := finiteIterationTrace s f b k.down
      have ht := M.finiteIterationTrace_mem pairing unions separation infinite s f b k.down hB
      have code := finiteIterationTrace_code s f b k.down
      have bound : t ⊆ P := by
        intro a ha
        obtain ⟨i, hi, y, hy, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 ha)
        obtain ⟨m, _, rfl⟩ := (mem_natSetCode i (k.down + 1)).1 hi
        exact ZFSet.pair_mem_prod.2 ⟨(mem_omega_iff_natSetCode _).2 ⟨m, rfl⟩, hy⟩
      exact ⟨shape, natSetCode k.down, natPresentation.encode_mem k,
        s.encode (natIterate f b k.down), s.encode_mem _, natSetCode (k.down + 1),
        (mem_omega_iff_natSetCode _).2 ⟨k.down + 1, rfl⟩, t,
        (M.mem_groundPower P t).2 ⟨ht, bound⟩, eq.symm, rfl, code,
        code.value s f b k.down (Nat.le_refl _)⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
