import OAI.SetTheory.PartitionPrinciple.Definability.FiniteWordOperationFormulas
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalAlphabetInversion
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundFiniteWordLength
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundNaturalRecursion

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def natSuccessorEntryFormula {k} (z w : Fin k) : BoundedFormula k :=
  exMem w (exMem w.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (successorFormula 0 1)))

theorem truth_natSuccessorEntryFormula {k} (z w : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (natSuccessorEntryFormula z w) env ↔
      ∃ a ∈ env w, ∃ b ∈ env w, env z = ZFSet.pair a b ∧ b = insert a a := by
  simp only [natSuccessorEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_successorFormula]
  rfl

def natAddEntryFormula {k} (z w step traces zero : Fin k) : BoundedFormula k :=
  exMem w (exMem w.succ (exMem w.succ.succ (exMem w.succ.succ.succ
    (exMem traces.succ.succ.succ.succ
      (.conj (orderedTripleFormula z.succ.succ.succ.succ.succ 4 3 2)
        (.conj (successorFormula 1 3)
          (.conj (iterationTraceFormula 3 1 w.succ.succ.succ.succ.succ
            step.succ.succ.succ.succ.succ 4 0 zero.succ.succ.succ.succ.succ)
            (pairMembershipFormula 3 2 0))))))))

theorem truth_natAddEntryFormula {k} (z w step traces zero : Fin k)
    (env : Fin k → ZFSet.{u}) (hzero : env zero = ∅) :
    Truth (natAddEntryFormula z w step traces zero) env ↔
      ∃ a ∈ env w, ∃ b ∈ env w, ∃ c ∈ env w, ∃ d ∈ env w, ∃ t ∈ env traces,
        env z = ZFSet.pair (ZFSet.pair a b) c ∧ d = insert b b ∧
          IterationTraceCode b d (env w) (env step) a t ∧ ZFSet.pair b c ∈ t := by
  simp only [natAddEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_successorFormula, truth_pairMembershipFormula]
  apply exists_congr
  intro a
  apply and_congr_right
  intro _
  apply exists_congr
  intro b
  apply and_congr_right
  intro _
  apply exists_congr
  intro c
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

def natMulEntryFormula {k} (z w family traces zero : Fin k) : BoundedFormula k :=
  exMem w (exMem w.succ (exMem w.succ.succ (exMem w.succ.succ.succ
    (exMem traces.succ.succ.succ.succ (exMem traces.succ.succ.succ.succ.succ
      (.conj (orderedTripleFormula z.succ.succ.succ.succ.succ.succ 5 4 3)
        (.conj (successorFormula 2 4)
          (.conj (pairMembershipFormula 5 0 family.succ.succ.succ.succ.succ.succ)
            (.conj (iterationTraceFormula 4 2 w.succ.succ.succ.succ.succ.succ
              0 zero.succ.succ.succ.succ.succ.succ 1 zero.succ.succ.succ.succ.succ.succ)
              (pairMembershipFormula 4 3 1))))))))))

theorem truth_natMulEntryFormula {k} (z w family traces zero : Fin k)
    (env : Fin k → ZFSet.{u}) (hzero : env zero = ∅) :
    Truth (natMulEntryFormula z w family traces zero) env ↔
      ∃ a ∈ env w, ∃ b ∈ env w, ∃ c ∈ env w, ∃ d ∈ env w,
      ∃ t ∈ env traces, ∃ step ∈ env traces,
        env z = ZFSet.pair (ZFSet.pair a b) c ∧ d = insert b b ∧
          ZFSet.pair a step ∈ env family ∧
            IterationTraceCode b d (env w) step ∅ t ∧ ZFSet.pair b c ∈ t := by
  simp only [natMulEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_successorFormula, truth_pairMembershipFormula]
  apply exists_congr
  intro a
  apply and_congr_right
  intro _
  apply exists_congr
  intro b
  apply and_congr_right
  intro _
  apply exists_congr
  intro c
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
  apply exists_congr
  intro step
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  have correct := truth_iterationTraceFormula 4 2 w.succ.succ.succ.succ.succ.succ
    0 zero.succ.succ.succ.succ.succ.succ 1 zero.succ.succ.succ.succ.succ.succ
    (extend step (extend t (extend d (extend c (extend b (extend a env)))))) (by exact hzero)
  constructor
  · rintro ⟨h, entry⟩
    have trace := correct.1 h
    change IterationTraceCode b d (env w) step (env zero) t at trace
    exact ⟨by simpa only [hzero] using trace, entry⟩
  · rintro ⟨trace, entry⟩
    refine ⟨correct.2 ?_, entry⟩
    change IterationTraceCode b d (env w) step (env zero) t
    simpa only [hzero] using trace

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem natSuccessorGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0) : natSuccessorGraph ∈ M.sets := by
  have hw := M.omega_mem separation infinite
  have bound := M.prod_mem pairing unions powers separation hw hw
  let params := extend ZFSet.omega Fin.elim0
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.natSuccessorEntryFormula 0 1) params
    (Fin.cases hw (fun i => Fin.elim0 i)) bound
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.natSuccessorEntryFormula 0 1) (extend z params))
      (ZFSet.prod ZFSet.omega ZFSet.omega) = natSuccessorGraph := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_natSuccessorEntryFormula]
    change (z ∈ ZFSet.prod ZFSet.omega ZFSet.omega ∧ ∃ a ∈ ZFSet.omega,
      ∃ b ∈ ZFSet.omega, z = ZFSet.pair a b ∧ b = insert a a) ↔ _
    constructor
    · rintro ⟨_, a, ha, b, _, rfl, rfl⟩
      obtain ⟨a, rfl⟩ := (mem_omega_iff_natSetCode a).1 ha
      exact (pair_mem_natSuccessorGraph a (a + 1)).2 rfl
    · intro hz
      have shape := natSuccessorGraph_isFunc.1 hz
      obtain ⟨a, rfl⟩ := (natPresentation.mem_graph natPresentation
        (fun n => ⟨n.down + 1⟩) z).1 hz
      exact ⟨shape, natSetCode a.down, natPresentation.encode_mem a,
        natSetCode (a.down + 1), natPresentation.encode_mem ⟨a.down + 1⟩, rfl, rfl⟩
  exact equal ▸ selected

theorem naturalFiniteTrace_mem_relations
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (f : ULift.{u} Nat → ULift.{u} Nat) (a n : Nat) :
    finiteIterationTrace natPresentation f ⟨a⟩ n ∈ M.groundRelations ZFSet.omega ZFSet.omega := by
  refine (M.mem_groundRelations _ _ _).2
    ⟨M.finiteIterationTrace_mem pairing unions separation infinite natPresentation f ⟨a⟩ n
      (M.omega_mem separation infinite), ?_⟩
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1
    ((finiteIterationTrace_code natPresentation f ⟨a⟩ n).function.1 hz)
  obtain ⟨k, _, rfl⟩ := (mem_natSetCode x (n + 1)).1 hx
  exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega k, hy⟩

theorem natAddGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0) : natAddGraph ∈ M.sets := by
  have hw := M.omega_mem separation infinite
  have hs := M.natSuccessorGraph_mem pairing unions powers separation infinite
  have hz := M.empty_mem ⟨ZFSet.omega, hw⟩
  let T := M.groundRelations ZFSet.omega ZFSet.omega
  have ht := M.groundRelations_mem pairing unions powers separation hw hw
  let P := ZFSet.prod (ZFSet.prod ZFSet.omega ZFSet.omega) ZFSet.omega
  have hp := M.prod_mem pairing unions powers separation
    (M.prod_mem pairing unions powers separation hw hw) hw
  let params := extend ZFSet.omega (extend natSuccessorGraph (extend T (extend ∅ Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.natAddEntryFormula 0 1 2 3 4) params
    (Fin.cases hw (Fin.cases hs (Fin.cases ht (Fin.cases hz (fun i => Fin.elim0 i))))) hp
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.natAddEntryFormula 0 1 2 3 4) (extend z params)) P = natAddGraph := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_natAddEntryFormula _ _ _ _ _ _ rfl]
    change (z ∈ P ∧ ∃ a ∈ ZFSet.omega, ∃ b ∈ ZFSet.omega, ∃ c ∈ ZFSet.omega,
      ∃ d ∈ ZFSet.omega, ∃ t ∈ T, z = ZFSet.pair (ZFSet.pair a b) c ∧ d = insert b b ∧
        IterationTraceCode b d ZFSet.omega natSuccessorGraph a t ∧ ZFSet.pair b c ∈ t) ↔ _
    constructor
    · rintro ⟨_, a, ha, b, hb, c, hc, d, _, t, _, rfl, rfl, trace, entry⟩
      obtain ⟨a, rfl⟩ := (mem_omega_iff_natSetCode a).1 ha
      obtain ⟨b, rfl⟩ := (mem_omega_iff_natSetCode b).1 hb
      obtain ⟨c, rfl⟩ := (mem_omega_iff_natSetCode c).1 hc
      have value := trace.output natPresentation (fun n => ⟨n.down + 1⟩) ⟨a⟩ entry
      have eq : natSetCode c = natSetCode (a + b) := by
        simpa only [natIterate_successor, natPresentation] using value
      exact (pair_mem_natAddGraph a b c).2 (natSetCode_injective eq)
    · intro h
      have shape := natAddGraph_isFunc.1 h
      obtain ⟨⟨a, b⟩, rfl⟩ := ((natPresentation.product natPresentation).mem_graph
        natPresentation (fun n => ⟨n.1.down + n.2.down⟩) z).1 h
      let f := fun n : ULift.{u} Nat => (⟨n.down + 1⟩ : ULift.{u} Nat)
      let t := finiteIterationTrace natPresentation f a b.down
      have code := finiteIterationTrace_code natPresentation f a b.down
      refine ⟨shape, natSetCode a.down, natPresentation.encode_mem a,
        natSetCode b.down, natPresentation.encode_mem b, natSetCode (a.down + b.down),
        natSetCode_mem_omega _, natSetCode (b.down + 1), natSetCode_mem_omega _, t,
        M.naturalFiniteTrace_mem_relations pairing unions separation infinite f a.down b.down,
        rfl, rfl, code, ?_⟩
      have iterate : natIterate f a b.down = ⟨a.down + b.down⟩ :=
        natIterate_successor a.down b.down
      have output := code.value natPresentation f a b.down (Nat.le_refl _)
      rw [iterate] at output
      exact output
  exact equal ▸ selected

theorem natMulGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0) : natMulGraph ∈ M.sets := by
  have hw := M.omega_mem separation infinite
  have hadd := M.natAddGraph_mem pairing unions powers separation infinite
  have hz := M.empty_mem ⟨ZFSet.omega, hw⟩
  let T := M.groundRelations ZFSet.omega ZFSet.omega
  have ht := M.groundRelations_mem pairing unions powers separation hw hw
  let family := M.indexedRelationSections ZFSet.omega ZFSet.omega ZFSet.omega natAddGraph
  have spec := M.indexedRelationSections_spec pairing unions powers separation hw hw hw hadd
  let P := ZFSet.prod (ZFSet.prod ZFSet.omega ZFSet.omega) ZFSet.omega
  have hp := M.prod_mem pairing unions powers separation
    (M.prod_mem pairing unions powers separation hw hw) hw
  let params := extend ZFSet.omega (extend family (extend T (extend ∅ Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.natMulEntryFormula 0 1 2 3 4) params
    (Fin.cases hw (Fin.cases spec.1 (Fin.cases ht (Fin.cases hz (fun i => Fin.elim0 i))))) hp
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.natMulEntryFormula 0 1 2 3 4) (extend z params)) P = natMulGraph := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_natMulEntryFormula _ _ _ _ _ _ rfl]
    change (z ∈ P ∧ ∃ a ∈ ZFSet.omega, ∃ b ∈ ZFSet.omega, ∃ c ∈ ZFSet.omega,
      ∃ d ∈ ZFSet.omega, ∃ t ∈ T, ∃ step ∈ T,
        z = ZFSet.pair (ZFSet.pair a b) c ∧ d = insert b b ∧ ZFSet.pair a step ∈ family ∧
          IterationTraceCode b d ZFSet.omega step ∅ t ∧ ZFSet.pair b c ∈ t) ↔ _
    constructor
    · rintro ⟨_, a, ha, b, hb, c, hc, d, _, t, _, step, _, rfl, rfl, member, trace, entry⟩
      obtain ⟨a, rfl⟩ := (mem_omega_iff_natSetCode a).1 ha
      obtain ⟨b, rfl⟩ := (mem_omega_iff_natSetCode b).1 hb
      obtain ⟨c, rfl⟩ := (mem_omega_iff_natSetCode c).1 hc
      have eqStep : step = natAddSection a :=
        ((spec.2.2 _ _).1 member).2.trans (natAddSection_eq a).symm
      rw [eqStep] at trace
      have value := trace.output natPresentation (fun n => ⟨a + n.down⟩) ⟨0⟩ entry
      have eq : natSetCode c = natSetCode (a * b) := by
        simpa only [natIterate_add, natPresentation] using value
      exact (pair_mem_natMulGraph a b c).2 (natSetCode_injective eq)
    · intro h
      have shape := natMulGraph_isFunc.1 h
      obtain ⟨⟨a, b⟩, rfl⟩ := ((natPresentation.product natPresentation).mem_graph
        natPresentation (fun n => ⟨n.1.down * n.2.down⟩) z).1 h
      let f := fun n : ULift.{u} Nat => (⟨a.down + n.down⟩ : ULift.{u} Nat)
      let t := finiteIterationTrace natPresentation f ⟨0⟩ b.down
      have code := finiteIterationTrace_code natPresentation f ⟨0⟩ b.down
      have member : ZFSet.pair (natSetCode a.down) (natAddSection a.down) ∈ family :=
        (spec.2.2 _ _).2 ⟨natPresentation.encode_mem a, natAddSection_eq a.down⟩
      have stepBound : natAddSection a.down ∈ T := (ZFSet.pair_mem_prod.1 (spec.2.1.1 member)).2
      refine ⟨shape, natSetCode a.down, natPresentation.encode_mem a,
        natSetCode b.down, natPresentation.encode_mem b, natSetCode (a.down * b.down),
        natSetCode_mem_omega _, natSetCode (b.down + 1), natSetCode_mem_omega _, t,
        M.naturalFiniteTrace_mem_relations pairing unions separation infinite f 0 b.down,
        natAddSection a.down, stepBound, rfl, rfl, member, code, ?_⟩
      simpa only [t, f, natIterate_add, natPresentation] using code.value natPresentation f ⟨0⟩ b.down (Nat.le_refl _)
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace BoundedFormula

def finiteWordMapEntryFormula {k} (z wordsA wordsB omega a b e : Fin k) : BoundedFormula k :=
  exMem wordsA (exMem wordsB.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (finiteWordMapFormula omega.succ.succ a.succ.succ b.succ.succ e.succ.succ 1 0)))

theorem truth_finiteWordMapEntryFormula {k} (z wordsA wordsB omega a b e : Fin k)
    (env : Fin k → ZFSet.{u}) :
    Truth (finiteWordMapEntryFormula z wordsA wordsB omega a b e) env ↔
      ∃ f ∈ env wordsA, ∃ g ∈ env wordsB, env z = ZFSet.pair f g ∧
        FiniteWordMapCode (env omega) (env a) (env b) (env e) f g := by
  simp only [finiteWordMapEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_finiteWordMapFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def finiteWordMapGraph (A B e : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ f ∈ M.finiteWords A, ∃ g ∈ M.finiteWords B,
    z = ZFSet.pair f g ∧ FiniteWordMapCode ZFSet.omega A B e f g)
    (ZFSet.prod (M.finiteWords A) (M.finiteWords B))

theorem pair_mem_finiteWordMapGraph (A B e f g : ZFSet.{u}) :
    ZFSet.pair f g ∈ M.finiteWordMapGraph A B e ↔
      f ∈ M.finiteWords A ∧ g ∈ M.finiteWords B ∧
        FiniteWordMapCode ZFSet.omega A B e f g := by
  rw [finiteWordMapGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, x, hx, y, hy, eq, code⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hx, hy, code⟩
  · rintro ⟨hf, hg, code⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hf, hg⟩, f, hf, g, hg, rfl, code⟩

theorem finiteWordMapGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A B e : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (he : e ∈ M.sets) :
    M.finiteWordMapGraph A B e ∈ M.sets := by
  have hw := M.omega_mem separation infinite
  have hWA := M.finiteWords_mem pairing unions powers separation infinite hA
  have hWB := M.finiteWords_mem pairing unions powers separation infinite hB
  let params := extend ZFSet.omega (extend A (extend B (extend e
    (extend (M.finiteWords A) (extend (M.finiteWords B) Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.finiteWordMapEntryFormula 0 5 6 1 2 3 4) params
    (Fin.cases hw (Fin.cases hA (Fin.cases hB (Fin.cases he
      (Fin.cases hWA (Fin.cases hWB (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hWA hWB)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.finiteWordMapEntryFormula 0 5 6 1 2 3 4) (extend z params))
      (ZFSet.prod (M.finiteWords A) (M.finiteWords B)) = M.finiteWordMapGraph A B e := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, finiteWordMapGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_finiteWordMapEntryFormula 0 5 6 1 2 3 4 _)
  exact eq ▸ selected

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable {B D : Type u} (s : Presentation B) (t : Presentation D) (e : B → D)
variable (hB : s.carrier ∈ M.sets) (hD : t.carrier ∈ M.sets)

theorem finiteWordMapGraph_eq_graph :
    M.finiteWordMapGraph s.carrier t.carrier (s.graph t e) =
      (finiteWordPresentation s M pairing unions separation infinite hB).graph
        (finiteWordPresentation t M pairing unions separation infinite hD) (List.map e) := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph]
  change z ∈ M.finiteWordMapGraph s.carrier t.carrier (s.graph t e) ↔
    ∃ xs, ZFSet.pair (finiteWordGraph s xs) (finiteWordGraph t (xs.map e)) = z
  constructor
  · intro hz
    obtain ⟨f, hf, g, hg, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).1
    obtain ⟨xs, rfl⟩ := (finiteWords_exact_lists s M pairing unions separation infinite hB f).1 hf
    obtain ⟨ys, rfl⟩ := (finiteWords_exact_lists t M pairing unions separation infinite hD g).1 hg
    have code := ((M.pair_mem_finiteWordMapGraph _ _ _ _ _).1 hz).2.2
    have eq := (finiteWordMapCode_iff s t e xs ys).1 code
    subst ys
    exact ⟨xs, rfl⟩
  · rintro ⟨xs, rfl⟩
    exact (M.pair_mem_finiteWordMapGraph _ _ _ _ _).2
      ⟨finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hB xs,
        finiteWordGraph_mem_finiteWords t M pairing unions separation infinite hD (xs.map e),
        (finiteWordMapCode_iff s t e xs (xs.map e)).2 rfl⟩

include pairing unions separation infinite hB hD in
theorem finiteWordMapGraph_function :
    ZFSet.IsFunc (M.finiteWords s.carrier) (M.finiteWords t.carrier)
      (M.finiteWordMapGraph s.carrier t.carrier (s.graph t e)) := by
  rw [M.finiteWordMapGraph_eq_graph pairing unions separation infinite s t e hB hD]
  exact (finiteWordPresentation s M pairing unions separation infinite hB).graph_isFunc
    (finiteWordPresentation t M pairing unions separation infinite hD) _

end TransitiveGround





namespace BoundedFormula

def finiteWordAppendEntryFormula {n} (z words alphabet omega add : Fin n) : BoundedFormula n :=
  exMem words (exMem words.succ (exMem words.succ.succ
    (.conj (orderedTripleFormula z.succ.succ.succ 2 1 0)
      (finiteWordAppendFormula alphabet.succ.succ.succ omega.succ.succ.succ
        add.succ.succ.succ 2 1 0))))

theorem truth_finiteWordAppendEntryFormula {n} (z words alphabet omega add : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (finiteWordAppendEntryFormula z words alphabet omega add) env ↔
      ∃ f ∈ env words, ∃ g ∈ env words, ∃ h ∈ env words,
        env z = ZFSet.pair (ZFSet.pair f g) h ∧
          FiniteWordAppendCode (env alphabet) (env omega) (env add) f g h := by
  simp only [finiteWordAppendEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_finiteWordAppendFormula]
  rfl

def finiteWordReverseEntryFormula {n} (z words alphabet omega add : Fin n) : BoundedFormula n :=
  exMem words (exMem words.succ
    (.conj (orderedPairFormula z.succ.succ 1 0)
      (finiteWordReverseFormula alphabet.succ.succ omega.succ.succ add.succ.succ 1 0)))

theorem truth_finiteWordReverseEntryFormula {n} (z words alphabet omega add : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (finiteWordReverseEntryFormula z words alphabet omega add) env ↔
      ∃ f ∈ env words, ∃ h ∈ env words, env z = ZFSet.pair f h ∧
        FiniteWordReverseCode (env alphabet) (env omega) (env add) f h := by
  simp only [finiteWordReverseEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_finiteWordReverseFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def finiteWordAppendGraph (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ f ∈ M.finiteWords A, ∃ g ∈ M.finiteWords A,
    ∃ h ∈ M.finiteWords A, z = ZFSet.pair (ZFSet.pair f g) h ∧
      FiniteWordAppendCode A ZFSet.omega natAddGraph f g h)
    (ZFSet.prod (ZFSet.prod (M.finiteWords A) (M.finiteWords A)) (M.finiteWords A))

noncomputable def finiteWordReverseGraph (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ f ∈ M.finiteWords A, ∃ h ∈ M.finiteWords A,
    z = ZFSet.pair f h ∧ FiniteWordReverseCode A ZFSet.omega natAddGraph f h)
    (ZFSet.prod (M.finiteWords A) (M.finiteWords A))

theorem pair_mem_finiteWordAppendGraph (A f g h : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair f g) h ∈ M.finiteWordAppendGraph A ↔
      f ∈ M.finiteWords A ∧ g ∈ M.finiteWords A ∧ h ∈ M.finiteWords A ∧
        FiniteWordAppendCode A ZFSet.omega natAddGraph f g h := by
  rw [finiteWordAppendGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, f', hf, g', hg, h', hh, eq, code⟩
    obtain ⟨fg, rfl⟩ := ZFSet.pair_inj.1 eq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 fg
    exact ⟨hf, hg, hh, code⟩
  · rintro ⟨hf, hg, hh, code⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hf, hg⟩, hh⟩,
      f, hf, g, hg, h, hh, rfl, code⟩

theorem pair_mem_finiteWordReverseGraph (A f h : ZFSet.{u}) :
    ZFSet.pair f h ∈ M.finiteWordReverseGraph A ↔
      f ∈ M.finiteWords A ∧ h ∈ M.finiteWords A ∧
        FiniteWordReverseCode A ZFSet.omega natAddGraph f h := by
  rw [finiteWordReverseGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, f', hf, h', hh, eq, code⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hf, hh, code⟩
  · rintro ⟨hf, hh, code⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hf, hh⟩, f, hf, h, hh, rfl, code⟩

theorem finiteWordAppendGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) : M.finiteWordAppendGraph A ∈ M.sets := by
  have hWords := M.finiteWords_mem pairing unions powers separation infinite hA
  have hOmega := M.omega_mem separation infinite
  have hAdd := M.natAddGraph_mem pairing unions powers separation infinite
  have domain := M.prod_mem pairing unions powers separation hWords hWords
  have bound := M.prod_mem pairing unions powers separation domain hWords
  let params := extend (M.finiteWords A) (extend A (extend ZFSet.omega (extend natAddGraph Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.finiteWordAppendEntryFormula 0 1 2 3 4) params
    (Fin.cases hWords (Fin.cases hA (Fin.cases hOmega (Fin.cases hAdd (fun j => Fin.elim0 j))))) bound
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.finiteWordAppendEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod (ZFSet.prod (M.finiteWords A) (M.finiteWords A)) (M.finiteWords A)) =
        M.finiteWordAppendGraph A := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, finiteWordAppendGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_finiteWordAppendEntryFormula 0 1 2 3 4 _)
  exact eq ▸ selected

theorem finiteWordReverseGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) : M.finiteWordReverseGraph A ∈ M.sets := by
  have hWords := M.finiteWords_mem pairing unions powers separation infinite hA
  have hOmega := M.omega_mem separation infinite
  have hAdd := M.natAddGraph_mem pairing unions powers separation infinite
  have bound := M.prod_mem pairing unions powers separation hWords hWords
  let params := extend (M.finiteWords A) (extend A (extend ZFSet.omega (extend natAddGraph Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.finiteWordReverseEntryFormula 0 1 2 3 4) params
    (Fin.cases hWords (Fin.cases hA (Fin.cases hOmega (Fin.cases hAdd (fun j => Fin.elim0 j))))) bound
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.finiteWordReverseEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod (M.finiteWords A) (M.finiteWords A)) = M.finiteWordReverseGraph A := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, finiteWordReverseGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_finiteWordReverseEntryFormula 0 1 2 3 4 _)
  exact eq ▸ selected

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

theorem finiteWordAppendGraph_eq_graph {B : Type u} (s : Presentation B)
    (hB : s.carrier ∈ M.sets) :
    M.finiteWordAppendGraph s.carrier =
      ((finiteWordPresentation s M pairing unions separation infinite hB).product
        (finiteWordPresentation s M pairing unions separation infinite hB)).graph
          (finiteWordPresentation s M pairing unions separation infinite hB)
            (fun p => p.1 ++ p.2) := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph]
  change z ∈ M.finiteWordAppendGraph s.carrier ↔
    ∃ p : List B × List B, ZFSet.pair
      (ZFSet.pair (finiteWordGraph s p.1) (finiteWordGraph s p.2))
        (finiteWordGraph s (p.1 ++ p.2)) = z
  constructor
  · intro hz
    obtain ⟨fg, hfg, h, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).1
    obtain ⟨f, hf, g, hg, rfl⟩ := ZFSet.mem_prod.1 hfg
    obtain ⟨xs, rfl⟩ := (finiteWords_exact_lists s M pairing unions separation infinite hB f).1 hf
    obtain ⟨ys, rfl⟩ := (finiteWords_exact_lists s M pairing unions separation infinite hB g).1 hg
    have code := ((M.pair_mem_finiteWordAppendGraph _ _ _ _).1 hz).2.2.2
    have eq := (finiteWordAppendCode_iff s xs ys h).1 code
    subst h
    exact ⟨(xs, ys), rfl⟩
  · rintro ⟨⟨xs, ys⟩, rfl⟩
    exact (M.pair_mem_finiteWordAppendGraph _ _ _ _).2
      ⟨finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hB xs,
        finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hB ys,
        finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hB (xs ++ ys),
        finiteWordGraph_append_code s xs ys⟩

theorem finiteWordReverseGraph_eq_graph {B : Type u} (s : Presentation B)
    (hB : s.carrier ∈ M.sets) :
    M.finiteWordReverseGraph s.carrier =
      (finiteWordPresentation s M pairing unions separation infinite hB).graph
        (finiteWordPresentation s M pairing unions separation infinite hB) List.reverse := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph]
  change z ∈ M.finiteWordReverseGraph s.carrier ↔
    ∃ xs : List B, ZFSet.pair (finiteWordGraph s xs) (finiteWordGraph s xs.reverse) = z
  constructor
  · intro hz
    obtain ⟨f, hf, h, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).1
    obtain ⟨xs, rfl⟩ := (finiteWords_exact_lists s M pairing unions separation infinite hB f).1 hf
    have code := ((M.pair_mem_finiteWordReverseGraph _ _ _).1 hz).2.2
    have eq := (finiteWordReverseCode_iff s xs h).1 code
    subst h
    exact ⟨xs, rfl⟩
  · rintro ⟨xs, rfl⟩
    exact (M.pair_mem_finiteWordReverseGraph _ _ _).2
      ⟨finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hB xs,
        finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hB xs.reverse,
        finiteWordGraph_reverse_code s xs⟩

include pairing unions separation infinite in
theorem finiteWordAppendGraph_function {A : ZFSet.{u}} (hA : A ∈ M.sets) :
    ZFSet.IsFunc (ZFSet.prod (M.finiteWords A) (M.finiteWords A)) (M.finiteWords A)
      (M.finiteWordAppendGraph A) := by
  let s := SetMembers.presentation A
  change ZFSet.IsFunc (ZFSet.prod (M.finiteWords s.carrier) (M.finiteWords s.carrier))
    (M.finiteWords s.carrier) (M.finiteWordAppendGraph s.carrier)
  rw [M.finiteWordAppendGraph_eq_graph pairing unions separation infinite s hA]
  exact ((finiteWordPresentation s M pairing unions separation infinite hA).product
    (finiteWordPresentation s M pairing unions separation infinite hA)).graph_isFunc
      (finiteWordPresentation s M pairing unions separation infinite hA) _

include pairing unions separation infinite in
theorem finiteWordReverseGraph_function {A : ZFSet.{u}} (hA : A ∈ M.sets) :
    ZFSet.IsFunc (M.finiteWords A) (M.finiteWords A) (M.finiteWordReverseGraph A) := by
  let s := SetMembers.presentation A
  change ZFSet.IsFunc (M.finiteWords s.carrier) (M.finiteWords s.carrier)
    (M.finiteWordReverseGraph s.carrier)
  rw [M.finiteWordReverseGraph_eq_graph pairing unions separation infinite s hA]
  exact (finiteWordPresentation s M pairing unions separation infinite hA).graph_isFunc
    (finiteWordPresentation s M pairing unions separation infinite hA) _

end TransitiveGround






def externalWordInverse {J L : Type u} [Inv J] (xs : List (J ⊕ (L × Bool))) :
    List (J ⊕ (L × Bool)) := (xs.map externalSymbolInverse).reverse

theorem externalWordInverse_involutive {J L : Type u} [InvolutiveInv J] :
    Function.Involutive (externalWordInverse : List (J ⊕ (L × Bool)) → List (J ⊕ (L × Bool))) := by
  intro xs
  simp only [externalWordInverse, List.map_reverse, List.reverse_reverse, List.map_map]
  have eq : (externalSymbolInverse : J ⊕ (L × Bool) → J ⊕ (L × Bool)) ∘
      externalSymbolInverse = id := by
    funext x
    exact externalSymbolInverse_involutive x
  rw [eq, List.map_id]

theorem externalWordInverse_append {J L : Type u} [Inv J]
    (xs ys : List (J ⊕ (L × Bool))) :
    externalWordInverse (xs ++ ys) = externalWordInverse ys ++ externalWordInverse xs := by
  simp only [externalWordInverse, List.map_append, List.reverse_append]

private theorem compose_presentation_graphs {A B C : Type u}
    (s : Presentation A) (t : Presentation B) (v : Presentation C) (f : A → B) (g : B → C) :
    relationCompose s.carrier t.carrier v.carrier (s.graph t f) (t.graph v g) =
      s.graph v (fun x => g (f x)) := by
  apply ZFSet.ext
  intro z
  rw [mem_relationCompose, Presentation.mem_graph]
  constructor
  · rintro ⟨x, hx, y, hy, w, hw, rfl, first, second⟩
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (t.mem_carrier y).1 hy
    obtain ⟨c, rfl⟩ := (v.mem_carrier w).1 hw
    have ab := (s.pair_mem_graph t f a b).1 first
    have bc := (t.pair_mem_graph v g b c).1 second
    subst b
    subst c
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨s.encode a, s.encode_mem a, t.encode (f a), t.encode_mem (f a),
      v.encode (g (f a)), v.encode_mem (g (f a)), rfl,
      (s.pair_mem_graph t f a (f a)).2 rfl,
      (t.pair_mem_graph v g (f a) (g (f a))).2 rfl⟩

namespace TransitiveGround

variable (M : TransitiveGround.{u})

noncomputable def externalInverseWordGraph (G S inv : ZFSet.{u}) : ZFSet.{u} :=
  let alphabet := externalGeneratorAlphabet G S
  let words := M.finiteWords alphabet
  relationCompose words words words
    (M.finiteWordMapGraph alphabet alphabet (externalSymbolInverseGraph G S inv))
    (M.finiteWordReverseGraph alphabet)

theorem externalInverseWordGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {G S inv : ZFSet.{u}} (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hInv : inv ∈ M.sets) :
    M.externalInverseWordGraph G S inv ∈ M.sets := by
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  have hWords := M.finiteWords_mem pairing unions powers separation infinite hAlphabet
  have hSymbols := M.externalSymbolInverseGraph_mem pairing unions powers separation hG hS hInv
  exact M.relationCompose_mem pairing unions powers separation hWords hWords hWords
    (M.finiteWordMapGraph_mem pairing unions powers separation infinite hAlphabet hAlphabet hSymbols)
    (M.finiteWordReverseGraph_mem pairing unions powers separation infinite hAlphabet)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable {J L : Type u} [Inv J] (s : Presentation J) (t : Presentation L)
variable (hAlphabet : externalGeneratorAlphabet s.carrier t.carrier ∈ M.sets)

theorem externalInverseWordGraph_eq_graph :
    M.externalInverseWordGraph s.carrier t.carrier (s.graph s Inv.inv) =
      (finiteWordPresentation (externalGeneratorAlphabetPresentation s t)
        M pairing unions separation infinite hAlphabet).graph
      (finiteWordPresentation (externalGeneratorAlphabetPresentation s t)
        M pairing unions separation infinite hAlphabet) externalWordInverse := by
  unfold externalInverseWordGraph
  dsimp only
  rw [externalSymbolInverseGraph_eq_graph]
  have mapEq := M.finiteWordMapGraph_eq_graph pairing unions separation infinite
    (externalGeneratorAlphabetPresentation s t) (externalGeneratorAlphabetPresentation s t)
    externalSymbolInverse hAlphabet hAlphabet
  change M.finiteWordMapGraph (externalGeneratorAlphabet s.carrier t.carrier)
    (externalGeneratorAlphabet s.carrier t.carrier)
    ((externalGeneratorAlphabetPresentation s t).graph
      (externalGeneratorAlphabetPresentation s t) externalSymbolInverse) = _ at mapEq
  rw [mapEq]
  have reverseEq := M.finiteWordReverseGraph_eq_graph pairing unions separation infinite
    (externalGeneratorAlphabetPresentation s t) hAlphabet
  change M.finiteWordReverseGraph (externalGeneratorAlphabet s.carrier t.carrier) = _ at reverseEq
  rw [reverseEq]
  let p := finiteWordPresentation (externalGeneratorAlphabetPresentation s t)
    M pairing unions separation infinite hAlphabet
  exact compose_presentation_graphs p p p (List.map externalSymbolInverse) List.reverse

include pairing unions separation infinite hAlphabet in
theorem externalInverseWordGraph_entry_iff (xs ys : List (J ⊕ (L × Bool))) :
    ZFSet.pair (finiteWordGraph (externalGeneratorAlphabetPresentation s t) xs)
      (finiteWordGraph (externalGeneratorAlphabetPresentation s t) ys) ∈
        M.externalInverseWordGraph s.carrier t.carrier (s.graph s Inv.inv) ↔
      externalWordInverse xs = ys := by
  rw [M.externalInverseWordGraph_eq_graph pairing unions separation infinite s t hAlphabet]
  exact (finiteWordPresentation (externalGeneratorAlphabetPresentation s t)
    M pairing unions separation infinite hAlphabet).pair_mem_graph _ _ xs ys

include pairing unions separation infinite hAlphabet in
theorem externalInverseWordGraph_function :
    ZFSet.IsFunc (M.finiteWords (externalGeneratorAlphabet s.carrier t.carrier))
      (M.finiteWords (externalGeneratorAlphabet s.carrier t.carrier))
      (M.externalInverseWordGraph s.carrier t.carrier (s.graph s Inv.inv)) := by
  rw [M.externalInverseWordGraph_eq_graph pairing unions separation infinite s t hAlphabet]
  exact (finiteWordPresentation (externalGeneratorAlphabetPresentation s t)
    M pairing unions separation infinite hAlphabet).graph_isFunc _ _

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u})

private theorem decodeWord {A f : ZFSet.{u}} (word : f ∈ M.finiteWords A) :
    ∃ xs : List (SetMembers A), finiteWordGraph (SetMembers.presentation A) xs = f := by
  obtain ⟨_, n, function⟩ := (M.mem_finiteWords A f).1 word
  obtain ⟨xs, _, equal⟩ := exists_finiteWordGraph (SetMembers.presentation A) function
  exact ⟨xs, equal⟩

theorem finiteWordAppend_empty {A f : ZFSet.{u}} (word : f ∈ M.finiteWords A) :
    ZFSet.pair (ZFSet.pair ∅ f) f ∈ M.finiteWordAppendGraph A ∧
      ZFSet.pair (ZFSet.pair f ∅) f ∈ M.finiteWordAppendGraph A := by
  obtain ⟨xs, rfl⟩ := M.decodeWord word
  let s := SetMembers.presentation A
  have emptyWord : (∅ : ZFSet.{u}) ∈ M.finiteWords A := by
    apply (M.mem_finiteWords A ∅).2
    refine ⟨M.empty_mem ⟨_, ((M.mem_finiteWords A _).1 word).1⟩, 0, ?_⟩
    simpa only [s, SetMembers.presentation, finiteWordGraph_nil, List.length_nil] using
      finiteWordGraph_function s ([] : List (SetMembers A))
  constructor
  · apply (M.pair_mem_finiteWordAppendGraph A _ _ _).2
    refine ⟨emptyWord, word, word, ?_⟩
    simpa only [s, SetMembers.presentation, finiteWordGraph_nil, List.nil_append] using
      finiteWordGraph_append_code s [] xs
  · apply (M.pair_mem_finiteWordAppendGraph A _ _ _).2
    refine ⟨word, emptyWord, word, ?_⟩
    simpa only [s, SetMembers.presentation, finiteWordGraph_nil, List.append_nil] using
      finiteWordGraph_append_code s xs []

theorem finiteWordAppend_assoc {A f g h fg gh left right : ZFSet.{u}}
    (first : ZFSet.pair (ZFSet.pair f g) fg ∈ M.finiteWordAppendGraph A)
    (second : ZFSet.pair (ZFSet.pair g h) gh ∈ M.finiteWordAppendGraph A)
    (leftEntry : ZFSet.pair (ZFSet.pair fg h) left ∈ M.finiteWordAppendGraph A)
    (rightEntry : ZFSet.pair (ZFSet.pair f gh) right ∈ M.finiteWordAppendGraph A) :
    left = right := by
  obtain ⟨xs, rfl⟩ := M.decodeWord ((M.pair_mem_finiteWordAppendGraph A _ _ _).1 first).1
  obtain ⟨ys, rfl⟩ := M.decodeWord ((M.pair_mem_finiteWordAppendGraph A _ _ _).1 first).2.1
  obtain ⟨zs, rfl⟩ := M.decodeWord ((M.pair_mem_finiteWordAppendGraph A _ _ _).1 second).2.1
  let s := SetMembers.presentation A
  have eqFirst := (finiteWordAppendCode_iff s xs ys fg).1
    ((M.pair_mem_finiteWordAppendGraph A _ _ _).1 first).2.2.2
  have eqSecond := (finiteWordAppendCode_iff s ys zs gh).1
    ((M.pair_mem_finiteWordAppendGraph A _ _ _).1 second).2.2.2
  subst fg gh
  have eqLeft := (finiteWordAppendCode_iff s (xs ++ ys) zs left).1
    ((M.pair_mem_finiteWordAppendGraph A _ _ _).1 leftEntry).2.2.2
  have eqRight := (finiteWordAppendCode_iff s xs (ys ++ zs) right).1
    ((M.pair_mem_finiteWordAppendGraph A _ _ _).1 rightEntry).2.2.2
  rw [List.append_assoc] at eqLeft
  exact eqLeft.trans eqRight.symm

theorem finiteWordReverse_involution {A f g : ZFSet.{u}}
    (entry : ZFSet.pair f g ∈ M.finiteWordReverseGraph A) :
    ZFSet.pair g f ∈ M.finiteWordReverseGraph A := by
  have members := (M.pair_mem_finiteWordReverseGraph A _ _).1 entry
  obtain ⟨xs, rfl⟩ := M.decodeWord members.1
  let s := SetMembers.presentation A
  have equal := (finiteWordReverseCode_iff s xs g).1 members.2.2
  subst g
  apply (M.pair_mem_finiteWordReverseGraph A _ _).2
  refine ⟨members.2.1, members.1, ?_⟩
  simpa only [s, SetMembers.presentation, List.reverse_reverse] using
    finiteWordGraph_reverse_code s xs.reverse

theorem finiteWordReverse_append {A f g fg rf rg result : ZFSet.{u}}
    (append : ZFSet.pair (ZFSet.pair f g) fg ∈ M.finiteWordAppendGraph A)
    (first : ZFSet.pair f rf ∈ M.finiteWordReverseGraph A)
    (second : ZFSet.pair g rg ∈ M.finiteWordReverseGraph A)
    (swapped : ZFSet.pair (ZFSet.pair rg rf) result ∈ M.finiteWordAppendGraph A) :
    ZFSet.pair fg result ∈ M.finiteWordReverseGraph A := by
  have members := (M.pair_mem_finiteWordAppendGraph A _ _ _).1 append
  have resultMember := ((M.pair_mem_finiteWordAppendGraph A _ _ _).1 swapped).2.2.1
  obtain ⟨xs, rfl⟩ := M.decodeWord members.1
  obtain ⟨ys, rfl⟩ := M.decodeWord members.2.1
  let s := SetMembers.presentation A
  have eqAppend := (finiteWordAppendCode_iff s xs ys fg).1 members.2.2.2
  have eqFirst := (finiteWordReverseCode_iff s xs rf).1
    ((M.pair_mem_finiteWordReverseGraph A _ _).1 first).2.2
  have eqSecond := (finiteWordReverseCode_iff s ys rg).1
    ((M.pair_mem_finiteWordReverseGraph A _ _).1 second).2.2
  subst fg rf rg
  have eqResult := (finiteWordAppendCode_iff s ys.reverse xs.reverse result).1
    ((M.pair_mem_finiteWordAppendGraph A _ _ _).1 swapped).2.2.2
  subst result
  apply (M.pair_mem_finiteWordReverseGraph A _ _).2
  refine ⟨members.2.2.1, resultMember, ?_⟩
  simpa only [s, SetMembers.presentation, List.reverse_append] using
    finiteWordGraph_reverse_code s (xs ++ ys)

theorem finiteWordLength_append {A f g h n k l : ZFSet.{u}}
    (append : ZFSet.pair (ZFSet.pair f g) h ∈ M.finiteWordAppendGraph A)
    (first : ZFSet.pair f n ∈ M.finiteWordLengthGraph A)
    (second : ZFSet.pair g k ∈ M.finiteWordLengthGraph A)
    (result : ZFSet.pair h l ∈ M.finiteWordLengthGraph A) :
    ZFSet.pair (ZFSet.pair n k) l ∈ natAddGraph := by
  have members := (M.pair_mem_finiteWordAppendGraph A _ _ _).1 append
  obtain ⟨xs, rfl⟩ := M.decodeWord members.1
  obtain ⟨ys, rfl⟩ := M.decodeWord members.2.1
  let s := SetMembers.presentation A
  have eqAppend := (finiteWordAppendCode_iff s xs ys h).1 members.2.2.2
  subst h
  have eqFirst := (M.pair_mem_finiteWordLengthGraph_word s xs
    ((M.mem_finiteWords A _).1 members.1).1 n).1 first
  have eqSecond := (M.pair_mem_finiteWordLengthGraph_word s ys
    ((M.mem_finiteWords A _).1 members.2.1).1 k).1 second
  have eqResult := (M.pair_mem_finiteWordLengthGraph_word s (xs ++ ys)
    ((M.mem_finiteWords A _).1 members.2.2.1).1 l).1 result
  rw [eqFirst, eqSecond, eqResult]
  exact (pair_mem_natAddGraph xs.length ys.length (xs ++ ys).length).2 List.length_append

theorem finiteWordLength_reverse {A f g n : ZFSet.{u}}
    (reverse : ZFSet.pair f g ∈ M.finiteWordReverseGraph A)
    (length : ZFSet.pair f n ∈ M.finiteWordLengthGraph A) :
    ZFSet.pair g n ∈ M.finiteWordLengthGraph A := by
  have members := (M.pair_mem_finiteWordReverseGraph A _ _).1 reverse
  obtain ⟨xs, rfl⟩ := M.decodeWord members.1
  let s := SetMembers.presentation A
  have eqReverse := (finiteWordReverseCode_iff s xs g).1 members.2.2
  subst g
  have eqLength := (M.pair_mem_finiteWordLengthGraph_word s xs
    ((M.mem_finiteWords A _).1 members.1).1 n).1 length
  apply (M.pair_mem_finiteWordLengthGraph_word s xs.reverse
    ((M.mem_finiteWords A _).1 members.2.1).1 n).2
  simpa only [List.length_reverse] using eqLength

end PartitionPilot.Forcing.TransitiveGround

end OAI
