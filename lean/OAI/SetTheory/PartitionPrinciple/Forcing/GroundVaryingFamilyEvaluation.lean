import OAI.SetTheory.PartitionPrinciple.Definability.BatchGraphSetFormulas
import OAI.SetTheory.PartitionPrinciple.Definability.GroundFunctionRangeFamilies

namespace OAI

namespace PartitionPilot.Forcing

section

universe u

def familyEvaluationGraph (K P L V Ss Es : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ k ∈ K, ∃ S ∈ V, ∃ e ∈ P, ∃ y ∈ L,
    z = ZFSet.pair k y ∧ ZFSet.pair k S ∈ Ss ∧
      ZFSet.pair k e ∈ Es ∧ ZFSet.pair e y ∈ S) (ZFSet.prod K L)

theorem pair_mem_familyEvaluationGraph (K P L V Ss Es k y : ZFSet.{u}) :
    ZFSet.pair k y ∈ familyEvaluationGraph K P L V Ss Es ↔
      k ∈ K ∧ y ∈ L ∧ ∃ S ∈ V, ∃ e ∈ P,
        ZFSet.pair k S ∈ Ss ∧ ZFSet.pair k e ∈ Es ∧ ZFSet.pair e y ∈ S := by
  rw [familyEvaluationGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hk, hy⟩, k', _, S, hS, e, he, y', _, eq, ks, ke, ey⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hk, hy, S, hS, e, he, ks, ke, ey⟩
  · rintro ⟨hk, hy, S, hS, e, he, ks, ke, ey⟩
    exact ⟨⟨hk, hy⟩, k, hk, S, hS, e, he, y, hy, rfl, ks, ke, ey⟩

theorem familyEvaluationGraph_entry_iff {K P L V Ss Es k S e y : ZFSet.{u}}
    (functions : ZFSet.IsFunc K V Ss) (arguments : ZFSet.IsFunc K P Es)
    (ks : ZFSet.pair k S ∈ Ss) (ke : ZFSet.pair k e ∈ Es) :
    ZFSet.pair k y ∈ familyEvaluationGraph K P L V Ss Es ↔
      y ∈ L ∧ ZFSet.pair e y ∈ S := by
  rw [pair_mem_familyEvaluationGraph]
  constructor
  · rintro ⟨_, hy, S', _, e', _, ks', ke', entry⟩
    have eqS := (show FunctionGraphOn K Ss from ⟨V, functions⟩).unique ks' ks
    have eqE := (show FunctionGraphOn K Es from ⟨P, arguments⟩).unique ke' ke
    exact ⟨hy, eqE ▸ eqS ▸ entry⟩
  · rintro ⟨hy, entry⟩
    have hs := ZFSet.pair_mem_prod.1 (functions.1 ks)
    have he := ZFSet.pair_mem_prod.1 (arguments.1 ke)
    exact ⟨hs.1, hy, S, hs.2, e, he.2, ks, ke, entry⟩

theorem familyEvaluationGraph_function {K P L V Ss Es : ZFSet.{u}}
    (functions : ZFSet.IsFunc K V Ss) (arguments : ZFSet.IsFunc K P Es)
    (valid : ∀ k S, ZFSet.pair k S ∈ Ss → ZFSet.IsFunc P L S) :
    ZFSet.IsFunc K L (familyEvaluationGraph K P L V Ss Es) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro k hk
  obtain ⟨S, ks, _⟩ := functions.2 k hk
  obtain ⟨e, ke, _⟩ := arguments.2 k hk
  have function := valid k S ks
  obtain ⟨y, ey, unique⟩ := function.2 e (ZFSet.pair_mem_prod.1 (arguments.1 ke)).2
  refine ⟨y, (familyEvaluationGraph_entry_iff functions arguments ks ke).2
    ⟨(ZFSet.pair_mem_prod.1 (function.1 ey)).2, ey⟩, ?_⟩
  intro z hz
  exact unique z ((familyEvaluationGraph_entry_iff functions arguments ks ke).1 hz).2

namespace BoundedFormula

open SetFormula

def familyEvaluationEntryFormula {n} (z k p l v ss es : Fin n) : BoundedFormula n :=
  exMem k (exMem v.succ (exMem p.succ.succ (exMem l.succ.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ.succ 3 0)
      (.conj (pairMembershipFormula 3 2 ss.succ.succ.succ.succ)
        (.conj (pairMembershipFormula 3 1 es.succ.succ.succ.succ)
          (pairMembershipFormula 1 0 2)))))))

theorem truth_familyEvaluationEntryFormula {n} (z k p l v ss es : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (familyEvaluationEntryFormula z k p l v ss es) env ↔
      ∃ i ∈ env k, ∃ S ∈ env v, ∃ e ∈ env p, ∃ y ∈ env l,
        env z = ZFSet.pair i y ∧ ZFSet.pair i S ∈ env ss ∧
          ZFSet.pair i e ∈ env es ∧ ZFSet.pair e y ∈ S := by
  simp only [familyEvaluationEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem familyEvaluationGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {K P L V Ss Es : ZFSet.{u}} (hK : K ∈ M.sets) (hP : P ∈ M.sets)
    (hL : L ∈ M.sets) (hV : V ∈ M.sets) (hSs : Ss ∈ M.sets) (hEs : Es ∈ M.sets) :
    familyEvaluationGraph K P L V Ss Es ∈ M.sets := by
  let params := extend K (extend P (extend L (extend V (extend Ss (extend Es Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.familyEvaluationEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hK (Fin.cases hP (Fin.cases hL (Fin.cases hV (Fin.cases hSs
      (Fin.cases hEs (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hK hL)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.familyEvaluationEntryFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod K L) = familyEvaluationGraph K P L V Ss Es := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, familyEvaluationGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_familyEvaluationEntryFormula 0 1 2 3 4 5 6 _)
  exact equal ▸ selected

end TransitiveGround

end

section
open SetFormula
universe u

namespace SetFormula

def familyEvaluationSetFormula {n} (output K P L V Ss Es : Fin n) : SetFormula n :=
  exactSetFormula output
    (BoundedFormula.familyEvaluationEntryFormula
      0 K.succ P.succ L.succ V.succ Ss.succ Es.succ).toFormula

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_familyEvaluationSetFormula {n} (output K P L V Ss Es : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (familyEvaluationSetFormula output K P L V Ss Es) env ↔
      env output = familyEvaluationGraph (env K) (env P) (env L) (env V) (env Ss) (env Es) := by
  apply M.realize_exactBoundedSetFormula output _ env members
    (M.familyEvaluationGraph_mem pairing unions powers separation
      (members K) (members P) (members L) (members V) (members Ss) (members Es))
  intro z
  rw [BoundedFormula.truth_familyEvaluationEntryFormula]
  change (∃ i ∈ env K, ∃ S ∈ env V, ∃ e ∈ env P, ∃ y ∈ env L,
    z = ZFSet.pair i y ∧ ZFSet.pair i S ∈ env Ss ∧
      ZFSet.pair i e ∈ env Es ∧ ZFSet.pair e y ∈ S) ↔ _
  rw [familyEvaluationGraph, ZFSet.mem_sep]
  constructor
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨i, hi, _, _, _, _, y, hy, rfl, _⟩ := witness
    exact ZFSet.pair_mem_prod.2 ⟨hi, hy⟩
  · exact And.right

noncomputable def definable_familyEvaluation : GroundDefinableFunction M
    (fun env : Fin 6 → ZFSet.{u} =>
      familyEvaluationGraph (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) where
  formula := familyEvaluationSetFormula 0 1 2 3 4 5 6
  closed := fun _ members => M.familyEvaluationGraph_mem pairing unions powers separation
    (members 0) (members 1) (members 2) (members 3) (members 4) (members 5)
  correct := fun env members z hz => M.realize_familyEvaluationSetFormula
    pairing unions powers separation 0 1 2 3 4 5 6 (extend z env) (Fin.cases hz members)

end TransitiveGround
end

open SetFormula
universe u v
variable {I : Type v} [Small.{u} I]

theorem TransitiveGround.familyCodeGraph_evaluation_ground (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (key arguments graphs values : I → ZFSet.{u}) (injective : Function.Injective key)
    (domain : ZFSet.range key ∈ M.sets)
    (argumentsGround : familyCodeGraph key arguments ∈ M.sets)
    (graphsGround : familyCodeGraph key graphs ∈ M.sets)
    (lookup : ∀ i y, ZFSet.pair (arguments i) y ∈ graphs i ↔ y = values i) :
    familyCodeGraph key values ∈ M.sets := by
  let Ss := familyCodeGraph key graphs
  let Es := familyCodeGraph key arguments
  let P := ZFSet.sUnion (ZFSet.sUnion Es)
  let V := ZFSet.sUnion (ZFSet.sUnion Ss)
  let L := ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion V))
  let evaluated := familyEvaluationGraph (ZFSet.range key) P L V Ss Es
  have hP : P ∈ M.sets := M.union_mem unions (M.union_mem unions argumentsGround)
  have hV : V ∈ M.sets := M.union_mem unions (M.union_mem unions graphsGround)
  have hL : L ∈ M.sets := M.union_mem unions (M.union_mem unions (M.union_mem unions hV))
  have ground : evaluated ∈ M.sets :=
    M.familyEvaluationGraph_mem pairing unions powers separation domain hP hL hV graphsGround argumentsGround
  have graphFunction : ZFSet.IsFunc (ZFSet.range key) V Ss :=
    (familyCodeGraph_function key graphs injective).to_isFunc
  have argumentFunction : ZFSet.IsFunc (ZFSet.range key) P Es :=
    (familyCodeGraph_function key arguments injective).to_isFunc
  have valueBound (i : I) : values i ∈ L := by
    have stored : graphs i ∈ V :=
      pair_second_mem_doubleUnion ((pair_mem_familyCodeGraph key graphs injective i _).2 rfl)
    have entry : ZFSet.pair (arguments i) (values i) ∈ ZFSet.sUnion V :=
      ZFSet.mem_sUnion.2 ⟨graphs i, stored, (lookup i _).2 rfl⟩
    exact pair_second_mem_doubleUnion entry
  have entries (i : I) (y : ZFSet.{u}) : ZFSet.pair (key i) y ∈ evaluated ↔ y = values i := by
    rw [familyEvaluationGraph_entry_iff graphFunction argumentFunction
      ((pair_mem_familyCodeGraph key graphs injective i _).2 rfl)
      ((pair_mem_familyCodeGraph key arguments injective i _).2 rfl), lookup i y]
    exact ⟨And.right, fun equal => ⟨equal.symm ▸ valueBound i, equal⟩⟩
  have function : FunctionGraphOn (ZFSet.range key) evaluated := by
    refine ⟨L, fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
    intro x hx
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
    exact ⟨values i, (entries i _).2 rfl, fun y hy => (entries i y).1 hy⟩
  exact familyCodeGraph_ground_of_entries ground function key values rfl (fun i => (entries i _).2 rfl)

theorem familyCodeGraph_evaluation_rank_le (key arguments graphs values : I → ZFSet.{u})
    (entries : ∀ i, ZFSet.pair (arguments i) (values i) ∈ graphs i) :
    ZFSet.rank (familyCodeGraph key values) ≤ ZFSet.rank (familyCodeGraph key graphs) := by
  apply familyCodeGraph_rank_mono
  intro i
  exact (ZFSet.rank_lt_of_mem (pair_second_mem_doubleUnion (entries i))).le.trans
    ((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _))

end PartitionPilot.Forcing

end OAI
