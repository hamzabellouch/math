import OAI.SetTheory.PartitionPrinciple.Definability.GroundFlatCopyGraphs

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.FunctionGraphOn

universe u
variable {I f : ZFSet.{u}}

noncomputable def value (h : FunctionGraphOn I f) (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} :=
  Classical.choose (h.total i.property)

theorem value_entry (h : FunctionGraphOn I f) (i : {i : ZFSet.{u} // i ∈ I}) :
    ZFSet.pair i.val (h.value i) ∈ f :=
  Classical.choose_spec (h.total i.property)

theorem value_eq_of_entry (h : FunctionGraphOn I f) (i : {i : ZFSet.{u} // i ∈ I})
    {y : ZFSet.{u}} (entry : ZFSet.pair i.val y ∈ f) : h.value i = y :=
  h.unique (h.value_entry i) entry

theorem value_mem_doubleUnion (h : FunctionGraphOn I f) (i : {i : ZFSet.{u} // i ∈ I}) :
    h.value i ∈ ⋃₀ ⋃₀ f :=
  pair_second_mem_doubleUnion (h.value_entry i)

theorem value_mem (h : FunctionGraphOn I f) (M : TransitiveGround.{u})
    (hf : f ∈ M.sets) (i : {i : ZFSet.{u} // i ∈ I}) : h.value i ∈ M.sets :=
  M.pair_right (M.transitive hf (h.value_entry i))





noncomputable def totalValue (function : FunctionGraphOn I f) (i : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if hi : i ∈ I then function.value ⟨i, hi⟩ else ∅

theorem totalValue_entry (function : FunctionGraphOn I f) {i : ZFSet.{u}} (hi : i ∈ I) :
    ZFSet.pair i (function.totalValue i) ∈ f := by
  rw [totalValue, dite_eq_left hi]
  exact function.value_entry ⟨i, hi⟩

theorem totalValue_eq_of_entry (function : FunctionGraphOn I f) {i y : ZFSet.{u}}
    (entry : ZFSet.pair i y ∈ f) : function.totalValue i = y :=
  function.unique (function.totalValue_entry (function.pair_source entry)) entry

theorem totalValue_outside (function : FunctionGraphOn I f) {i : ZFSet.{u}} (hi : i ∉ I) :
    function.totalValue i = ∅ := by rw [totalValue, dite_eq_right hi]

theorem totalValue_ground (function : FunctionGraphOn I f) (M : TransitiveGround.{u})
    (hf : f ∈ M.sets) (i : ZFSet.{u}) : function.totalValue i ∈ M.sets := by
  classical
  by_cases hi : i ∈ I
  · exact M.pair_right (M.transitive hf (function.totalValue_entry hi))
  · rw [function.totalValue_outside hi]
    exact M.empty_mem ⟨f, hf⟩

end PartitionPilot.Forcing.FunctionGraphOn



namespace PartitionPilot.Forcing

open SetRealization
universe u

noncomputable def productFirst (A B : ZFSet.{u}) : ZFSet.{u} :=
  ((SetMembers.presentation A).product (SetMembers.presentation B)).graph (SetMembers.presentation A) Prod.fst

noncomputable def productSecond (A B : ZFSet.{u}) : ZFSet.{u} :=
  ((SetMembers.presentation A).product (SetMembers.presentation B)).graph (SetMembers.presentation B) Prod.snd

theorem mem_productFirst (A B z : ZFSet.{u}) : z ∈ productFirst A B ↔
    ∃ x ∈ A, ∃ y ∈ B, z = ZFSet.pair (ZFSet.pair x y) x := by
  rw [productFirst, Presentation.mem_graph]
  constructor
  · rintro ⟨⟨x, y⟩, eq⟩
    exact ⟨SetMembers.raw x, SetMembers.raw_mem x, SetMembers.raw y, SetMembers.raw_mem y, eq.symm⟩
  · rintro ⟨x, hx, y, hy, eq⟩
    refine ⟨(SetMembers.ofMem x hx, SetMembers.ofMem y hy), ?_⟩
    change ZFSet.pair (ZFSet.pair (SetMembers.raw _) (SetMembers.raw _)) (SetMembers.raw _) = z
    rw [SetMembers.raw_ofMem, SetMembers.raw_ofMem]
    exact eq.symm

theorem mem_productSecond (A B z : ZFSet.{u}) : z ∈ productSecond A B ↔
    ∃ x ∈ A, ∃ y ∈ B, z = ZFSet.pair (ZFSet.pair x y) y := by
  rw [productSecond, Presentation.mem_graph]
  constructor
  · rintro ⟨⟨x, y⟩, eq⟩
    exact ⟨SetMembers.raw x, SetMembers.raw_mem x, SetMembers.raw y, SetMembers.raw_mem y, eq.symm⟩
  · rintro ⟨x, hx, y, hy, eq⟩
    refine ⟨(SetMembers.ofMem x hx, SetMembers.ofMem y hy), ?_⟩
    change ZFSet.pair (ZFSet.pair (SetMembers.raw _) (SetMembers.raw _)) (SetMembers.raw _) = z
    rw [SetMembers.raw_ofMem, SetMembers.raw_ofMem]
    exact eq.symm

theorem productFirst_function (A B : ZFSet.{u}) : ZFSet.IsFunc (ZFSet.prod A B) A (productFirst A B) :=
  ((SetMembers.presentation A).product (SetMembers.presentation B)).graph_isFunc (SetMembers.presentation A) Prod.fst

theorem productSecond_function (A B : ZFSet.{u}) : ZFSet.IsFunc (ZFSet.prod A B) B (productSecond A B) :=
  ((SetMembers.presentation A).product (SetMembers.presentation B)).graph_isFunc (SetMembers.presentation B) Prod.snd

namespace BoundedFormula

open SetFormula

def productFirstEntryFormula {n} (z a b : Fin n) : BoundedFormula n :=
  exMem a (exMem b.succ (orderedTripleFormula z.succ.succ 1 0 1))

def productSecondEntryFormula {n} (z a b : Fin n) : BoundedFormula n :=
  exMem a (exMem b.succ (orderedTripleFormula z.succ.succ 1 0 0))

theorem truth_productFirstEntryFormula {n} (z a b : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (productFirstEntryFormula z a b) env ↔ env z ∈ productFirst (env a) (env b) := by
  simp only [productFirstEntryFormula, truth_exMem, truth_orderedTripleFormula, mem_productFirst]
  rfl

theorem truth_productSecondEntryFormula {n} (z a b : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (productSecondEntryFormula z a b) env ↔ env z ∈ productSecond (env a) (env b) := by
  simp only [productSecondEntryFormula, truth_exMem, truth_orderedTripleFormula, mem_productSecond]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem productFirst_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) : productFirst A B ∈ M.sets := by
  let params := extend A (extend B Fin.elim0)
  have selected := M.bounded_separation_mem separation (BoundedFormula.productFirstEntryFormula 0 1 2)
    params (Fin.cases hA (Fin.cases hB (fun i => Fin.elim0 i)))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hA hB) hA)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.productFirstEntryFormula 0 1 2)
      (extend z params)) (ZFSet.prod (ZFSet.prod A B) A) = productFirst A B := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_productFirstEntryFormula]
    exact ⟨And.right, fun hz => ⟨(productFirst_function A B).1 hz, hz⟩⟩
  exact eq ▸ selected

theorem productSecond_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) : productSecond A B ∈ M.sets := by
  let params := extend A (extend B Fin.elim0)
  have selected := M.bounded_separation_mem separation (BoundedFormula.productSecondEntryFormula 0 1 2)
    params (Fin.cases hA (Fin.cases hB (fun i => Fin.elim0 i)))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hA hB) hB)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.productSecondEntryFormula 0 1 2)
      (extend z params)) (ZFSet.prod (ZFSet.prod A B) B) = productSecond A B := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_productSecondEntryFormula]
    exact ⟨And.right, fun hz => ⟨(productSecond_function A B).1 hz, hz⟩⟩
  exact eq ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

universe u

theorem relationCompose_domain_eq {U B D L ell f : ZFSet.{u}}
    (subset : U ⊆ B) (shape : ell ⊆ ZFSet.prod U D) :
    relationCompose B D L ell f = relationCompose U D L ell f := by
  apply ZFSet.ext
  intro z
  rw [mem_relationCompose, mem_relationCompose]
  constructor
  · rintro ⟨x, _, y, hy, w, hw, equal, first, second⟩
    exact ⟨x, (ZFSet.pair_mem_prod.1 (shape first)).1, y, hy, w, hw, equal, first, second⟩
  · rintro ⟨x, hx, y, hy, w, hw, equal, first, second⟩
    exact ⟨x, subset hx, y, hy, w, hw, equal, first, second⟩

noncomputable def pairCompositionFamily (K I J B D L Es Ss W : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ j ∈ J, ∃ ell ∈ ⋃₀ ⋃₀ Es, ∃ f ∈ ⋃₀ ⋃₀ Ss,
    ∃ c ∈ W, z = ZFSet.pair (ZFSet.pair i j) c ∧ ZFSet.pair i j ∈ K ∧
      ZFSet.pair j ell ∈ Es ∧ ZFSet.pair i f ∈ Ss ∧ c = relationCompose B D L ell f)
    (ZFSet.prod K W)

theorem pair_mem_pairCompositionFamily (K I J B D L Es Ss W i j c : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i j) c ∈ pairCompositionFamily K I J B D L Es Ss W ↔
      ZFSet.pair i j ∈ K ∧ i ∈ I ∧ j ∈ J ∧ c ∈ W ∧
        ∃ ell f, ZFSet.pair j ell ∈ Es ∧ ZFSet.pair i f ∈ Ss ∧ c = relationCompose B D L ell f := by
  constructor
  · intro entry
    obtain ⟨_, a, ha, b, hb, ell, _, f, _, c', hc', equal, hk, first, second, output⟩ :=
      ZFSet.mem_sep.1 entry
    obtain ⟨indices, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 indices
    exact ⟨hk, ha, hb, hc', ell, f, first, second, output⟩
  · rintro ⟨hk, hi, hj, hc, ell, f, first, second, output⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hk, hc⟩,
      i, hi, j, hj, ell, pair_second_mem_doubleUnion first,
      f, pair_second_mem_doubleUnion second, c, hc, rfl, hk, first, second, output⟩

theorem pairCompositionFamily_entry_iff {K I J B D L Es Ss W i j ell f c : ZFSet.{u}}
    (bases : FunctionGraphOn J Es) (maps : FunctionGraphOn I Ss)
    (first : ZFSet.pair j ell ∈ Es) (second : ZFSet.pair i f ∈ Ss) :
    ZFSet.pair (ZFSet.pair i j) c ∈ pairCompositionFamily K I J B D L Es Ss W ↔
      ZFSet.pair i j ∈ K ∧ c ∈ W ∧ c = relationCompose B D L ell f := by
  rw [pair_mem_pairCompositionFamily]
  constructor
  · rintro ⟨hk, _, _, hc, ell', f', left, right, equal⟩
    have ellEq := bases.unique left first
    have fEq := maps.unique right second
    exact ⟨hk, hc, ellEq ▸ fEq ▸ equal⟩
  · rintro ⟨hk, hc, equal⟩
    exact ⟨hk, maps.pair_source second, bases.pair_source first, hc, ell, f, first, second, equal⟩

theorem pairCompositionFamily_function {K I J B D L Es Ss W : ZFSet.{u}}
    (bases : FunctionGraphOn J Es) (maps : FunctionGraphOn I Ss) (subset : K ⊆ ZFSet.prod I J)
    (bounded : ∀ i ∈ I, ∀ j ∈ J, ∀ ell f, ZFSet.pair j ell ∈ Es → ZFSet.pair i f ∈ Ss →
      relationCompose B D L ell f ∈ W) :
    ZFSet.IsFunc K W (pairCompositionFamily K I J B D L Es Ss W) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro k hk
  obtain ⟨i, hi, j, hj, rfl⟩ := ZFSet.mem_prod.1 (subset hk)
  obtain ⟨ell, first⟩ := bases.total hj
  obtain ⟨f, second⟩ := maps.total hi
  refine ⟨relationCompose B D L ell f,
    (pairCompositionFamily_entry_iff bases maps first second).2
      ⟨hk, bounded i hi j hj ell f first second, rfl⟩, ?_⟩
  intro c entry
  exact ((pairCompositionFamily_entry_iff bases maps first second).1 entry).2.2

namespace BoundedFormula

open SetFormula

def compositionGraphFormula {n} (f B D L ell s : Fin n) : BoundedFormula n :=
  .conj (.allMem f (composeEntryFormula 0 B.succ D.succ L.succ ell.succ s.succ))
    (.allMem B (.allMem D.succ (.allMem L.succ.succ (imp
      (.conj (pairMembershipFormula 2 1 ell.succ.succ.succ)
        (pairMembershipFormula 1 0 s.succ.succ.succ)) (pairMembershipFormula 2 0 f.succ.succ.succ)))))

theorem truth_compositionGraphFormula {n} (f B D L ell s : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (compositionGraphFormula f B D L ell s) env ↔
      env f = relationCompose (env B) (env D) (env L) (env ell) (env s) := by
  simp only [compositionGraphFormula, Truth, truth_composeEntryFormula, truth_imp,
    truth_pairMembershipFormula]
  constructor
  · rintro ⟨sound, complete⟩
    apply ZFSet.ext
    intro z
    rw [mem_relationCompose]
    refine ⟨sound z, ?_⟩
    rintro ⟨x, hx, y, hy, w, hw, rfl, first, second⟩
    exact complete x hx y hy w hw ⟨first, second⟩
  · intro equal
    refine ⟨fun z hz => (mem_relationCompose _ _ _ _ _ z).1 (equal ▸ hz), ?_⟩
    intro x hx y hy w hw entries
    change ZFSet.pair x w ∈ env f
    rw [equal]
    exact (pair_mem_relationCompose _ _ _ _ _ x w).2 ⟨hx, hw, y, hy, entries⟩

def pairCompositionEntryFormula {n} (z K I J B D L Es Ss W U V : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ
  exMem I (exMem J.succ (exMem U.succ.succ (exMem V.succ.succ.succ (exMem W.succ.succ.succ.succ
    (.conj (orderedTripleFormula (lift z) 4 3 0)
      (.conj (pairMembershipFormula 4 3 (lift K))
        (.conj (pairMembershipFormula 3 2 (lift Es))
          (.conj (pairMembershipFormula 4 1 (lift Ss))
            (compositionGraphFormula 0 (lift B) (lift D) (lift L) 2 1)))))))))

theorem truth_pairCompositionEntryFormula {n} (z K I J B D L Es Ss W U V : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (pairCompositionEntryFormula z K I J B D L Es Ss W U V) env ↔
      ∃ i ∈ env I, ∃ j ∈ env J, ∃ ell ∈ env U, ∃ f ∈ env V, ∃ c ∈ env W,
        env z = ZFSet.pair (ZFSet.pair i j) c ∧ ZFSet.pair i j ∈ env K ∧
          ZFSet.pair j ell ∈ env Es ∧ ZFSet.pair i f ∈ env Ss ∧
            c = relationCompose (env B) (env D) (env L) ell f := by
  simp only [pairCompositionEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_pairMembershipFormula, truth_compositionGraphFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

universe u v w

noncomputable def literalTaskCode (a c ell e F label : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair a (ZFSet.pair c (ZFSet.pair ell (ZFSet.pair e (ZFSet.pair F label))))

noncomputable def literalTaskBound (P R U Labels : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod P (ZFSet.prod P (ZFSet.prod R (ZFSet.prod P (ZFSet.prod U Labels))))

theorem literalTaskCode_inj {a c ell e F label a' c' ell' e' F' label' : ZFSet.{u}} :
    literalTaskCode a c ell e F label = literalTaskCode a' c' ell' e' F' label' ↔
      a = a' ∧ c = c' ∧ ell = ell' ∧ e = e' ∧ F = F' ∧ label = label' := by
  simp only [literalTaskCode, ZFSet.pair_inj]

theorem literalTaskCode_mem_bound (P R U Labels a c ell e F label : ZFSet.{u}) :
    literalTaskCode a c ell e F label ∈ literalTaskBound P R U Labels ↔
      a ∈ P ∧ c ∈ P ∧ ell ∈ R ∧ e ∈ P ∧ F ∈ U ∧ label ∈ Labels := by
  simp only [literalTaskCode, literalTaskBound, ZFSet.pair_mem_prod]

theorem mem_literalTaskBound (P R U Labels z : ZFSet.{u}) :
    z ∈ literalTaskBound P R U Labels ↔
      ∃ a ∈ P, ∃ c ∈ P, ∃ ell ∈ R, ∃ e ∈ P, ∃ F ∈ U, ∃ label ∈ Labels,
        z = literalTaskCode a c ell e F label := by
  constructor
  · intro hz
    obtain ⟨a, ha, rest1, hrest1, rfl⟩ := ZFSet.mem_prod.1 hz
    obtain ⟨c, hc, rest2, hrest2, rfl⟩ := ZFSet.mem_prod.1 hrest1
    obtain ⟨ell, hell, rest3, hrest3, rfl⟩ := ZFSet.mem_prod.1 hrest2
    obtain ⟨e, he, rest4, hrest4, rfl⟩ := ZFSet.mem_prod.1 hrest3
    obtain ⟨F, hF, label, hlabel, rfl⟩ := ZFSet.mem_prod.1 hrest4
    exact ⟨a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel, rfl⟩
  · rintro ⟨a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel, rfl⟩
    exact (literalTaskCode_mem_bound P R U Labels a c ell e F label).2
      ⟨ha, hc, hell, he, hF, hlabel⟩

def literalTaskField {α : Type v} (a c ell e F label : α) : Fin 6 → α :=
  Fin.cases a (Fin.cases c (Fin.cases ell (Fin.cases e (Fin.cases F (Fin.cases label Fin.elim0)))))

theorem literalTaskField_map {α : Type v} {β : Type w} (f : α → β)
    (a c ell e F label : α) (j : Fin 6) :
    f (literalTaskField a c ell e F label j) =
      literalTaskField (f a) (f c) (f ell) (f e) (f F) (f label) j := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (fun i => Fin.elim0 i)))))) j <;> rfl

def literalTaskFieldBound (P R U Labels : ZFSet.{u}) (j : Fin 6) : ZFSet.{u} :=
  literalTaskField P P R P U Labels j

theorem literalTaskField_mem {P R U Labels a c ell e F label : ZFSet.{u}}
    (ha : a ∈ P) (hc : c ∈ P) (hell : ell ∈ R) (he : e ∈ P) (hF : F ∈ U)
    (hlabel : label ∈ Labels) (j : Fin 6) :
    literalTaskField a c ell e F label j ∈ literalTaskFieldBound P R U Labels j := by
  exact Fin.cases ha (Fin.cases hc (Fin.cases hell (Fin.cases he
    (Fin.cases hF (Fin.cases hlabel (fun i => Fin.elim0 i)))))) j

noncomputable def literalTaskFieldGraph (I P R U Labels : ZFSet.{u}) (j : Fin 6) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ a ∈ P, ∃ c ∈ P, ∃ ell ∈ R, ∃ e ∈ P,
    ∃ F ∈ U, ∃ label ∈ Labels,
      z = ZFSet.pair i (literalTaskField a c ell e F label j) ∧
        i = literalTaskCode a c ell e F label)
    (ZFSet.prod I (literalTaskFieldBound P R U Labels j))

theorem mem_literalTaskFieldGraph (I P R U Labels z : ZFSet.{u}) (j : Fin 6) :
    z ∈ literalTaskFieldGraph I P R U Labels j ↔
      ∃ i ∈ I, ∃ a ∈ P, ∃ c ∈ P, ∃ ell ∈ R, ∃ e ∈ P, ∃ F ∈ U, ∃ label ∈ Labels,
        z = ZFSet.pair i (literalTaskField a c ell e F label j) ∧
          i = literalTaskCode a c ell e F label := by
  rw [literalTaskFieldGraph, ZFSet.mem_sep]
  refine ⟨And.right, ?_⟩
  rintro ⟨i, hi, a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel, equal, code⟩
  exact ⟨equal.symm ▸ ZFSet.pair_mem_prod.2
    ⟨hi, literalTaskField_mem ha hc hell he hF hlabel j⟩,
    i, hi, a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel, equal, code⟩

theorem pair_mem_literalTaskFieldGraph (I P R U Labels i x : ZFSet.{u}) (j : Fin 6) :
    ZFSet.pair i x ∈ literalTaskFieldGraph I P R U Labels j ↔
      i ∈ I ∧ ∃ a ∈ P, ∃ c ∈ P, ∃ ell ∈ R, ∃ e ∈ P, ∃ F ∈ U, ∃ label ∈ Labels,
        i = literalTaskCode a c ell e F label ∧ x = literalTaskField a c ell e F label j := by
  rw [mem_literalTaskFieldGraph]
  constructor
  · rintro ⟨i', hi, a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel, equal, code⟩
    obtain ⟨same, value⟩ := ZFSet.pair_inj.1 equal
    exact ⟨same.symm ▸ hi, a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel,
      same.trans code, value⟩
  · rintro ⟨hi, a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel, code, value⟩
    exact ⟨i, hi, a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel,
      congrArg (ZFSet.pair i) value, code⟩

theorem literalTaskFieldGraph_entry_iff
    {I P R U Labels a c ell e F label x : ZFSet.{u}}
    (ha : a ∈ P) (hc : c ∈ P) (hell : ell ∈ R) (he : e ∈ P) (hF : F ∈ U)
    (hlabel : label ∈ Labels) (j : Fin 6) :
    ZFSet.pair (literalTaskCode a c ell e F label) x ∈ literalTaskFieldGraph I P R U Labels j ↔
      literalTaskCode a c ell e F label ∈ I ∧ x = literalTaskField a c ell e F label j := by
  rw [pair_mem_literalTaskFieldGraph]
  constructor
  · rintro ⟨hi, a', _, c', _, ell', _, e', _, F', _, label', _, equal, value⟩
    obtain ⟨sameA, sameC, sameEll, sameE, sameF, sameLabel⟩ := literalTaskCode_inj.1 equal
    subst a' c' ell' e' F' label'
    exact ⟨hi, value⟩
  · rintro ⟨hi, value⟩
    exact ⟨hi, a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel, rfl, value⟩

theorem literalTaskFieldGraph_function {I P R U Labels : ZFSet.{u}}
    (subset : I ⊆ literalTaskBound P R U Labels) (j : Fin 6) :
    ZFSet.IsFunc I (literalTaskFieldBound P R U Labels j) (literalTaskFieldGraph I P R U Labels j) := by
  refine ⟨fun _ h => (ZFSet.mem_sep.1 h).1, ?_⟩
  intro i hi
  obtain ⟨a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel, equal⟩ :=
    (mem_literalTaskBound P R U Labels i).1 (subset hi)
  subst i
  refine ⟨literalTaskField a c ell e F label j,
    (literalTaskFieldGraph_entry_iff ha hc hell he hF hlabel j).2 ⟨hi, rfl⟩, ?_⟩
  intro y entry
  exact ((literalTaskFieldGraph_entry_iff ha hc hell he hF hlabel j).1 entry).2

noncomputable abbrev literalTaskSourceGraph (I P R U Labels : ZFSet.{u}) :=
  literalTaskFieldGraph I P R U Labels 0
noncomputable abbrev literalTaskTargetGraph (I P R U Labels : ZFSet.{u}) :=
  literalTaskFieldGraph I P R U Labels 1
noncomputable abbrev literalTaskBaseGraph (I P R U Labels : ZFSet.{u}) :=
  literalTaskFieldGraph I P R U Labels 2
noncomputable abbrev literalTaskSeparatorGraph (I P R U Labels : ZFSet.{u}) :=
  literalTaskFieldGraph I P R U Labels 3
noncomputable abbrev literalTaskFilterGraph (I P R U Labels : ZFSet.{u}) :=
  literalTaskFieldGraph I P R U Labels 4
noncomputable abbrev literalTaskLabelGraph (I P R U Labels : ZFSet.{u}) :=
  literalTaskFieldGraph I P R U Labels 5

noncomputable def constantFamilyGraph (I x : ZFSet.{u}) : ZFSet.{u} := ZFSet.prod I {x}

theorem pair_mem_constantFamilyGraph (I x i y : ZFSet.{u}) :
    ZFSet.pair i y ∈ constantFamilyGraph I x ↔ i ∈ I ∧ y = x := by
  rw [constantFamilyGraph, ZFSet.pair_mem_prod, ZFSet.mem_singleton]

theorem constantFamilyGraph_function (I x : ZFSet.{u}) :
    ZFSet.IsFunc I {x} (constantFamilyGraph I x) := by
  refine ⟨fun _ h => h, ?_⟩
  intro i hi
  exact ⟨x, (pair_mem_constantFamilyGraph I x i x).2 ⟨hi, rfl⟩,
    fun y entry => ((pair_mem_constantFamilyGraph I x i y).1 entry).2⟩

namespace BoundedFormula

open SetFormula

def literalTaskFormula {n} (z a c ell e F label : Fin n) : BoundedFormula n :=
  let lift2 (j : Fin n) := j.succ.succ
  let lift4 (j : Fin n) := j.succ.succ.succ.succ
  let lift6 (j : Fin n) := j.succ.succ.succ.succ.succ.succ
  let lift8 (j : Fin n) := j.succ.succ.succ.succ.succ.succ.succ.succ
  exMem z (exMem 0 (.conj (orderedPairFormula (lift2 z) (lift2 a) 0)
    (exMem 0 (exMem 0 (.conj (orderedPairFormula 2 (lift4 c) 0)
      (exMem 0 (exMem 0 (.conj (orderedPairFormula 2 (lift6 ell) 0)
        (exMem 0 (exMem 0 (.conj (orderedPairFormula 2 (lift8 e) 0)
          (orderedPairFormula 0 (lift8 F) (lift8 label)))))))))))))

theorem truth_literalTaskFormula {n} (z a c ell e F label : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (literalTaskFormula z a c ell e F label) env ↔
      env z = literalTaskCode (env a) (env c) (env ell) (env e) (env F) (env label) := by
  simp only [literalTaskFormula, truth_exMem, Truth, truth_orderedPairFormula]
  change (∃ u ∈ env z, ∃ v ∈ u, env z = ZFSet.pair (env a) v ∧
    ∃ u' ∈ v, ∃ v' ∈ u', v = ZFSet.pair (env c) v' ∧
    ∃ u'' ∈ v', ∃ v'' ∈ u'', v' = ZFSet.pair (env ell) v'' ∧
    ∃ u''' ∈ v'', ∃ v''' ∈ u''', v'' = ZFSet.pair (env e) v''' ∧
      v''' = ZFSet.pair (env F) (env label)) ↔ _
  constructor
  · rintro ⟨_, _, v, _, outer, _, _, v', _, second, _, _, v'', _, third,
      _, _, v''', _, fourth, last⟩
    rw [outer, second, third, fourth, last]
    rfl
  · intro equal
    let v''' := ZFSet.pair (env F) (env label)
    let v'' := ZFSet.pair (env e) v'''
    let v' := ZFSet.pair (env ell) v''
    let v := ZFSet.pair (env c) v'
    have outer : env z = ZFSet.pair (env a) v := equal
    refine ⟨{env a, v}, ?_, v, ZFSet.mem_pair.2 (Or.inr rfl), outer,
      {env c, v'}, ZFSet.mem_pair.2 (Or.inr rfl), v', ZFSet.mem_pair.2 (Or.inr rfl), rfl,
      {env ell, v''}, ZFSet.mem_pair.2 (Or.inr rfl), v'', ZFSet.mem_pair.2 (Or.inr rfl), rfl,
      {env e, v'''}, ZFSet.mem_pair.2 (Or.inr rfl), v''', ZFSet.mem_pair.2 (Or.inr rfl), rfl, rfl⟩
    rw [outer]
    exact ZFSet.mem_pair.2 (Or.inr rfl)

def literalTaskFieldEntryFormula {n} (j : Fin 6) (z I P R U Labels : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ.succ
  exMem I (exMem P.succ (exMem P.succ.succ (exMem R.succ.succ.succ
    (exMem P.succ.succ.succ.succ (exMem U.succ.succ.succ.succ.succ
      (exMem Labels.succ.succ.succ.succ.succ.succ
        (.conj (orderedPairFormula (lift z) 6 (literalTaskField 5 4 3 2 1 0 j))
          (literalTaskFormula 6 5 4 3 2 1 0))))))))

theorem truth_literalTaskFieldEntryFormula {n} (j : Fin 6) (z I P R U Labels : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (literalTaskFieldEntryFormula j z I P R U Labels) env ↔
      ∃ i ∈ env I, ∃ a ∈ env P, ∃ c ∈ env P, ∃ ell ∈ env R, ∃ e ∈ env P,
        ∃ F ∈ env U, ∃ label ∈ env Labels,
          env z = ZFSet.pair i (literalTaskField a c ell e F label j) ∧
            i = literalTaskCode a c ell e F label := by
  simp only [literalTaskFieldEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_literalTaskFormula]
  simp only [literalTaskField_map]
  rfl

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem pairCompositionFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {K I J B D L Es Ss W : ZFSet.{u}} (hK : K ∈ M.sets) (hI : I ∈ M.sets)
    (hJ : J ∈ M.sets) (hB : B ∈ M.sets) (hD : D ∈ M.sets) (hL : L ∈ M.sets)
    (hEs : Es ∈ M.sets) (hSs : Ss ∈ M.sets) (hW : W ∈ M.sets) :
    pairCompositionFamily K I J B D L Es Ss W ∈ M.sets := by
  have hU := M.union_mem unions (M.union_mem unions hEs)
  have hV := M.union_mem unions (M.union_mem unions hSs)
  let params := extend K (extend I (extend J (extend B (extend D (extend L
    (extend Es (extend Ss (extend W (extend (⋃₀ ⋃₀ Es) (extend (⋃₀ ⋃₀ Ss) Fin.elim0))))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.pairCompositionEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11) params
    (Fin.cases hK (Fin.cases hI (Fin.cases hJ (Fin.cases hB (Fin.cases hD (Fin.cases hL
      (Fin.cases hEs (Fin.cases hSs (Fin.cases hW (Fin.cases hU (Fin.cases hV (fun i => Fin.elim0 i))))))))))))
    (M.prod_mem pairing unions powers separation hK hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.pairCompositionEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11) (extend z params))
      (ZFSet.prod K W) = pairCompositionFamily K I J B D L Es Ss W := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, pairCompositionFamily, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_pairCompositionEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 _)
  exact equal ▸ selected

noncomputable def groundPairCompositions (K I J B D L Es Ss : ZFSet.{u}) : ZFSet.{u} :=
  pairCompositionFamily K I J B D L Es Ss (M.groundRelations B L)

theorem groundPairCompositions_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {K I J B D L Es Ss : ZFSet.{u}} (hK : K ∈ M.sets) (hI : I ∈ M.sets)
    (hJ : J ∈ M.sets) (hB : B ∈ M.sets) (hD : D ∈ M.sets) (hL : L ∈ M.sets)
    (hEs : Es ∈ M.sets) (hSs : Ss ∈ M.sets)
    (bases : FunctionGraphOn J Es) (maps : FunctionGraphOn I Ss) (subset : K ⊆ ZFSet.prod I J) :
    M.groundPairCompositions K I J B D L Es Ss ∈ M.sets ∧
      ZFSet.IsFunc K (M.groundRelations B L) (M.groundPairCompositions K I J B D L Es Ss) ∧
      ∀ i j ell f c, ZFSet.pair j ell ∈ Es → ZFSet.pair i f ∈ Ss →
        (ZFSet.pair (ZFSet.pair i j) c ∈ M.groundPairCompositions K I J B D L Es Ss ↔
          ZFSet.pair i j ∈ K ∧ c = relationCompose B D L ell f) := by
  have bounded (i j ell f : ZFSet.{u}) (first : ZFSet.pair j ell ∈ Es)
      (second : ZFSet.pair i f ∈ Ss) : relationCompose B D L ell f ∈ M.groundRelations B L :=
    (M.mem_groundRelations B L _).2
      ⟨M.relationCompose_mem pairing unions powers separation hB hD hL
        (M.pair_right (M.transitive hEs first)) (M.pair_right (M.transitive hSs second)),
        fun _ hz => (ZFSet.mem_sep.1 hz).1⟩
  refine ⟨M.pairCompositionFamily_mem pairing unions powers separation hK hI hJ hB hD hL hEs hSs
    (M.groundRelations_mem pairing unions powers separation hB hL),
    pairCompositionFamily_function bases maps subset (fun i _ j _ ell f first second => bounded i j ell f first second), ?_⟩
  intro i j ell f c first second
  rw [groundPairCompositions, pairCompositionFamily_entry_iff bases maps first second]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · rintro ⟨hk, rfl⟩
    exact ⟨hk, bounded i j ell f first second, rfl⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
