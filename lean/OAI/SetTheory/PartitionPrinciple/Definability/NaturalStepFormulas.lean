import OAI.SetTheory.PartitionPrinciple.Definability.TaggedSumPresentations

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

namespace SetFormula

def functionGraphOnFormula {n} (a f : Fin n) : SetFormula n :=
  ex (BoundedFormula.functionFormula a.succ 0 f.succ).toFormula

end SetFormula

namespace BoundedFormula

def graphRestrictionFormula {n} (p a b f : Fin n) : BoundedFormula n :=
  .conj (.allMem p (.conj (.mem 0 f.succ) (productElementFormula 0 a.succ b.succ)))
    (.allMem f (imp (productElementFormula 0 a.succ b.succ) (.mem 0 p.succ)))

theorem truth_graphRestrictionFormula {n} (p a b f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (graphRestrictionFormula p a b f) env ↔
      env p = ZFSet.sep (fun z => z ∈ ZFSet.prod (env a) (env b)) (env f) := by
  simp only [graphRestrictionFormula, Truth, truth_imp, truth_productElementFormula]
  change ((∀ z ∈ env p, z ∈ env f ∧ z ∈ ZFSet.prod (env a) (env b)) ∧
    (∀ z ∈ env f, z ∈ ZFSet.prod (env a) (env b) → z ∈ env p)) ↔ _
  constructor
  · rintro ⟨forward, backward⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    exact ⟨forward z, fun hz => backward z hz.1 hz.2⟩
  · intro eq
    rw [eq]
    exact ⟨fun z hz => ZFSet.mem_sep.1 hz, fun z hz bound => ZFSet.mem_sep.2 ⟨hz, bound⟩⟩

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_functionGraphOnFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {n} (a f : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (functionGraphOnFormula a f) env ↔ FunctionGraphOn (env a) (env f) := by
  rw [functionGraphOnFormula, realize_ex]
  constructor
  · rintro ⟨B, hB, code⟩
    exact ⟨B, (BoundedFormula.truth_functionFormula a.succ 0 f.succ _).1
      ((BoundedFormula.realize_toFormula M _ _ (Fin.cases hB members)).1 code)⟩
  · intro code
    have range := M.union_mem unions (M.union_mem unions (members f))
    exact ⟨ZFSet.sUnion (ZFSet.sUnion (env f)), range,
      (BoundedFormula.realize_toFormula M _ _ (Fin.cases range members)).2
        ((BoundedFormula.truth_functionFormula a.succ 0 f.succ _).2 code.to_isFunc)⟩

theorem realize_graphRestrictionFormula {n} (p a b f : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (BoundedFormula.graphRestrictionFormula p a b f).toFormula env ↔
      env p = ZFSet.sep (fun z => z ∈ ZFSet.prod (env a) (env b)) (env f) :=
  (BoundedFormula.realize_toFormula M _ _ members).trans
    (BoundedFormula.truth_graphRestrictionFormula p a b f env)

end TransitiveGround

end




open SetFormula
universe u

def groundRecursionStep (M : TransitiveGround.{u}) {k : Nat}
    (φ : SetFormula (k + 3)) (params : Fin k → ZFSet.{u}) (a p y : ZFSet.{u}) : Prop :=
  p ∈ M.sets ∧ y ∈ M.sets ∧ Realize M.sets φ (extend a (extend p (extend y params)))

namespace SetFormula

def ordinalRecursionTraceFormula {k : Nat} (φ : SetFormula (k + 3)) : SetFormula (k + 2) :=
  ex <| .conj (BoundedFormula.functionFormula 1 0 2).toFormula <|
    .all <| imp (.mem 0 2) <| .all <| imp (.mem 0 2) <|
      imp (BoundedFormula.pairMembershipFormula 1 0 4).toFormula <|
        ex <| .conj (BoundedFormula.graphRestrictionFormula 0 2 3 5).toFormula <|
          reindex (extend 2 (extend 0 (extend 1
            (fun j => j.succ.succ.succ.succ.succ.succ)))) φ

def ordinalSuccessorTraceFormula {k : Nat} (φ : SetFormula (k + 3)) : SetFormula (k + 2) :=
  ex (.conj (BoundedFormula.successorFormula 0 1).toFormula
    (reindex (extend 0 (extend 2 (fun j => j.succ.succ.succ))) (ordinalRecursionTraceFormula φ)))

end SetFormula

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem realize_ordinalRecursionTraceFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {k : Nat} (φ : SetFormula (k + 3)) (params : Fin k → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {A f : ZFSet.{u}}
    (hA : A ∈ M.sets) (hf : f ∈ M.sets) :
    Realize M.sets (ordinalRecursionTraceFormula φ) (extend A (extend f params)) ↔
      OrdinalRecursionTrace (groundRecursionStep M φ params) A f := by
  rw [ordinalRecursionTraceFormula, realize_ex]
  constructor
  · rintro ⟨B, hB, function, steps⟩
    have mem3 : ∀ i, extend B (extend A (extend f params)) i ∈ M.sets :=
      Fin.cases hB (Fin.cases hA (Fin.cases hf members))
    have func : ZFSet.IsFunc A B f := (BoundedFormula.truth_functionFormula 1 0 2 _).1
      ((BoundedFormula.realize_toFormula M _ _ mem3).1 function)
    refine ⟨⟨B, func⟩, ?_⟩
    intro a ha y ay
    have haM := M.transitive hA ha
    have hyB := (ZFSet.pair_mem_prod.1 (func.1 ay)).2
    have hyM := M.transitive hB hyB
    have first := (realize_imp M.sets _ _ _).1 (steps a haM) ha
    have second := (realize_imp M.sets _ _ _).1 (first y hyM) hyB
    have mem5 : ∀ i, extend y (extend a (extend B (extend A (extend f params)))) i ∈ M.sets :=
      Fin.cases hyM (Fin.cases haM mem3)
    have pairCode := (BoundedFormula.realize_toFormula M _ _ mem5).2
      ((BoundedFormula.truth_pairMembershipFormula 1 0 4 _).2 ay)
    obtain ⟨p, hp, restricted, step⟩ := (realize_ex M.sets _ _).1
      ((realize_imp M.sets _ _ _).1 second pairCode)
    have eq := (M.realize_graphRestrictionFormula 0 2 3 5 _ (Fin.cases hp mem5)).1 restricted
    have same : p = graphRestriction a f := eq.trans (graphRestriction_eq_sep func).symm
    rw [realize_reindex, map_extend, map_extend, map_extend] at step
    change Realize M.sets φ (extend a (extend p (extend y params))) at step
    rw [same] at hp step
    exact ⟨hp, hyM, step⟩
  · intro trace
    let B := ZFSet.sUnion (ZFSet.sUnion f)
    have hB : B ∈ M.sets := M.union_mem unions (M.union_mem unions hf)
    have func : ZFSet.IsFunc A B f := trace.1.to_isFunc
    have mem3 : ∀ i, extend B (extend A (extend f params)) i ∈ M.sets :=
      Fin.cases hB (Fin.cases hA (Fin.cases hf members))
    refine ⟨B, hB, (BoundedFormula.realize_toFormula M _ _ mem3).2
      ((BoundedFormula.truth_functionFormula 1 0 2 _).2 func), ?_⟩
    intro a haM
    apply (realize_imp M.sets _ _ _).2
    intro ha y hyM
    apply (realize_imp M.sets _ _ _).2
    intro _
    apply (realize_imp M.sets _ _ _).2
    intro pairCode
    have mem5 : ∀ i, extend y (extend a (extend B (extend A (extend f params)))) i ∈ M.sets :=
      Fin.cases hyM (Fin.cases haM mem3)
    have ay := (BoundedFormula.truth_pairMembershipFormula 1 0 4 _).1
      ((BoundedFormula.realize_toFormula M _ _ mem5).1 pairCode)
    obtain ⟨hp, _, step⟩ := trace.2 a ha y ay
    apply (realize_ex M.sets _ _).2
    refine ⟨graphRestriction a f, hp,
      (M.realize_graphRestrictionFormula 0 2 3 5 _ (Fin.cases hp mem5)).2
        (graphRestriction_eq_sep func), ?_⟩
    rw [realize_reindex, map_extend, map_extend, map_extend]
    exact step

theorem realize_ordinalSuccessorTraceFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {k : Nat} (φ : SetFormula (k + 3)) (params : Fin k → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {a f : ZFSet.{u}}
    (ha : a ∈ M.sets) (hf : f ∈ M.sets) :
    Realize M.sets (ordinalSuccessorTraceFormula φ) (extend a (extend f params)) ↔
      OrdinalRecursionTrace (groundRecursionStep M φ params) (insert a a) f := by
  rw [ordinalSuccessorTraceFormula, realize_ex]
  constructor
  · rintro ⟨A, hA, successor, trace⟩
    have eq := (BoundedFormula.truth_successorFormula 0 1 _).1
      ((BoundedFormula.realize_toFormula M _ _
        (Fin.cases hA (Fin.cases ha (Fin.cases hf members)))).1 successor)
    rw [realize_reindex, map_extend, map_extend] at trace
    change Realize M.sets (ordinalRecursionTraceFormula φ) (extend A (extend f params)) at trace
    have code := (M.realize_ordinalRecursionTraceFormula unions φ params members hA hf).1 trace
    exact eq ▸ code
  · intro trace
    have hA := M.insert_mem pairing unions ha ha
    refine ⟨insert a a, hA, (BoundedFormula.realize_toFormula M _ _
      (Fin.cases hA (Fin.cases ha (Fin.cases hf members)))).2
        ((BoundedFormula.truth_successorFormula 0 1 _).2 rfl), ?_⟩
    rw [realize_reindex, map_extend, map_extend]
    exact (M.realize_ordinalRecursionTraceFormula unions φ params members hA hf).2 trace

end TransitiveGround





namespace SetFormula

def naturalStepFormula {k : Nat} (successor : SetFormula (k + 2)) : SetFormula (k + 4) :=
  disj (.conj (BoundedFormula.emptyFormula 0).toFormula (.equal 2 3))
    (ex (ex (.conj (BoundedFormula.successorFormula 2 1).toFormula
      (.conj (BoundedFormula.pairMembershipFormula 1 0 3).toFormula
        (reindex (extend 0 (extend 4 (fun j => j.succ.succ.succ.succ.succ.succ))) successor)))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_naturalStepFormula {k : Nat} (φ : SetFormula (k + 2))
    (params : Fin k → ZFSet.{u}) (members : ∀ i, params i ∈ M.sets)
    {a p y base : ZFSet.{u}} (ha : a ∈ M.sets) (hp : p ∈ M.sets)
    (hy : y ∈ M.sets) (hb : base ∈ M.sets) :
    Realize M.sets (naturalStepFormula φ) (extend a (extend p (extend y (extend base params)))) ↔
      (a = ∅ ∧ y = base) ∨ ∃ m ∈ M.sets, ∃ x ∈ M.sets,
        a = insert m m ∧ ZFSet.pair m x ∈ p ∧
          Realize M.sets φ (extend x (extend y params)) := by
  have mem4 : ∀ i, extend a (extend p (extend y (extend base params))) i ∈ M.sets :=
    Fin.cases ha (Fin.cases hp (Fin.cases hy (Fin.cases hb members)))
  rw [naturalStepFormula, realize_disj]
  apply or_congr
  · change (Realize M.sets (BoundedFormula.emptyFormula 0).toFormula _ ∧ y = base) ↔ _
    exact and_congr ((BoundedFormula.realize_toFormula M _ _ mem4).trans
      (BoundedFormula.truth_emptyFormula _ _)) Iff.rfl
  · rw [realize_ex]
    apply exists_congr
    intro m
    apply and_congr_right
    intro hm
    rw [realize_ex]
    apply exists_congr
    intro x
    apply and_congr_right
    intro hx
    have mem6 : ∀ i, extend x (extend m (extend a (extend p (extend y (extend base params))))) i ∈ M.sets :=
      Fin.cases hx (Fin.cases hm mem4)
    change (Realize M.sets (BoundedFormula.successorFormula 2 1).toFormula _ ∧
      Realize M.sets (BoundedFormula.pairMembershipFormula 1 0 3).toFormula _ ∧ _) ↔ _
    rw [BoundedFormula.realize_toFormula M _ _ mem6, BoundedFormula.truth_successorFormula,
      BoundedFormula.realize_toFormula M _ _ mem6, BoundedFormula.truth_pairMembershipFormula,
      realize_reindex, map_extend, map_extend]
    rfl

end TransitiveGround

theorem natSetCode_succ_eq_insert_iff (n : Nat) (x : ZFSet.{u}) :
    natSetCode (n + 1) = insert x x ↔ x = natSetCode n := by
  constructor
  · intro equal
    have member : x ∈ natSetCode (n + 1) := equal.symm ▸ ZFSet.mem_insert x x
    obtain ⟨j, _, rfl⟩ := (mem_natSetCode x (n + 1)).1 member
    have codes : natSetCode (n + 1) = natSetCode (j + 1) := equal
    exact congrArg natSetCode (Nat.add_right_cancel (natSetCode_injective codes)).symm
  · rintro rfl
    rfl


end PartitionPilot.Forcing

end OAI
