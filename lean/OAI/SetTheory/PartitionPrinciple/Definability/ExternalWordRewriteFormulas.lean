import OAI.SetTheory.PartitionPrinciple.Geometry.GroundFiniteWordLaws

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u

def wordSingleton (a : ZFSet.{u}) : ZFSet.{u} := {ZFSet.pair (natSetCode 0) a}

def wordDouble (a b : ZFSet.{u}) : ZFSet.{u} :=
  {ZFSet.pair (natSetCode 0) a, ZFSet.pair (natSetCode 1) b}

theorem finiteWordGraph_singleton {B : Type u} (s : Presentation B) (a : B) :
    finiteWordGraph s [a] = wordSingleton (s.encode a) := by
  apply ZFSet.ext
  intro z
  rw [mem_finiteWordGraph, wordSingleton, ZFSet.mem_singleton]
  constructor
  · rintro ⟨i, eq⟩
    have hi : i.val < 1 := i.isLt
    have equal : i = ⟨0, by simp⟩ := Fin.ext (by change i.val = 0; omega)
    subst i
    exact eq
  · intro eq
    exact ⟨⟨0, by simp⟩, eq⟩

theorem finiteWordGraph_double {B : Type u} (s : Presentation B) (a b : B) :
    finiteWordGraph s [a, b] = wordDouble (s.encode a) (s.encode b) := by
  apply ZFSet.ext
  intro z
  rw [mem_finiteWordGraph, wordDouble, ZFSet.mem_pair]
  constructor
  · rintro ⟨i, eq⟩
    have hi : i.val < 2 := i.isLt
    have cases : i = ⟨0, by simp⟩ ∨ i = ⟨1, by simp⟩ := by
      have values : i.val = 0 ∨ i.val = 1 := by omega
      exact values.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
    rcases cases with rfl | rfl
    · exact Or.inl eq
    · exact Or.inr eq
  · rintro (eq | eq)
    · exact ⟨⟨0, by simp⟩, eq⟩
    · exact ⟨⟨1, by simp⟩, eq⟩

def ExternalWordAtomicCode (G S m one l r : ZFSet.{u}) : Prop :=
  (one ∈ G ∧ l = wordSingleton (externalActorSymbol one) ∧ r = ∅) ∨
  (∃ g ∈ G, ∃ h ∈ G, ∃ k ∈ G, ZFSet.pair (ZFSet.pair g h) k ∈ m ∧
    l = wordDouble (externalActorSymbol g) (externalActorSymbol h) ∧
    r = wordSingleton (externalActorSymbol k)) ∨
  (∃ s ∈ S, (l = wordDouble (externalLetterSymbol s false) (externalLetterSymbol s true) ∨
    l = wordDouble (externalLetterSymbol s true) (externalLetterSymbol s false)) ∧ r = ∅)

def ExternalWordStepCode (W append G S m one f g : ZFSet.{u}) : Prop :=
  ∃ pre ∈ W, ∃ post ∈ W, ∃ l ∈ W, ∃ r ∈ W, ∃ pl ∈ W, ∃ pr ∈ W,
    ExternalWordAtomicCode G S m one l r ∧
    ZFSet.pair (ZFSet.pair pre l) pl ∈ append ∧
    ZFSet.pair (ZFSet.pair pre r) pr ∈ append ∧
    ((ZFSet.pair (ZFSet.pair pl post) f ∈ append ∧
        ZFSet.pair (ZFSet.pair pr post) g ∈ append) ∨
      (ZFSet.pair (ZFSet.pair pl post) g ∈ append ∧
        ZFSet.pair (ZFSet.pair pr post) f ∈ append))

theorem ExternalWordStepCode.symm {W append G S m one f g : ZFSet.{u}}
    (step : ExternalWordStepCode W append G S m one f g) :
    ExternalWordStepCode W append G S m one g f := by
  obtain ⟨pre, hp, post, hq, l, hl, r, hr, pl, hpl, pr, hpr, atomic, left, right, direction⟩ := step
  exact ⟨pre, hp, post, hq, l, hl, r, hr, pl, hpl, pr, hpr, atomic, left, right, direction.symm⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def actorSingletonWordFormula {n} (w zero g : Fin n) : BoundedFormula n :=
  exMem w (.conj (nonemptyTupleFormula 2 0
    (Fin.cases zero.succ (Fin.cases zero.succ (Fin.cases g.succ Fin.elim0))))
    (singletonFormula w.succ 0))

theorem truth_actorSingletonWordFormula {n} (w zero g : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (actorSingletonWordFormula w zero g) env ↔
      env w = {ZFSet.pair (env zero) (ZFSet.pair (env zero) (env g))} := by
  simp only [actorSingletonWordFormula, truth_exMem, Truth,
    truth_nonemptyTupleFormula, truth_singletonFormula]
  change (∃ z ∈ env w, z = ZFSet.pair (env zero) (ZFSet.pair (env zero) (env g)) ∧
    env w = {z}) ↔ _
  constructor
  · rintro ⟨z, _, rfl, eq⟩
    exact eq
  · intro eq
    exact ⟨_, eq.symm ▸ ZFSet.mem_singleton.2 rfl, rfl, eq⟩

def actorDoubleWordFormula {n} (w zero unit g h : Fin n) : BoundedFormula n :=
  exMem w (exMem w.succ
    (.conj (nonemptyTupleFormula 2 1
      (Fin.cases zero.succ.succ (Fin.cases zero.succ.succ (Fin.cases g.succ.succ Fin.elim0))))
      (.conj (nonemptyTupleFormula 2 0
        (Fin.cases unit.succ.succ (Fin.cases zero.succ.succ (Fin.cases h.succ.succ Fin.elim0))))
        (unorderedPairFormula w.succ.succ 1 0))))

theorem truth_actorDoubleWordFormula {n} (w zero unit g h : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (actorDoubleWordFormula w zero unit g h) env ↔
      env w = {ZFSet.pair (env zero) (ZFSet.pair (env zero) (env g)),
        ZFSet.pair (env unit) (ZFSet.pair (env zero) (env h))} := by
  simp only [actorDoubleWordFormula, truth_exMem, Truth,
    truth_nonemptyTupleFormula, truth_unorderedPairFormula]
  change (∃ z ∈ env w, ∃ v ∈ env w,
    z = ZFSet.pair (env zero) (ZFSet.pair (env zero) (env g)) ∧
    v = ZFSet.pair (env unit) (ZFSet.pair (env zero) (env h)) ∧ env w = {z, v}) ↔ _
  constructor
  · rintro ⟨z, _, v, _, rfl, rfl, eq⟩
    exact eq
  · intro eq
    exact ⟨_, eq.symm ▸ ZFSet.mem_pair.2 (Or.inl rfl),
      _, eq.symm ▸ ZFSet.mem_pair.2 (Or.inr rfl), rfl, rfl, eq⟩

def signedDoubleWordFormula {n} (w zero unit s a b : Fin n) : BoundedFormula n :=
  exMem w (exMem w.succ
    (.conj (nonemptyTupleFormula 3 1
      (Fin.cases zero.succ.succ (Fin.cases unit.succ.succ
        (Fin.cases s.succ.succ (Fin.cases a.succ.succ Fin.elim0)))))
      (.conj (nonemptyTupleFormula 3 0
        (Fin.cases unit.succ.succ (Fin.cases unit.succ.succ
          (Fin.cases s.succ.succ (Fin.cases b.succ.succ Fin.elim0)))))
        (unorderedPairFormula w.succ.succ 1 0))))

theorem truth_signedDoubleWordFormula {n} (w zero unit s a b : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (signedDoubleWordFormula w zero unit s a b) env ↔
      env w = {ZFSet.pair (env zero) (ZFSet.pair (env unit) (ZFSet.pair (env s) (env a))),
        ZFSet.pair (env unit) (ZFSet.pair (env unit) (ZFSet.pair (env s) (env b)))} := by
  simp only [signedDoubleWordFormula, truth_exMem, Truth,
    truth_nonemptyTupleFormula, truth_unorderedPairFormula]
  change (∃ z ∈ env w, ∃ v ∈ env w,
    z = ZFSet.pair (env zero) (ZFSet.pair (env unit) (ZFSet.pair (env s) (env a))) ∧
    v = ZFSet.pair (env unit) (ZFSet.pair (env unit) (ZFSet.pair (env s) (env b))) ∧
    env w = {z, v}) ↔ _
  constructor
  · rintro ⟨z, _, v, _, rfl, rfl, eq⟩
    exact eq
  · intro eq
    exact ⟨_, eq.symm ▸ ZFSet.mem_pair.2 (Or.inl rfl),
      _, eq.symm ▸ ZFSet.mem_pair.2 (Or.inr rfl), rfl, rfl, eq⟩

def externalWordAtomicFormula {n} (zero unit G S m one l r : Fin n) : BoundedFormula n :=
  disj (.conj (.mem one G) (.conj (actorSingletonWordFormula l zero one) (emptyFormula r)))
    (disj (exMem G (exMem G.succ (exMem G.succ.succ
      (.conj (tripleMembershipFormula 2 1 0 m.succ.succ.succ)
        (.conj (actorDoubleWordFormula l.succ.succ.succ zero.succ.succ.succ unit.succ.succ.succ 2 1)
          (actorSingletonWordFormula r.succ.succ.succ zero.succ.succ.succ 0))))))
      (exMem S (.conj
        (disj (signedDoubleWordFormula l.succ zero.succ unit.succ 0 zero.succ unit.succ)
          (signedDoubleWordFormula l.succ zero.succ unit.succ 0 unit.succ zero.succ)) (emptyFormula r.succ))))

theorem truth_externalWordAtomicFormula {n} (zero unit G S m one l r : Fin n)
    (env : Fin n → ZFSet.{u}) (zeroValue : env zero = natSetCode 0)
    (unitValue : env unit = natSetCode 1) :
    Truth (externalWordAtomicFormula zero unit G S m one l r) env ↔
      ExternalWordAtomicCode (env G) (env S) (env m) (env one) (env l) (env r) := by
  simp only [externalWordAtomicFormula, truth_disj, truth_exMem, Truth,
    truth_actorSingletonWordFormula, truth_actorDoubleWordFormula, truth_signedDoubleWordFormula,
    truth_emptyFormula, truth_tripleMembershipFormula]
  change ((env one ∈ env G ∧ env l = {ZFSet.pair (env zero) (ZFSet.pair (env zero) (env one))} ∧ env r = ∅) ∨
    (∃ g ∈ env G, ∃ h ∈ env G, ∃ k ∈ env G, ZFSet.pair (ZFSet.pair g h) k ∈ env m ∧
      env l = {ZFSet.pair (env zero) (ZFSet.pair (env zero) g), ZFSet.pair (env unit) (ZFSet.pair (env zero) h)} ∧
      env r = {ZFSet.pair (env zero) (ZFSet.pair (env zero) k)}) ∨
    (∃ s ∈ env S,
      (env l = {ZFSet.pair (env zero) (ZFSet.pair (env unit) (ZFSet.pair s (env zero))),
          ZFSet.pair (env unit) (ZFSet.pair (env unit) (ZFSet.pair s (env unit)))} ∨
        env l = {ZFSet.pair (env zero) (ZFSet.pair (env unit) (ZFSet.pair s (env unit))),
          ZFSet.pair (env unit) (ZFSet.pair (env unit) (ZFSet.pair s (env zero)))}) ∧ env r = ∅)) ↔ _
  rw [zeroValue, unitValue]
  rfl

def externalWordStepFormula {n} (W append zero unit G S m one f g : Fin n) : BoundedFormula n :=
  exMem W (exMem W.succ (exMem W.succ.succ (exMem W.succ.succ.succ
    (exMem W.succ.succ.succ.succ (exMem W.succ.succ.succ.succ.succ
      (.conj (externalWordAtomicFormula zero.succ.succ.succ.succ.succ.succ
        unit.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ
        S.succ.succ.succ.succ.succ.succ m.succ.succ.succ.succ.succ.succ
        one.succ.succ.succ.succ.succ.succ 3 2)
        (.conj (tripleMembershipFormula 5 3 1 append.succ.succ.succ.succ.succ.succ)
          (.conj (tripleMembershipFormula 5 2 0 append.succ.succ.succ.succ.succ.succ)
            (disj (.conj (tripleMembershipFormula 1 4 f.succ.succ.succ.succ.succ.succ append.succ.succ.succ.succ.succ.succ)
              (tripleMembershipFormula 0 4 g.succ.succ.succ.succ.succ.succ append.succ.succ.succ.succ.succ.succ))
              (.conj (tripleMembershipFormula 1 4 g.succ.succ.succ.succ.succ.succ append.succ.succ.succ.succ.succ.succ)
                (tripleMembershipFormula 0 4 f.succ.succ.succ.succ.succ.succ append.succ.succ.succ.succ.succ.succ)))))))))))

theorem truth_externalWordStepFormula {n} (W append zero unit G S m one f g : Fin n)
    (env : Fin n → ZFSet.{u}) (zeroValue : env zero = natSetCode 0)
    (unitValue : env unit = natSetCode 1) :
    Truth (externalWordStepFormula W append zero unit G S m one f g) env ↔
      ExternalWordStepCode (env W) (env append) (env G) (env S) (env m) (env one) (env f) (env g) := by
  simp only [externalWordStepFormula, truth_exMem, Truth, truth_tripleMembershipFormula, truth_disj,
    ExternalWordStepCode]
  constructor
  · rintro ⟨pre, hp, post, hq, l, hl, r, hr, pl, hpl, pr, hpr, atomic, left, right, direction⟩
    exact ⟨pre, hp, post, hq, l, hl, r, hr, pl, hpl, pr, hpr,
      (truth_externalWordAtomicFormula zero.succ.succ.succ.succ.succ.succ
        unit.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ
        S.succ.succ.succ.succ.succ.succ m.succ.succ.succ.succ.succ.succ
        one.succ.succ.succ.succ.succ.succ 3 2
        (extend pr (extend pl (extend r (extend l (extend post (extend pre env)))))) zeroValue unitValue).1 atomic, left, right, direction⟩
  · rintro ⟨pre, hp, post, hq, l, hl, r, hr, pl, hpl, pr, hpr, atomic, left, right, direction⟩
    exact ⟨pre, hp, post, hq, l, hl, r, hr, pl, hpl, pr, hpr,
      (truth_externalWordAtomicFormula zero.succ.succ.succ.succ.succ.succ
        unit.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ
        S.succ.succ.succ.succ.succ.succ m.succ.succ.succ.succ.succ.succ
        one.succ.succ.succ.succ.succ.succ 3 2
        (extend pr (extend pl (extend r (extend l (extend post (extend pre env)))))) zeroValue unitValue).2 atomic, left, right, direction⟩

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
