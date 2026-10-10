import OAI.SetTheory.PartitionPrinciple.Definability.UnionEntryFormula
import OAI.SetTheory.PartitionPrinciple.Transfinite.OrdinalRecursionTraces

namespace OAI


namespace PartitionPilot.Forcing

namespace BoundedFormula

open SetFormula
universe u

def Truth : {n : Nat} → BoundedFormula n → (Fin n → ZFSet.{u}) → Prop
  | _, .equal i j, env => env i = env j
  | _, .mem i j, env => env i ∈ env j
  | _, .neg φ, env => ¬ Truth φ env
  | _, .conj φ ψ, env => Truth φ env ∧ Truth ψ env
  | _, .allMem b φ, env => ∀ x ∈ env b, Truth φ (extend x env)

theorem truth_imp {n} (φ ψ : BoundedFormula n) (env : Fin n → ZFSet.{u}) :
    Truth (imp φ ψ) env ↔ (Truth φ env → Truth ψ env) := by
  classical
  simp only [imp, Truth, not_and, not_not]

theorem truth_disj {n} (φ ψ : BoundedFormula n) (env : Fin n → ZFSet.{u}) :
    Truth (disj φ ψ) env ↔ (Truth φ env ∨ Truth ψ env) := by
  classical
  simp only [disj, Truth, not_and_or, not_not]

theorem truth_exMem {n} (b : Fin n) (φ : BoundedFormula (n + 1)) (env : Fin n → ZFSet.{u}) :
    Truth (exMem b φ) env ↔ ∃ x ∈ env b, Truth φ (extend x env) := by
  classical
  simp only [exMem, Truth, not_forall, not_not, exists_prop]

theorem realize_toFormula (M : TransitiveGround.{u}) {n} (φ : BoundedFormula n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets φ.toFormula env ↔ Truth φ env := by
  induction φ with
  | equal i j => rfl
  | mem i j => rfl
  | neg φ ih => exact not_congr (ih env members)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ env members) (ihψ env members)
  | allMem b φ ih =>
    change (∀ x ∈ M.sets, Realize M.sets (SetFormula.imp (.mem 0 b.succ) φ.toFormula) (extend x env)) ↔ _
    constructor
    · intro h x hx
      have hxM := M.transitive (members b) hx
      exact (ih (extend x env) (Fin.cases hxM members)).1
        ((realize_imp M.sets _ _ _).1 (h x hxM) hx)
    · intro h x hxM
      apply (realize_imp M.sets _ _ _).2
      intro hx
      exact (ih (extend x env) (Fin.cases hxM members)).2 (h x hx)

theorem absolute (M N : TransitiveGround.{u}) {n} (φ : BoundedFormula n)
    (env : Fin n → ZFSet.{u}) (inM : ∀ i, env i ∈ M.sets) (inN : ∀ i, env i ∈ N.sets) :
    Realize M.sets φ.toFormula env ↔ Realize N.sets φ.toFormula env :=
  (realize_toFormula M φ env inM).trans (realize_toFormula N φ env inN).symm

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def emptyFormula {n} (x : Fin n) : BoundedFormula n :=
  .allMem x (.neg (.equal 0 0))

def successorFormula {n} (y x : Fin n) : BoundedFormula n :=
  .conj (.mem x y) (.conj (.allMem x (.mem 0 y.succ))
    (.allMem y (disj (.equal 0 x.succ) (.mem 0 x.succ))))

def setTransitiveFormula {n} (x : Fin n) : BoundedFormula n :=
  .allMem x (.allMem 0 (.mem 0 x.succ.succ))

def zeroOrSuccessorFormula {n} (x : Fin n) : BoundedFormula n :=
  disj (emptyFormula x) (exMem x (successorFormula x.succ 0))

def naturalFormula {n} (x : Fin n) : BoundedFormula n :=
  .conj (setTransitiveFormula x) (.conj (zeroOrSuccessorFormula x)
    (.allMem x (.conj (setTransitiveFormula 0) (zeroOrSuccessorFormula 0))))

theorem truth_emptyFormula {n} (x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (emptyFormula x) env ↔ env x = ∅ := by
  change (∀ y ∈ env x, ¬ y = y) ↔ _
  constructor
  · intro h
    exact (ZFSet.eq_empty _).2 (fun y hy => h y hy rfl)
  · intro h y hy
    exact False.elim ((ZFSet.eq_empty _).1 h y hy)

theorem truth_successorFormula {n} (y x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (successorFormula y x) env ↔ env y = insert (env x) (env x) := by
  simp only [successorFormula, Truth, truth_disj]
  change (env x ∈ env y ∧ (∀ z ∈ env x, z ∈ env y) ∧
    ∀ z ∈ env y, z = env x ∨ z ∈ env x) ↔ _
  constructor
  · rintro ⟨hx, lower, upper⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_insert_iff]
    exact ⟨upper z, fun h => h.elim (fun eq => eq.symm ▸ hx) (lower z)⟩
  · intro eq
    rw [eq]
    exact ⟨ZFSet.mem_insert _ _, fun _ hz => ZFSet.mem_insert_of_mem _ hz,
      fun _ hz => ZFSet.mem_insert_iff.1 hz⟩

theorem truth_setTransitiveFormula {n} (x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (setTransitiveFormula x) env ↔ setTransitive (env x) := Iff.rfl

theorem truth_zeroOrSuccessorFormula {n} (x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (zeroOrSuccessorFormula x) env ↔ zeroOrSuccessor (env x) := by
  simp only [zeroOrSuccessorFormula, truth_disj, truth_emptyFormula, truth_exMem,
    truth_successorFormula]
  rfl

theorem truth_naturalFormula {n} (x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (naturalFormula x) env ↔ env x ∈ ZFSet.omega := by
  simp only [naturalFormula, Truth, truth_setTransitiveFormula, truth_zeroOrSuccessorFormula]
  exact naturalSetProperty_iff_mem_omega (env x)

theorem realize_naturalFormula (M : TransitiveGround.{u}) {n}
    (x : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (naturalFormula x).toFormula env ↔ env x ∈ ZFSet.omega :=
  (realize_toFormula M _ env members).trans (truth_naturalFormula x env)






theorem truth_singletonFormula {n} (z x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (singletonFormula z x) env ↔ env z = {env x} := by
  change (env x ∈ env z ∧ ∀ w ∈ env z, w = env x) ↔ _
  constructor
  · rintro ⟨member, only⟩
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_singleton]
    exact ⟨only w, fun eq => eq.symm ▸ member⟩
  · intro eq
    rw [eq]
    exact ⟨ZFSet.mem_singleton.2 rfl, fun _ h => ZFSet.mem_singleton.1 h⟩

theorem truth_unorderedPairFormula {n} (z x y : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (unorderedPairFormula z x y) env ↔ env z = {env x, env y} := by
  simp only [unorderedPairFormula, Truth, truth_disj]
  change (env x ∈ env z ∧ env y ∈ env z ∧ ∀ w ∈ env z, w = env x ∨ w = env y) ↔ _
  constructor
  · rintro ⟨hx, hy, only⟩
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_pair]
    refine ⟨only w, ?_⟩
    rintro (rfl | rfl)
    · exact hx
    · exact hy
  · intro eq
    rw [eq]
    exact ⟨ZFSet.mem_pair.2 (Or.inl rfl), ZFSet.mem_pair.2 (Or.inr rfl), fun _ h => ZFSet.mem_pair.1 h⟩

theorem truth_orderedPairFormula {n} (z x y : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (orderedPairFormula z x y) env ↔ env z = ZFSet.pair (env x) (env y) := by
  rw [orderedPairFormula, truth_exMem]
  constructor
  · rintro ⟨a, _, first, rest⟩
    have ha := (truth_singletonFormula 0 x.succ (extend a env)).1 first
    obtain ⟨b, _, second, shape⟩ := (truth_exMem _ _ _).1 rest
    have hb := (truth_unorderedPairFormula 0 x.succ.succ y.succ.succ (extend b (extend a env))).1 second
    have hz := (truth_unorderedPairFormula z.succ.succ 1 0 (extend b (extend a env))).1 shape
    change a = {env x} at ha
    change b = {env x, env y} at hb
    change env z = {a, b} at hz
    rw [hz, ha, hb]
    rfl
  · intro eq
    have ha : ({env x} : ZFSet.{u}) ∈ env z := by
      rw [eq]
      exact ZFSet.mem_pair.2 (Or.inl rfl)
    refine ⟨{env x}, ha, (truth_singletonFormula 0 x.succ _).2 rfl, ?_⟩
    apply (truth_exMem _ _ _).2
    have hb : ({env x, env y} : ZFSet.{u}) ∈ env z := by
      rw [eq]
      exact ZFSet.mem_pair.2 (Or.inr rfl)
    exact ⟨{env x, env y}, hb, (truth_unorderedPairFormula 0 x.succ.succ y.succ.succ _).2 rfl,
      (truth_unorderedPairFormula z.succ.succ 1 0 _).2 eq⟩

theorem truth_pairMembershipFormula {n} (x y r : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (pairMembershipFormula x y r) env ↔ ZFSet.pair (env x) (env y) ∈ env r := by
  rw [pairMembershipFormula, truth_exMem]
  constructor
  · rintro ⟨z, hz, shape⟩
    have eq := (truth_orderedPairFormula 0 x.succ y.succ (extend z env)).1 shape
    exact eq ▸ hz
  · intro member
    exact ⟨ZFSet.pair (env x) (env y), member, (truth_orderedPairFormula 0 x.succ y.succ _).2 rfl⟩

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing

universe u

namespace SetFormula

def exactSetFormula {n} (output : Fin n) (entry : SetFormula (n + 1)) : SetFormula n :=
  .all (.conj (imp (.mem 0 output.succ) entry) (imp entry (.mem 0 output.succ)))

end SetFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_exactSetFormula {n} (output : Fin n) (entry : SetFormula (n + 1))
    (env : Fin n → ZFSet.{u}) {target : ZFSet.{u}}
    (hOutput : env output ∈ M.sets) (elements : ∀ z ∈ target, z ∈ M.sets)
    (meaning : ∀ z ∈ M.sets, Realize M.sets entry (extend z env) ↔ z ∈ target) :
    Realize M.sets (exactSetFormula output entry) env ↔ env output = target := by
  change (∀ z ∈ M.sets, Realize M.sets
    (.conj (imp (.mem 0 output.succ) entry) (imp entry (.mem 0 output.succ))) (extend z env)) ↔ _
  simp only [Realize, realize_imp]
  change (∀ z ∈ M.sets, (z ∈ env output → Realize M.sets entry (extend z env)) ∧
    (Realize M.sets entry (extend z env) → z ∈ env output)) ↔ _
  constructor
  · intro correct
    apply ZFSet.ext
    intro z
    constructor
    · intro member
      have hz := M.transitive hOutput member
      exact (meaning z hz).1 ((correct z hz).1 member)
    · intro member
      have hz := elements z member
      exact (correct z hz).2 ((meaning z hz).2 member)
  · intro equal z hz
    exact ⟨fun member => (meaning z hz).2 (equal ▸ member),
      fun predicate => equal.symm ▸ (meaning z hz).1 predicate⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula SetRealization
universe u

def ordinalFormula {n} (x : Fin n) : BoundedFormula n :=
  .conj (setTransitiveFormula x) (.allMem x (setTransitiveFormula 0))

theorem truth_ordinalFormula {n} (x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (ordinalFormula x) env ↔ ∃ o : Ordinal.{u}, env x = ordinalCode o := by
  simp only [ordinalFormula, Truth, truth_setTransitiveFormula]
  exact ordinalSetProperty_iff (env x)

theorem realize_ordinalFormula (M : TransitiveGround.{u}) {n}
    (x : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (ordinalFormula x).toFormula env ↔ ∃ o : Ordinal.{u}, env x = ordinalCode o :=
  (realize_toFormula M _ env members).trans (truth_ordinalFormula x env)

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def graphFiberInclusionFormula {n} (x y f g : Fin n) : BoundedFormula n :=
  .allMem f (.allMem 0 (.allMem 0
    (imp (orderedPairFormula 2 x.succ.succ.succ 0)
      (pairMembershipFormula y.succ.succ.succ 0 g.succ.succ.succ))))

theorem truth_graphFiberInclusionFormula {n} (x y f g : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (graphFiberInclusionFormula x y f g) env ↔
      ∀ z, ZFSet.pair (env x) z ∈ env f → ZFSet.pair (env y) z ∈ env g := by
  simp only [graphFiberInclusionFormula, Truth, truth_imp,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  change (∀ p ∈ env f, ∀ a ∈ p, ∀ z ∈ a,
    p = ZFSet.pair (env x) z → ZFSet.pair (env y) z ∈ env g) ↔ _
  constructor
  · intro h z entry
    exact h (ZFSet.pair (env x) z) entry {env x, z}
      (ZFSet.mem_pair.2 (Or.inr rfl)) z (ZFSet.mem_pair.2 (Or.inr rfl)) rfl
  · intro h p hp a _ z _ equal
    exact h z (equal ▸ hp)

def graphFiberEqualityFormula {n} (x y f g : Fin n) : BoundedFormula n :=
  .conj (graphFiberInclusionFormula x y f g) (graphFiberInclusionFormula y x g f)

theorem truth_graphFiberEqualityFormula {n} (x y f g : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (graphFiberEqualityFormula x y f g) env ↔
      ∀ z, ZFSet.pair (env x) z ∈ env f ↔ ZFSet.pair (env y) z ∈ env g := by
  simp only [graphFiberEqualityFormula, Truth, truth_graphFiberInclusionFormula]
  exact ⟨fun h z => ⟨h.1 z, h.2 z⟩, fun h => ⟨fun z => (h z).1, fun z => (h z).2⟩⟩

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing

universe u

structure PartialOrderCode (Q R : ZFSet.{u}) : Prop where
  relation : R ⊆ ZFSet.prod Q Q
  refl : ∀ x ∈ Q, ZFSet.pair x x ∈ R
  antisymm : ∀ x ∈ Q, ∀ y ∈ Q, ZFSet.pair x y ∈ R → ZFSet.pair y x ∈ R → x = y
  trans : ∀ x ∈ Q, ∀ y ∈ Q, ∀ z ∈ Q,
    ZFSet.pair x y ∈ R → ZFSet.pair y z ∈ R → ZFSet.pair x z ∈ R

namespace BoundedFormula

open SetFormula

def relationOnFormula {n} (c r : Fin n) : BoundedFormula n :=
  .allMem r (exMem c.succ (exMem c.succ.succ (orderedPairFormula 2 1 0)))

def reflexiveFormula {n} (c r : Fin n) : BoundedFormula n :=
  .allMem c (pairMembershipFormula 0 0 r.succ)

def antisymmetricFormula {n} (c r : Fin n) : BoundedFormula n :=
  .allMem c (.allMem c.succ (imp
    (.conj (pairMembershipFormula 1 0 r.succ.succ) (pairMembershipFormula 0 1 r.succ.succ)) (.equal 1 0)))

def transitiveFormula {n} (c r : Fin n) : BoundedFormula n :=
  .allMem c (.allMem c.succ (.allMem c.succ.succ (imp
    (.conj (pairMembershipFormula 2 1 r.succ.succ.succ) (pairMembershipFormula 1 0 r.succ.succ.succ))
    (pairMembershipFormula 2 0 r.succ.succ.succ))))

def partialOrderFormula {n} (c r : Fin n) : BoundedFormula n :=
  .conj (relationOnFormula c r) (.conj (reflexiveFormula c r)
    (.conj (antisymmetricFormula c r) (transitiveFormula c r)))

def topFormula {n} (c r t : Fin n) : BoundedFormula n :=
  .conj (.mem t c) (.allMem c (pairMembershipFormula 0 t.succ r.succ))

theorem truth_relationOnFormula {n} (c r : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (relationOnFormula c r) env ↔ env r ⊆ ZFSet.prod (env c) (env c) := by
  simp only [relationOnFormula, Truth, truth_exMem, truth_orderedPairFormula]
  exact forall_congr' (fun _ => forall_congr' (fun _ => ZFSet.mem_prod.symm))

theorem truth_partialOrderFormula {n} (c r : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (partialOrderFormula c r) env ↔ PartialOrderCode (env c) (env r) := by
  simp only [partialOrderFormula, Truth, truth_relationOnFormula, reflexiveFormula,
    antisymmetricFormula, transitiveFormula, truth_imp, truth_pairMembershipFormula]
  constructor
  · rintro ⟨shape, refl, antisymm, trans⟩
    exact ⟨shape, refl, fun x hx y hy xy yx => antisymm x hx y hy ⟨xy, yx⟩,
      fun x hx y hy z hz xy yz => trans x hx y hy z hz ⟨xy, yz⟩⟩
  · intro h
    exact ⟨h.relation, h.refl, fun x hx y hy ⟨xy, yx⟩ => h.antisymm x hx y hy xy yx,
      fun x hx y hy z hz ⟨xy, yz⟩ => h.trans x hx y hy z hz xy yz⟩

theorem truth_topFormula {n} (c r t : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (topFormula c r t) env ↔ env t ∈ env c ∧ ∀ x ∈ env c, ZFSet.pair x (env t) ∈ env r := by
  simp only [topFormula, Truth, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_partialOrderCode {Q R : ZFSet.{u}} (hQ : Q ∈ M.sets) (hR : R ∈ M.sets) :
    Realize M.sets (BoundedFormula.partialOrderFormula 0 1).toFormula (extend Q (extend R Fin.elim0)) ↔
      PartialOrderCode Q R :=
  (BoundedFormula.realize_toFormula M _ _ (Fin.cases hQ (Fin.cases hR (fun i => Fin.elim0 i)))).trans
    (BoundedFormula.truth_partialOrderFormula 0 1 _)

theorem partialOrderCode_absolute (N : TransitiveGround.{u}) {Q R : ZFSet.{u}}
    (hQM : Q ∈ M.sets) (hRM : R ∈ M.sets) (hQN : Q ∈ N.sets) (hRN : R ∈ N.sets) :
    Realize M.sets (BoundedFormula.partialOrderFormula 0 1).toFormula (extend Q (extend R Fin.elim0)) ↔
      Realize N.sets (BoundedFormula.partialOrderFormula 0 1).toFormula (extend Q (extend R Fin.elim0)) :=
  (M.realize_partialOrderCode hQM hRM).trans (N.realize_partialOrderCode hQN hRN).symm

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def orderedTripleFormula {n} (w x y z : Fin n) : BoundedFormula n :=
  exMem w (exMem 0 (.conj (orderedPairFormula 0 x.succ.succ y.succ.succ)
    (orderedPairFormula w.succ.succ 0 z.succ.succ)))

def tripleMembershipFormula {n} (x y z f : Fin n) : BoundedFormula n :=
  exMem f (orderedTripleFormula 0 x.succ y.succ z.succ)

theorem truth_orderedTripleFormula {n} (w x y z : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (orderedTripleFormula w x y z) env ↔
      env w = ZFSet.pair (ZFSet.pair (env x) (env y)) (env z) := by
  simp only [orderedTripleFormula, truth_exMem, Truth, truth_orderedPairFormula]
  change (∃ a ∈ env w, ∃ b ∈ a, b = ZFSet.pair (env x) (env y) ∧
    env w = ZFSet.pair b (env z)) ↔ _
  constructor
  · rintro ⟨a, _, b, _, rfl, eq⟩
    exact eq
  · intro eq
    refine ⟨{ZFSet.pair (env x) (env y)}, ?_, ZFSet.pair (env x) (env y),
      ZFSet.mem_singleton.2 rfl, rfl, eq⟩
    rw [eq]
    exact ZFSet.mem_pair.2 (Or.inl rfl)

theorem truth_tripleMembershipFormula {n} (x y z f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (tripleMembershipFormula x y z f) env ↔
      ZFSet.pair (ZFSet.pair (env x) (env y)) (env z) ∈ env f := by
  simp only [tripleMembershipFormula, truth_exMem, truth_orderedTripleFormula]
  change (∃ w ∈ env f, w = ZFSet.pair (ZFSet.pair (env x) (env y)) (env z)) ↔ _
  exact ⟨fun ⟨_, hw, eq⟩ => eq ▸ hw, fun hw => ⟨_, hw, rfl⟩⟩

end PartitionPilot.Forcing.BoundedFormula


section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

theorem truth_relationBetweenFormula {n} (a b f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (relationBetweenFormula a b f) env ↔ env f ⊆ ZFSet.prod (env a) (env b) := by
  simp only [relationBetweenFormula, Truth, truth_exMem, truth_orderedPairFormula]
  exact forall_congr' (fun _ => forall_congr' (fun _ => ZFSet.mem_prod.symm))

theorem truth_functionFormula {n} (a b f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (functionFormula a b f) env ↔ ZFSet.IsFunc (env a) (env b) (env f) := by
  simp only [functionFormula, Truth, truth_relationBetweenFormula, truth_exMem,
    truth_pairMembershipFormula, truth_imp]
  constructor
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro x hx
    obtain ⟨y, _, pair, unique⟩ := total x hx
    refine ⟨y, pair, ?_⟩
    intro z rel
    exact unique z (ZFSet.pair_mem_prod.1 (shape rel)).2 rel
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro x hx
    obtain ⟨y, rel, unique⟩ := total x hx
    exact ⟨y, (ZFSet.pair_mem_prod.1 (shape rel)).2, rel, fun z _ hz => unique z hz⟩

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_functionCode {A B f : ZFSet.{u}}
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hf : f ∈ M.sets) :
    Realize M.sets (BoundedFormula.functionFormula 0 1 2).toFormula
      (extend A (extend B (extend f Fin.elim0))) ↔ ZFSet.IsFunc A B f :=
  (BoundedFormula.realize_toFormula M _ _ (Fin.cases hA (Fin.cases hB (Fin.cases hf (fun i => Fin.elim0 i))))).trans
    (BoundedFormula.truth_functionFormula 0 1 2 _)

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def nestedActionTripleFormula {n} (z g a b c d : Fin n) : BoundedFormula n :=
  let lift4 (j : Fin n) := j.succ.succ.succ.succ
  let lift6 (j : Fin n) := j.succ.succ.succ.succ.succ.succ
  exMem z (exMem 0 (exMem z.succ.succ (exMem 0
    (.conj (orderedPairFormula (lift4 z) 2 0)
      (.conj (orderedPairFormula 0 (lift4 c) (lift4 d))
        (exMem 2 (exMem 0 (.conj (orderedPairFormula 4 (lift6 g) 0)
          (orderedPairFormula 0 (lift6 a) (lift6 b))))))))))

theorem truth_nestedActionTripleFormula {n} (z g a b c d : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (nestedActionTripleFormula z g a b c d) env ↔
      env z = ZFSet.pair (ZFSet.pair (env g) (ZFSet.pair (env a) (env b)))
        (ZFSet.pair (env c) (env d)) := by
  simp only [nestedActionTripleFormula, truth_exMem, Truth, truth_orderedPairFormula]
  change (∃ s ∈ env z, ∃ x ∈ s, ∃ t ∈ env z, ∃ y ∈ t,
    env z = ZFSet.pair x y ∧ y = ZFSet.pair (env c) (env d) ∧
      ∃ w ∈ x, ∃ v ∈ w, x = ZFSet.pair (env g) v ∧ v = ZFSet.pair (env a) (env b)) ↔ _
  constructor
  · rintro ⟨_, _, x, _, _, _, y, _, outer, hy, _, _, v, _, hx, hv⟩
    rw [outer, hy, hx, hv]
  · intro equal
    let v := ZFSet.pair (env a) (env b)
    let x := ZFSet.pair (env g) v
    let y := ZFSet.pair (env c) (env d)
    refine ⟨{x}, ?_, x, ZFSet.mem_singleton.2 rfl, {x, y}, ?_, y,
      ZFSet.mem_pair.2 (Or.inr rfl), equal, rfl, {env g, v},
      ZFSet.mem_pair.2 (Or.inr rfl), v, ZFSet.mem_pair.2 (Or.inr rfl), rfl, rfl⟩
    · rw [equal]
      exact ZFSet.mem_pair.2 (Or.inl rfl)
    · rw [equal]
      exact ZFSet.mem_pair.2 (Or.inr rfl)






def binaryRelationFormula {n} (g f : Fin n) : BoundedFormula n :=
  .allMem f (exMem g.succ (exMem g.succ.succ
    (exMem g.succ.succ.succ (orderedTripleFormula 3 2 1 0))))

def binaryFunctionFormula {n} (g f : Fin n) : BoundedFormula n :=
  .conj (binaryRelationFormula g f) (.allMem g (.allMem g.succ
    (exMem g.succ.succ (.conj (tripleMembershipFormula 2 1 0 f.succ.succ.succ)
      (.allMem g.succ.succ.succ (imp
        (tripleMembershipFormula 3 2 0 f.succ.succ.succ.succ) (.equal 0 1)))))))

theorem truth_binaryRelationFormula {n} (g f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (binaryRelationFormula g f) env ↔
      env f ⊆ ZFSet.prod (ZFSet.prod (env g) (env g)) (env g) := by
  simp only [binaryRelationFormula, Truth, truth_exMem, truth_orderedTripleFormula]
  constructor
  · intro h w hw
    obtain ⟨x, hx, y, hy, z, hz, eq⟩ := h w hw
    exact ZFSet.mem_prod.2 ⟨ZFSet.pair x y, ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, z, hz, eq⟩
  · intro h w hw
    obtain ⟨xy, hxy, z, hz, eq⟩ := ZFSet.mem_prod.1 (h hw)
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    exact ⟨x, hx, y, hy, z, hz, eq⟩

theorem truth_binaryFunctionFormula {n} (g f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (binaryFunctionFormula g f) env ↔
      ZFSet.IsFunc (ZFSet.prod (env g) (env g)) (env g) (env f) := by
  simp only [binaryFunctionFormula, Truth, truth_binaryRelationFormula, truth_exMem,
    truth_tripleMembershipFormula, truth_imp]
  constructor
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro xy hxy
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    obtain ⟨z, _, rel, unique⟩ := total x hx y hy
    refine ⟨z, rel, ?_⟩
    intro w hw
    exact unique w (ZFSet.pair_mem_prod.1 (shape hw)).2 hw
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro x hx y hy
    obtain ⟨z, rel, unique⟩ := total (ZFSet.pair x y) (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
    exact ⟨z, (ZFSet.pair_mem_prod.1 (shape rel)).2, rel, fun w _ hw => unique w hw⟩

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing

universe u

structure GroupCode (G m i e : ZFSet.{u}) : Prop where
  mul_function : ZFSet.IsFunc (ZFSet.prod G G) G m
  inv_function : ZFSet.IsFunc G G i
  identity_mem : e ∈ G
  one_mul : ∀ x ∈ G, ZFSet.pair (ZFSet.pair e x) x ∈ m
  mul_one : ∀ x ∈ G, ZFSet.pair (ZFSet.pair x e) x ∈ m
  inv_mul : ∀ x ∈ G, ∀ y ∈ G, ZFSet.pair x y ∈ i → ZFSet.pair (ZFSet.pair y x) e ∈ m
  mul_assoc : ∀ x ∈ G, ∀ y ∈ G, ∀ z ∈ G, ∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G,
    ZFSet.pair (ZFSet.pair x y) a ∈ m → ZFSet.pair (ZFSet.pair y z) b ∈ m →
    ZFSet.pair (ZFSet.pair a z) c ∈ m → ZFSet.pair (ZFSet.pair x b) c ∈ m

namespace BoundedFormula

open SetFormula

def groupIdentityFormula {n} (g m e : Fin n) : BoundedFormula n :=
  .allMem g (.conj (tripleMembershipFormula e.succ 0 0 m.succ)
    (tripleMembershipFormula 0 e.succ 0 m.succ))

def groupInverseFormula {n} (g m i e : Fin n) : BoundedFormula n :=
  .allMem g (.allMem g.succ (imp (pairMembershipFormula 1 0 i.succ.succ)
    (tripleMembershipFormula 0 1 e.succ.succ m.succ.succ)))

def groupAssociativeFormula {n} (g m : Fin n) : BoundedFormula n :=
  .allMem g (.allMem g.succ (.allMem g.succ.succ (.allMem g.succ.succ.succ
    (.allMem g.succ.succ.succ.succ (.allMem g.succ.succ.succ.succ.succ
      (imp (.conj (tripleMembershipFormula 5 4 2 m.succ.succ.succ.succ.succ.succ)
        (.conj (tripleMembershipFormula 4 3 1 m.succ.succ.succ.succ.succ.succ)
          (tripleMembershipFormula 2 3 0 m.succ.succ.succ.succ.succ.succ)))
        (tripleMembershipFormula 5 1 0 m.succ.succ.succ.succ.succ.succ)))))))

def groupFormula {n} (g m i e : Fin n) : BoundedFormula n :=
  .conj (binaryFunctionFormula g m) (.conj (functionFormula g g i)
    (.conj (.mem e g) (.conj (groupIdentityFormula g m e)
      (.conj (groupInverseFormula g m i e) (groupAssociativeFormula g m)))))

theorem truth_groupFormula {n} (g m i e : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (groupFormula g m i e) env ↔ GroupCode (env g) (env m) (env i) (env e) := by
  simp only [groupFormula, Truth, truth_binaryFunctionFormula, truth_functionFormula,
    groupIdentityFormula, groupInverseFormula, groupAssociativeFormula,
    truth_tripleMembershipFormula, truth_pairMembershipFormula, truth_imp]
  constructor
  · rintro ⟨mul, inv, one, identity, inverse, assoc⟩
    exact ⟨mul, inv, one, fun x hx => (identity x hx).1,
      fun x hx => (identity x hx).2, inverse,
      fun x hx y hy z hz a ha b hb c hc xy yz az => assoc x hx y hy z hz a ha b hb c hc ⟨xy, yz, az⟩⟩
  · intro h
    exact ⟨h.mul_function, h.inv_function, h.identity_mem,
      fun x hx => ⟨h.one_mul x hx, h.mul_one x hx⟩, h.inv_mul,
      fun x hx y hy z hz a ha b hb c hc ⟨xy, yz, az⟩ => h.mul_assoc x hx y hy z hz a ha b hb c hc xy yz az⟩

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_groupCode {G m i e : ZFSet.{u}}
    (hG : G ∈ M.sets) (hm : m ∈ M.sets) (hi : i ∈ M.sets) (he : e ∈ M.sets) :
    Realize M.sets (BoundedFormula.groupFormula 0 1 2 3).toFormula
      (extend G (extend m (extend i (extend e Fin.elim0)))) ↔ GroupCode G m i e :=
  (BoundedFormula.realize_toFormula M _ _
    (Fin.cases hG (Fin.cases hm (Fin.cases hi (Fin.cases he (fun j => Fin.elim0 j)))))).trans
      (BoundedFormula.truth_groupFormula 0 1 2 3 _)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.SetRealization.Presentation
open Forcing
universe u
variable {G : Type u} [Group G] (s : Presentation G)

theorem groupCode : GroupCode s.carrier
    ((s.product s).graph s (fun xy => xy.1 * xy.2))
    (s.graph s (fun x => x⁻¹)) (s.encode 1) := by
  refine ⟨(s.product s).graph_isFunc s _, s.graph_isFunc s _, s.encode_mem 1, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    exact ((s.product s).pair_mem_graph s _ (1, a) a).2 (one_mul a)
  · intro x hx
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    exact ((s.product s).pair_mem_graph s _ (a, 1) a).2 (mul_one a)
  · intro x hx y hy entry
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (s.mem_carrier y).1 hy
    have inverse := (s.pair_mem_graph s _ a b).1 entry
    apply ((s.product s).pair_mem_graph s _ (b, a) 1).2
    rw [← inverse, inv_mul_cancel]
  · intro x hx y hy z hz a ha b hb c hc xy yz az
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    obtain ⟨z, rfl⟩ := (s.mem_carrier z).1 hz
    obtain ⟨a, rfl⟩ := (s.mem_carrier a).1 ha
    obtain ⟨b, rfl⟩ := (s.mem_carrier b).1 hb
    obtain ⟨c, rfl⟩ := (s.mem_carrier c).1 hc
    have first := ((s.product s).pair_mem_graph s _ (x, y) a).1 xy
    have second := ((s.product s).pair_mem_graph s _ (y, z) b).1 yz
    have third := ((s.product s).pair_mem_graph s _ (a, z) c).1 az
    apply ((s.product s).pair_mem_graph s _ (x, b) c).2
    rw [← second, ← mul_assoc, first, third]

end PartitionPilot.SetRealization.Presentation

end OAI
