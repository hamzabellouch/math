import OAI.SetTheory.PartitionPrinciple.Forcing.GroundSymmetricPowerSet

namespace OAI


namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} (s : Presentation P)

theorem mem_check_code (one : P) (x z : ZFSet.{u}) :
    z ∈ (check s one x).val ↔ ∃ y ∈ x, z = ZFSet.pair (check s one y).val (s.encode one) := by
  rw [check]
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨y, eq⟩
    exact ⟨y.val, y.property, eq.symm⟩
  · rintro ⟨y, hy, eq⟩
    exact ⟨⟨y, hy⟩, eq.symm⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.SetFormula

def checkStepFormula {n : Nat} (top r x y : Fin n) : SetFormula n :=
  .conj
    (.all (imp (.mem 0 x.succ) (ex (.conj (pairMembershipFormula 1 0 r.succ.succ)
      (pairMembershipFormula 0 top.succ.succ y.succ.succ)))))
    (.all (imp (.mem 0 y.succ) (ex (ex (.conj (.mem 1 x.succ.succ.succ)
      (.conj (pairMembershipFormula 1 0 r.succ.succ.succ)
        (orderedPairFormula 2 0 top.succ.succ.succ)))))))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

def RawCheckStep (top R x y : ZFSet.{u}) : Prop :=
  (∀ v ∈ x, ∃ w ∈ M.sets, ZFSet.pair v w ∈ R ∧ ZFSet.pair w top ∈ y) ∧
  (∀ z ∈ y, ∃ v ∈ x, ∃ w ∈ M.sets, ZFSet.pair v w ∈ R ∧ z = ZFSet.pair w top)

theorem rawCheckStep_mono {top R S x y : ZFSet.{u}} (sub : R ⊆ S)
    (h : M.RawCheckStep top R x y) : M.RawCheckStep top S x y := by
  constructor
  · intro v hv
    obtain ⟨w, hw, rel, entry⟩ := h.1 v hv
    exact ⟨w, hw, sub rel, entry⟩
  · intro z hz
    obtain ⟨v, hv, w, hw, rel, eq⟩ := h.2 z hz
    exact ⟨v, hv, w, hw, sub rel, eq⟩

theorem realize_checkStepFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (top r x y : Fin n) (env : Fin n → ZFSet.{u})
    (htop : env top ∈ M.sets) (hr : env r ∈ M.sets)
    (hx : env x ∈ M.sets) (hy : env y ∈ M.sets) :
    Realize M.sets (checkStepFormula top r x y) env ↔
      M.RawCheckStep (env top) (env r) (env x) (env y) := by
  change (Realize M.sets _ env ∧ Realize M.sets _ env) ↔ _
  constructor
  · rintro ⟨forward, backward⟩
    constructor
    · intro v hv
      have step := (realize_imp M.sets _ _ _).1 (forward v (M.transitive hx hv)) hv
      obtain ⟨w, hw, rel, entry⟩ := (realize_ex M.sets _ _).1 step
      let e := extend w (extend v env)
      exact ⟨w, hw,
        (M.realize_pairMembershipFormula pairing 1 0 r.succ.succ e (M.transitive hx hv) hw hr).1 rel,
        (M.realize_pairMembershipFormula pairing 0 top.succ.succ y.succ.succ e hw htop hy).1 entry⟩
    · intro z hz
      have step := (realize_imp M.sets _ _ _).1 (backward z (M.transitive hy hz)) hz
      obtain ⟨v, hv, step⟩ := (realize_ex M.sets _ _).1 step
      obtain ⟨w, hw, member, rel, shape⟩ := (realize_ex M.sets _ _).1 step
      let e := extend w (extend v (extend z env))
      exact ⟨v, member, w, hw,
        (M.realize_pairMembershipFormula pairing 1 0 r.succ.succ.succ e hv hw hr).1 rel,
        (M.realize_orderedPairFormula pairing 2 0 top.succ.succ.succ e (M.transitive hy hz) hw htop).1 shape⟩
  · rintro ⟨forward, backward⟩
    constructor
    · intro v hv
      rw [realize_imp]
      intro member
      obtain ⟨w, hw, rel, entry⟩ := forward v member
      rw [realize_ex]
      let e := extend w (extend v env)
      exact ⟨w, hw,
        (M.realize_pairMembershipFormula pairing 1 0 r.succ.succ e hv hw hr).2 rel,
        (M.realize_pairMembershipFormula pairing 0 top.succ.succ y.succ.succ e hw htop hy).2 entry⟩
    · intro z hz
      rw [realize_imp]
      intro member
      obtain ⟨v, hv, w, hw, rel, shape⟩ := backward z member
      rw [realize_ex]
      refine ⟨v, M.transitive hx hv, ?_⟩
      rw [realize_ex]
      let e := extend w (extend v (extend z env))
      exact ⟨w, hw, hv,
        (M.realize_pairMembershipFormula pairing 1 0 r.succ.succ.succ e (M.transitive hx hv) hw hr).2 rel,
        (M.realize_orderedPairFormula pairing 2 0 top.succ.succ.succ e hz hw htop).2 shape⟩

theorem rawCheckStep_eq {P : Type u} (s : Presentation P) (one : P) {R x y : ZFSet.{u}}
    (step : M.RawCheckStep (s.encode one) R x y)
    (children : ∀ v ∈ x, ∀ w ∈ M.sets, ZFSet.pair v w ∈ R → w = (Name.check s one v).val) :
    y = (Name.check s one x).val := by
  apply ZFSet.ext
  intro z
  rw [Name.mem_check_code]
  constructor
  · intro hz
    obtain ⟨v, hv, w, hw, rel, eq⟩ := step.2 z hz
    exact ⟨v, hv, eq.trans (congrArg (fun q => ZFSet.pair q (s.encode one)) (children v hv w hw rel))⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨w, hw, rel, entry⟩ := step.1 v hv
    rwa [children v hv w hw rel] at entry

end PartitionPilot.Forcing.TransitiveGround

end OAI
