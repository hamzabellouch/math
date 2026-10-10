import OAI.SetTheory.PartitionPrinciple.Forcing.NameRenameSteps

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

def orientedPairFormula {n : Nat} (reverse : Bool) (x y r : Fin n) : SetFormula n :=
  if reverse then pairMembershipFormula y x r else pairMembershipFormula x y r

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_orientedPairFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (reverse : Bool) (x y r : Fin n) (env : Fin n → ZFSet.{u})
    (hx : env x ∈ M.sets) (hy : env y ∈ M.sets) (hr : env r ∈ M.sets) :
    Realize M.sets (orientedPairFormula reverse x y r) env ↔
      if reverse then ZFSet.pair (env y) (env x) ∈ env r else ZFSet.pair (env x) (env y) ∈ env r := by
  cases reverse
  · exact M.realize_pairMembershipFormula pairing x y r env hx hy hr
  · exact M.realize_pairMembershipFormula pairing y x r env hy hx hr

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.SetFormula

def renameMatchFormula {n : Nat} (reverse : Bool) (c f r x y : Fin n) : SetFormula n :=
  .all (allConditions c.succ (imp (pairMembershipFormula 1 0 x.succ.succ)
    (ex (exConditions c.succ.succ.succ
      (.conj (pairMembershipFormula 1 0 y.succ.succ.succ.succ)
        (.conj (orientedPairFormula reverse 2 0 f.succ.succ.succ.succ)
          (orientedPairFormula reverse 3 1 r.succ.succ.succ.succ)))))))

def renameStepFormula {n : Nat} (c f r x y : Fin n) : SetFormula n :=
  .conj (renameMatchFormula false c f r x y) (renameMatchFormula true c f r y x)

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

def RawRenameMatch (reverse : Bool) (f : P → P) (R x y : ZFSet.{u}) : Prop :=
  ∀ v ∈ M.sets, ∀ p, ZFSet.pair v (s.encode p) ∈ x →
    ∃ w ∈ M.sets, ∃ q, ZFSet.pair w (s.encode q) ∈ y ∧
      (if reverse then f q = p else f p = q) ∧
      (if reverse then ZFSet.pair w v ∈ R else ZFSet.pair v w ∈ R)

def RawRenameStep (f : P → P) (R x y : ZFSet.{u}) : Prop :=
  M.RawRenameMatch s false f R x y ∧ M.RawRenameMatch s true f R y x

theorem rawRenameStep_mono (f : P → P) {R S x y : ZFSet.{u}} (sub : R ⊆ S)
    (h : M.RawRenameStep s f R x y) : M.RawRenameStep s f S x y := by
  constructor
  · intro v hv p entry
    obtain ⟨w, hw, q, matched, cond, rel⟩ := h.1 v hv p entry
    exact ⟨w, hw, q, matched, cond, sub rel⟩
  · intro w hw q entry
    obtain ⟨v, hv, p, matched, cond, rel⟩ := h.2 w hw q entry
    exact ⟨v, hv, p, matched, cond, sub rel⟩

theorem realize_orientedMapFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    {n : Nat} (reverse : Bool) (i j k : Fin n) (env : Fin n → ZFSet.{u}) (p q : P)
    (hi : env i = s.encode p) (hj : env j = s.encode q) (hk : env k = s.graph s f) :
    Realize M.sets (orientedPairFormula reverse i j k) env ↔
      if reverse then f q = p else f p = q := by
  rw [M.realize_orientedPairFormula pairing reverse i j k env
    (hi ▸ M.transitive carrier (s.encode_mem p)) (hj ▸ M.transitive carrier (s.encode_mem q))
    (hk ▸ graph), hi, hj, hk]
  cases reverse
  · exact s.pair_mem_graph s f p q
  · exact s.pair_mem_graph s f q p

theorem realize_renameMatchFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    {n : Nat} (reverse : Bool) (c g r x y : Fin n) (env : Fin n → ZFSet.{u})
    (hc : env c = s.carrier) (hg : env g = s.graph s f)
    (hr : env r ∈ M.sets) (hx : env x ∈ M.sets) (hy : env y ∈ M.sets) :
    Realize M.sets (renameMatchFormula reverse c g r x y) env ↔
      M.RawRenameMatch s reverse f (env r) (env x) (env y) := by
  change (∀ v ∈ M.sets, Realize M.sets _ (extend v env)) ↔ _
  apply forall_congr'
  intro v
  apply forall_congr'
  intro hv
  rw [M.realize_allConditions s c.succ _ (extend v env) carrier hc]
  apply forall_congr'
  intro p
  rw [realize_imp, M.realize_pairMembershipFormula pairing 1 0 x.succ.succ
    (extend (s.encode p) (extend v env)) hv (M.transitive carrier (s.encode_mem p)) hx]
  apply forall_congr'
  intro _
  rw [realize_ex]
  apply exists_congr
  intro w
  apply and_congr_right
  intro hw
  rw [M.realize_exConditions s c.succ.succ.succ _ (extend w (extend (s.encode p) (extend v env)))
    carrier hc]
  apply exists_congr
  intro q
  let e := extend (s.encode q) (extend w (extend (s.encode p) (extend v env)))
  change (Realize M.sets _ e ∧ Realize M.sets _ e ∧ Realize M.sets _ e) ↔ _
  rw [M.realize_pairMembershipFormula pairing 1 0 y.succ.succ.succ.succ e hw
    (M.transitive carrier (s.encode_mem q)) hy,
    M.realize_orientedMapFormula s pairing carrier f graph reverse 2 0 g.succ.succ.succ.succ e p q rfl rfl hg,
    M.realize_orientedPairFormula pairing reverse 3 1 r.succ.succ.succ.succ e hv hw hr]
  rfl

theorem realize_renameStepFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    {n : Nat} (c g r x y : Fin n) (env : Fin n → ZFSet.{u})
    (hc : env c = s.carrier) (hg : env g = s.graph s f)
    (hr : env r ∈ M.sets) (hx : env x ∈ M.sets) (hy : env y ∈ M.sets) :
    Realize M.sets (renameStepFormula c g r x y) env ↔
      M.RawRenameStep s f (env r) (env x) (env y) := by
  change (Realize M.sets _ env ∧ Realize M.sets _ env) ↔ _
  rw [M.realize_renameMatchFormula s pairing carrier f graph false c g r x y env hc hg hr hx hy,
    M.realize_renameMatchFormula s pairing carrier f graph true c g r y x env hc hg hr hy hx]
  rfl

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
