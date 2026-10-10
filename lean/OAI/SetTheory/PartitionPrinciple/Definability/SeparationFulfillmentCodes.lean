import OAI.SetTheory.PartitionPrinciple.Definability.PresentedGroupCodes

namespace OAI


namespace PartitionPilot.Forcing

namespace BoundedFormula

open SetFormula
universe u

def productRelationFormula {n} (a b c f : Fin n) : BoundedFormula n :=
  .allMem f (exMem a.succ (exMem b.succ.succ
    (exMem c.succ.succ.succ (orderedTripleFormula 3 2 1 0))))

def productFunctionFormula {n} (a b c f : Fin n) : BoundedFormula n :=
  .conj (productRelationFormula a b c f) (.allMem a (.allMem b.succ
    (exMem c.succ.succ (.conj (tripleMembershipFormula 2 1 0 f.succ.succ.succ)
      (.allMem c.succ.succ.succ (imp
        (tripleMembershipFormula 3 2 0 f.succ.succ.succ.succ) (.equal 0 1)))))))

theorem truth_productRelationFormula {n} (a b c f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (productRelationFormula a b c f) env ↔
      env f ⊆ ZFSet.prod (ZFSet.prod (env a) (env b)) (env c) := by
  simp only [productRelationFormula, Truth, truth_exMem, truth_orderedTripleFormula]
  constructor
  · intro h w hw
    obtain ⟨x, hx, y, hy, z, hz, eq⟩ := h w hw
    exact ZFSet.mem_prod.2 ⟨ZFSet.pair x y, ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, z, hz, eq⟩
  · intro h w hw
    obtain ⟨xy, hxy, z, hz, eq⟩ := ZFSet.mem_prod.1 (h hw)
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    exact ⟨x, hx, y, hy, z, hz, eq⟩

theorem truth_productFunctionFormula {n} (a b c f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (productFunctionFormula a b c f) env ↔
      ZFSet.IsFunc (ZFSet.prod (env a) (env b)) (env c) (env f) := by
  simp only [productFunctionFormula, Truth, truth_productRelationFormula, truth_exMem,
    truth_tripleMembershipFormula, truth_imp]
  constructor
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro xy hxy
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    obtain ⟨z, _, rel, unique⟩ := total x hx y hy
    exact ⟨z, rel, fun w hw => unique w (ZFSet.pair_mem_prod.1 (shape hw)).2 hw⟩
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro x hx y hy
    obtain ⟨z, rel, unique⟩ := total (ZFSet.pair x y) (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
    exact ⟨z, (ZFSet.pair_mem_prod.1 (shape rel)).2, rel, fun w _ hw => unique w hw⟩

end BoundedFormula




universe u

structure PosetActionCode (G P m e R A : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc (ZFSet.prod G P) P A
  one : ∀ p ∈ P, ZFSet.pair (ZFSet.pair e p) p ∈ A
  mul : ∀ g ∈ G, ∀ h ∈ G, ∀ k ∈ G, ∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P,
    ZFSet.pair (ZFSet.pair g h) k ∈ m → ZFSet.pair (ZFSet.pair h p) q ∈ A →
    ZFSet.pair (ZFSet.pair g q) r ∈ A → ZFSet.pair (ZFSet.pair k p) r ∈ A
  monotone : ∀ g ∈ G, ∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P, ∀ s ∈ P,
    ZFSet.pair (ZFSet.pair g p) r ∈ A → ZFSet.pair (ZFSet.pair g q) s ∈ A →
    ZFSet.pair p q ∈ R → ZFSet.pair r s ∈ R

namespace BoundedFormula

open SetFormula

def actionOneFormula {n} (p e a : Fin n) : BoundedFormula n :=
  .allMem p (tripleMembershipFormula e.succ 0 0 a.succ)

def actionMulFormula {n} (g p m a : Fin n) : BoundedFormula n :=
  .allMem g (.allMem g.succ (.allMem g.succ.succ (.allMem p.succ.succ.succ
    (.allMem p.succ.succ.succ.succ (.allMem p.succ.succ.succ.succ.succ
      (imp (.conj (tripleMembershipFormula 5 4 3 m.succ.succ.succ.succ.succ.succ)
        (.conj (tripleMembershipFormula 4 2 1 a.succ.succ.succ.succ.succ.succ)
          (tripleMembershipFormula 5 1 0 a.succ.succ.succ.succ.succ.succ)))
        (tripleMembershipFormula 3 2 0 a.succ.succ.succ.succ.succ.succ)))))))

def actionMonotoneFormula {n} (g p r a : Fin n) : BoundedFormula n :=
  .allMem g (.allMem p.succ (.allMem p.succ.succ (.allMem p.succ.succ.succ
    (.allMem p.succ.succ.succ.succ
      (imp (.conj (tripleMembershipFormula 4 3 1 a.succ.succ.succ.succ.succ)
        (.conj (tripleMembershipFormula 4 2 0 a.succ.succ.succ.succ.succ)
          (pairMembershipFormula 3 2 r.succ.succ.succ.succ.succ)))
        (pairMembershipFormula 1 0 r.succ.succ.succ.succ.succ))))))

def posetActionFormula {n} (g p m e r a : Fin n) : BoundedFormula n :=
  .conj (productFunctionFormula g p p a) (.conj (actionOneFormula p e a)
    (.conj (actionMulFormula g p m a) (actionMonotoneFormula g p r a)))

theorem truth_posetActionFormula {n} (g p m e r a : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (posetActionFormula g p m e r a) env ↔
      PosetActionCode (env g) (env p) (env m) (env e) (env r) (env a) := by
  simp only [posetActionFormula, Truth, truth_productFunctionFormula, actionOneFormula,
    actionMulFormula, actionMonotoneFormula, truth_tripleMembershipFormula,
    truth_pairMembershipFormula, truth_imp]
  constructor
  · rintro ⟨function, one, mul, monotone⟩
    exact ⟨function, one,
      fun g hg h hh k hk p hp q hq r hr gh hpq gr => mul g hg h hh k hk p hp q hq r hr ⟨gh, hpq, gr⟩,
      fun g hg p hp q hq r hr s hs gr gs pq => monotone g hg p hp q hq r hr s hs ⟨gr, gs, pq⟩⟩
  · intro h
    exact ⟨h.function, h.one,
      fun g hg j hj k hk p hp q hq r hr ⟨gj, jq, gr⟩ => h.mul g hg j hj k hk p hp q hq r hr gj jq gr,
      fun g hg p hp q hq r hr s hs ⟨gr, gs, pq⟩ => h.monotone g hg p hp q hq r hr s hs gr gs pq⟩

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_posetActionCode {G P m e R A : ZFSet.{u}}
    (hG : G ∈ M.sets) (hP : P ∈ M.sets) (hm : m ∈ M.sets)
    (he : e ∈ M.sets) (hR : R ∈ M.sets) (hA : A ∈ M.sets) :
    Realize M.sets (BoundedFormula.posetActionFormula 0 1 2 3 4 5).toFormula
      (extend G (extend P (extend m (extend e (extend R (extend A Fin.elim0)))))) ↔
        PosetActionCode G P m e R A :=
  (BoundedFormula.realize_toFormula M _ _ (Fin.cases hG (Fin.cases hP (Fin.cases hm
    (Fin.cases he (Fin.cases hR (Fin.cases hA (fun j => Fin.elim0 j)))))))).trans
      (BoundedFormula.truth_posetActionFormula 0 1 2 3 4 5 _)

end TransitiveGround





def SeparationActorCode (P r Q R ν A e W k : ZFSet.{u}) : Prop :=
  ∀ w ∈ Q, ZFSet.pair W w ∈ e →
    (∀ z ∈ Q, ZFSet.pair z w ∈ R → ZFSet.pair (ZFSet.pair k z) z ∈ A) ∧
    ∀ x ∈ P, ∀ y ∈ P, ∀ x' ∈ Q, ∀ y' ∈ Q, ∀ z ∈ Q,
      ZFSet.pair W x ∈ r → ZFSet.pair W y ∈ r →
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e →
      ZFSet.pair (ZFSet.pair k x') z ∈ A → ZFSet.pair (ZFSet.pair z y') w ∈ ν

def SeparationFulfillmentCode (P r Q R ν H A e : ZFSet.{u}) : Prop :=
  ∀ W ∈ P, ∃ k ∈ H, SeparationActorCode P r Q R ν A e W k

namespace BoundedFormula

def separationActorFormula {n} (P r Q R ν A e W k : Fin n) : BoundedFormula n :=
  .allMem Q (imp (pairMembershipFormula W.succ 0 e.succ)
    (.conj
      (.allMem Q.succ (imp (pairMembershipFormula 0 1 R.succ.succ)
        (tripleMembershipFormula k.succ.succ 0 0 A.succ.succ)))
      (.allMem P.succ (.allMem P.succ.succ (.allMem Q.succ.succ.succ
        (.allMem Q.succ.succ.succ.succ (.allMem Q.succ.succ.succ.succ.succ
          (imp (pairMembershipFormula W.succ.succ.succ.succ.succ.succ 4 r.succ.succ.succ.succ.succ.succ)
            (imp (pairMembershipFormula W.succ.succ.succ.succ.succ.succ 3 r.succ.succ.succ.succ.succ.succ)
              (imp (pairMembershipFormula 4 2 e.succ.succ.succ.succ.succ.succ)
                (imp (pairMembershipFormula 3 1 e.succ.succ.succ.succ.succ.succ)
                  (imp (tripleMembershipFormula k.succ.succ.succ.succ.succ.succ 2 0 A.succ.succ.succ.succ.succ.succ)
                    (tripleMembershipFormula 0 1 5 ν.succ.succ.succ.succ.succ.succ)))))))))))))

theorem truth_separationActorFormula {n} (P r Q R ν A e W k : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (separationActorFormula P r Q R ν A e W k) env ↔
      SeparationActorCode (env P) (env r) (env Q) (env R) (env ν) (env A) (env e) (env W) (env k) := by
  simp only [separationActorFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula]
  rfl

def separationFulfillmentFormula {n} (P r Q R ν H A e : Fin n) : BoundedFormula n :=
  .allMem P (.exMem H.succ (separationActorFormula P.succ.succ r.succ.succ Q.succ.succ
    R.succ.succ ν.succ.succ A.succ.succ e.succ.succ 1 0))

theorem truth_separationFulfillmentFormula {n} (P r Q R ν H A e : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (separationFulfillmentFormula P r Q R ν H A e) env ↔
      SeparationFulfillmentCode (env P) (env r) (env Q) (env R) (env ν) (env H) (env A) (env e) := by
  simp only [separationFulfillmentFormula, Truth, truth_exMem, truth_separationActorFormula]
  rfl

theorem realize_separationFulfillmentFormula (M : TransitiveGround.{u}) {n}
    (P r Q R ν H A e : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    SetFormula.Realize M.sets (separationFulfillmentFormula P r Q R ν H A e).toFormula env ↔
      SeparationFulfillmentCode (env P) (env r) (env Q) (env R) (env ν) (env H) (env A) (env e) :=
  (realize_toFormula M _ env members).trans (truth_separationFulfillmentFormula P r Q R ν H A e env)

end BoundedFormula


end PartitionPilot.Forcing

end OAI
