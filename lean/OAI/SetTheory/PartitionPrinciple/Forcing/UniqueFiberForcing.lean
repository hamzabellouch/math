import OAI.SetTheory.PartitionPrinciple.Definability.ParentSupportCodes

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def uniqueFiberFormula {n} (s x f : Fin n) : BoundedFormula n :=
  .conj (.mem x s) (.conj (pairMembershipFormula s x f)
    (.allMem s (imp (pairMembershipFormula s.succ 0 f.succ) (.equal 0 x.succ))))

theorem truth_uniqueFiberFormula {n} (s x f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (uniqueFiberFormula s x f) env ↔ env x ∈ env s ∧
      ZFSet.pair (env s) (env x) ∈ env f ∧
      ∀ z ∈ env s, ZFSet.pair (env s) z ∈ env f → z = env x := by
  simp only [uniqueFiberFormula, Truth, truth_pairMembershipFormula, truth_imp]
  rfl

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.SetFormula

open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem realize_uniqueFiber_values (D : Name.NameDomain s) (H : Set P)
    {n} (i j k : Fin n) (env : Assignment D n) :
    Realize (D.values H) (BoundedFormula.uniqueFiberFormula i j k).toFormula (evalAssignment H env) ↔
      Name.eval H (env j).val ∈ Name.eval H (env i).val ∧
      ZFSet.pair (Name.eval H (env i).val) (Name.eval H (env j).val) ∈ Name.eval H (env k).val ∧
      ∀ z ∈ Name.eval H (env i).val,
        ZFSet.pair (Name.eval H (env i).val) z ∈ Name.eval H (env k).val →
          z = Name.eval H (env j).val := by
  let N : TransitiveGround := ⟨D.values H, D.values_transitive H⟩
  exact (BoundedFormula.realize_toFormula N _ _ (fun l => ⟨env l, rfl⟩)).trans
    (BoundedFormula.truth_uniqueFiberFormula i j k (evalAssignment H env))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.PosetAction

open SetRealization SetFormula
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]

theorem uniqueFiber_eq_of_fixed_names (a : PosetAction G P) (s : Presentation P)
    (D : Name.NameDomain s) (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (g : G) (S x f : D.names)
    (fixedS : a.act s g S.val = S.val) (fixedF : a.act s g f.val = f.val)
    (p : P)
    (forced : Forces D (BoundedFormula.uniqueFiberFormula 0 1 2).toFormula
      (extend S (extend x (extend f Fin.elim0))) p)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily D))
    (hp : H.mem p) (hgp : H.mem (a.iso g p)) :
    Name.eval {q | H.mem q} x.val = Name.eval {q | H.mem q} (a.act s g x.val) := by
  let env := extend S (extend x (extend f Fin.elim0))
  have original := (realize_uniqueFiber_values D {q | H.mem q} 0 1 2 env).1
    (forces_sound D H generic _ env hp forced)
  have moved := (a.formula_forces_act_iff s D closed g
    (BoundedFormula.uniqueFiberFormula 0 1 2).toFormula env p).2 forced
  have translated := (realize_uniqueFiber_values D {q | H.mem q} 0 1 2
    (a.actAssignment s D closed g env)).1
    (forces_sound D H generic _ _ hgp moved)
  change Name.eval {q | H.mem q} (a.act s g x.val) ∈ Name.eval {q | H.mem q} (a.act s g S.val) ∧
    ZFSet.pair (Name.eval {q | H.mem q} (a.act s g S.val))
      (Name.eval {q | H.mem q} (a.act s g x.val)) ∈ Name.eval {q | H.mem q} (a.act s g f.val) ∧ _
    at translated
  rw [fixedS, fixedF] at translated
  exact (original.2.2 _ translated.1 translated.2.1).symm

end PartitionPilot.Forcing.PosetAction

end

end OAI
