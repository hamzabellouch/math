import OAI.SetTheory.PartitionPrinciple.Transfinite.RecursiveStateFieldEnvironments

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundDefinableFunction

def congr {M : TransitiveGround.{u}} {n : Nat}
    {f g : (Fin n → ZFSet.{u}) → ZFSet.{u}} (definition : GroundDefinableFunction M f)
    (equal : ∀ env, f env = g env) : GroundDefinableFunction M g where
  formula := definition.formula
  closed := fun env members => equal env ▸ definition.closed env members
  correct := by
    intro env members z hz
    rw [definition.correct env members z hz, equal env]

end GroundDefinableFunction

structure GroundSetTerm (M : TransitiveGround.{u}) (n : Nat) where
  eval : (Fin n → ZFSet.{u}) → ZFSet.{u}
  definition : GroundDefinableFunction M eval

namespace GroundSetTerm

def var (M : TransitiveGround.{u}) {n : Nat} (j : Fin n) : GroundSetTerm M n :=
  ⟨fun env => env j, GroundDefinableFunction.projection M j⟩

def app {M : TransitiveGround.{u}} {n k : Nat}
    {f : (Fin k → ZFSet.{u}) → ZFSet.{u}}
    (operation : GroundDefinableFunction M f) (args : Fin k → GroundSetTerm M n) :
    GroundSetTerm M n :=
  ⟨fun env => f (fun i => (args i).eval env),
    operation.comp (fun i => (args i).definition)⟩

theorem ground {M : TransitiveGround.{u}} {n : Nat} (term : GroundSetTerm M n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) : term.eval env ∈ M.sets :=
  term.definition.closed env members

theorem correct {M : TransitiveGround.{u}} {n : Nat} (term : GroundSetTerm M n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets term.definition.formula (extend z env) ↔ z = term.eval env :=
  term.definition.correct env members z hz

end GroundSetTerm

namespace TransitiveGround

noncomputable def definable_nonemptyTuple (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (k : Nat) :
    GroundDefinableFunction M (fun env : Fin (k + 1) → ZFSet.{u} => nonemptyTupleCode k env) where
  formula := (BoundedFormula.nonemptyTupleFormula k 0 Fin.succ).toFormula
  closed := fun env members => M.nonemptyTupleCode_mem pairing k env members
  correct := by
    intro env members z hz
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members),
      BoundedFormula.truth_nonemptyTupleFormula]
    rfl

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_relationProduct :
    GroundDefinableFunction M (fun env : Fin 6 → ZFSet.{u} =>
      relationProduct (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) := by
  let v := GroundSetTerm.var M (n := 6)
  let product (x y : GroundSetTerm M 6) :=
    GroundSetTerm.app (M.definable_product pairing unions powers separation) ![x,y]
  let bound := product (product (v 0) (v 1)) (product (v 2) (v 3))
  let formula : SetFormula 7 := (BoundedFormula.relationProductEntryFormula 0 1 2 3 4 5 6).toFormula
  let term := GroundSetTerm.app (M.definable_separation separation formula)
    ![bound,v 0,v 1,v 2,v 3,v 4,v 5]
  refine { formula := term.definition.formula
           closed := fun env members => M.relationProduct_mem pairing unions powers separation
             (members 0) (members 1) (members 2) (members 3) (members 4) (members 5)
           correct := ?_ }
  intro env members z hz
  rw [term.definition.correct env members z hz]
  have args : (fun j : Fin 6 => (![bound,v 0,v 1,v 2,v 3,v 4,v 5] j.succ).eval env) = env := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) j
  have equal : term.eval env = relationProduct (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) := by
    change ZFSet.sep (fun w => Realize M.sets formula (extend w _)) _ = _
    rw [args]
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_sep, relationProduct, ZFSet.mem_sep]
    apply and_congr_right
    intro hw
    rw [BoundedFormula.realize_toFormula M _ _
      (Fin.cases (M.transitive (bound.ground env members) hw) members),
      BoundedFormula.truth_relationProductEntryFormula]
    rfl
  rw [equal]

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
