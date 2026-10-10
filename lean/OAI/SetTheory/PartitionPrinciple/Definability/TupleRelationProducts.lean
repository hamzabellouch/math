import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCountableProducts

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def tupleRelationBound : (k : Nat) → (Fin (k + 1) → ZFSet.{u}) → ZFSet.{u}
  | 0, f => ⋃₀ ⋃₀ f 0
  | k + 1, f => ZFSet.prod (⋃₀ ⋃₀ f 0) (tupleRelationBound k (fun j => f j.succ))

noncomputable def tupleRelationProduct : (k : Nat) → (Fin (k + 1) → ZFSet.{u}) → ZFSet.{u}
  | 0, f => f 0
  | k + 1, f => relationProduct (⋃₀ ⋃₀ f 0) (tupleRelationBound k (fun j => f j.succ))
      (⋃₀ ⋃₀ f 0) (tupleRelationBound k (fun j => f j.succ)) (f 0)
      (tupleRelationProduct k (fun j => f j.succ))

theorem mem_tupleRelationBound (k : Nat) (f x : Fin (k + 1) → ZFSet.{u}) :
    nonemptyTupleCode k x ∈ tupleRelationBound k f ↔ ∀ j, x j ∈ ⋃₀ ⋃₀ f j := by
  induction k with
  | zero =>
    change x 0 ∈ ⋃₀ ⋃₀ f 0 ↔ _
    exact ⟨fun h => Fin.cases h (fun j => Fin.elim0 j), fun h => h 0⟩
  | succ k ih =>
    rw [tupleRelationBound, nonemptyTupleCode, ZFSet.pair_mem_prod, ih]
    exact ⟨fun h => Fin.cases h.1 h.2, fun h => ⟨h 0, fun j => h j.succ⟩⟩

theorem pair_mem_tupleRelationProduct (k : Nat) (f x y : Fin (k + 1) → ZFSet.{u}) :
    ZFSet.pair (nonemptyTupleCode k x) (nonemptyTupleCode k y) ∈ tupleRelationProduct k f ↔
      ∀ j, ZFSet.pair (x j) (y j) ∈ f j := by
  induction k with
  | zero =>
    change ZFSet.pair (x 0) (y 0) ∈ f 0 ↔ _
    exact ⟨fun h => Fin.cases h (fun j => Fin.elim0 j), fun h => h 0⟩
  | succ k ih =>
    rw [tupleRelationProduct, nonemptyTupleCode, nonemptyTupleCode,
      pair_mem_relationProduct, ih]
    constructor
    · rintro ⟨_, _, _, _, first, rest⟩
      exact Fin.cases first rest
    · intro entries
      exact ⟨pair_first_mem_doubleUnion (entries 0),
        (mem_tupleRelationBound k _ _).2 (fun j => pair_first_mem_doubleUnion (entries j.succ)),
        pair_second_mem_doubleUnion (entries 0),
        (mem_tupleRelationBound k _ _).2 (fun j => pair_second_mem_doubleUnion (entries j.succ)),
        entries 0, fun j => entries j.succ⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem tupleRelationBound_mem (k : Nat) (f : Fin (k + 1) → ZFSet.{u})
    (ground : ∀ j, f j ∈ M.sets) : tupleRelationBound k f ∈ M.sets := by
  induction k with
  | zero => exact M.union_mem unions (M.union_mem unions (ground 0))
  | succ k ih =>
    exact M.prod_mem pairing unions powers separation
      (M.union_mem unions (M.union_mem unions (ground 0))) (ih _ (fun j => ground j.succ))

theorem tupleRelationProduct_mem (k : Nat) (f : Fin (k + 1) → ZFSet.{u})
    (ground : ∀ j, f j ∈ M.sets) : tupleRelationProduct k f ∈ M.sets := by
  induction k with
  | zero => exact ground 0
  | succ k ih =>
    have first := M.union_mem unions (M.union_mem unions (ground 0))
    have rest := M.tupleRelationBound_mem pairing unions powers separation k _ (fun j => ground j.succ)
    exact M.relationProduct_mem pairing unions powers separation first rest first rest
      (ground 0) (ih _ (fun j => ground j.succ))

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
