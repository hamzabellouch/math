import OAI.SetTheory.PartitionPrinciple.Forcing.GroundDefinableRefinementNameGraphs

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

def stageOneRawSingleBody (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    (f : Fin 7 → ZFSet.{u}) (t u w lower : ZFSet.{u}) : Prop :=
  f 0 ∈ d 10 ∧
  f 1 ∈ d 10 ∧
  f 5 ∈ d 14 ∧
  f 6 ∈ d 14 ∧
  ZFSet.pair t (f 0) ∈ d 1 ∧
  ZFSet.pair t (f 1) ∈ d 2 ∧
  ZFSet.pair t (f 2) ∈ d 3 ∧
  ZFSet.pair t (f 3) ∈ d 4 ∧
  ZFSet.pair t (f 4) ∈ d 5 ∧
  stageOneRawClass M (d 6) (d 7) (d 8) (d 9) (f 4) u (f 5) ∧
  stageOneRawClass M (d 6) (d 7) (d 8) (d 9) (f 3) w (f 6) ∧
  stageOneRawForces M (d 7) (d 8) lower refinementActivityFormula ![u, w, f 2] ∧
  stageOneRawProfile M (d 7) (d 8) lower (d 10) (d 11) (d 13) (f 1) (f 5) (f 6) ∧
  stageOneRawCompatibility M (d 7) (d 8) lower (d 13) (d 12) (f 0) t (f 5) (f 6)

def stageOneRawSingle (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    (t u w lower : ZFSet.{u}) : Prop :=
  ∃ f : Fin 7 → ZFSet.{u}, (∀ j, f j ∈ M.sets) ∧ stageOneRawSingleBody M d f t u w lower

namespace SetFormula

def stageOneSingleBodyAt {n : Nat} (d : Fin 15 → Fin n) (f : Fin 7 → Fin n)
    (t u w lower : Fin n) : SetFormula n :=
  .conj (.mem (f 0) (d 10))
    (.conj (.mem (f 1) (d 10))
    (.conj (.mem (f 5) (d 14))
    (.conj (.mem (f 6) (d 14))
    (.conj ((BoundedFormula.pairMembershipFormula t (f 0) (d 1)).toFormula)
    (.conj ((BoundedFormula.pairMembershipFormula t (f 1) (d 2)).toFormula)
    (.conj ((BoundedFormula.pairMembershipFormula t (f 2) (d 3)).toFormula)
    (.conj ((BoundedFormula.pairMembershipFormula t (f 3) (d 4)).toFormula)
    (.conj ((BoundedFormula.pairMembershipFormula t (f 4) (d 5)).toFormula)
    (.conj (stageOneClassAt (f 5) (d 6) (f 4) u (d 7) (d 8) (d 9))
    (.conj (stageOneClassAt (f 6) (d 6) (f 3) w (d 7) (d 8) (d 9))
    (.conj (stageOneForcingAt refinementActivityFormula lower (d 7) (d 8) (extend u (extend w (extend (f 2) Fin.elim0))))
    (.conj (stageOneProfileAt (d 7) (d 8) lower (d 10) (d 11) (d 13) (f 1) (f 5) (f 6))
    ((stageOneCompatibilityAt (d 7) (d 8) lower (d 13) (d 12) (f 0) t (f 5) (f 6)))))))))))))))

def stageOneSingleAt {n : Nat} (d : Fin 15 → Fin n) (t u w lower : Fin n) : SetFormula n :=
  exBlock 7 (stageOneSingleBodyAt (fun j => suffixIndex n 7 (d j)) (prefixIndex n 7)
    (suffixIndex n 7 t) (suffixIndex n 7 u) (suffixIndex n 7 w) (suffixIndex n 7 lower))

end SetFormula

private theorem map_three {α β : Type*} (f : α → β) (a b c : α) :
    (fun j : Fin 3 => f ((extend a (extend b (extend c Fin.elim0))) j)) = ![f a, f b, f c] := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) j

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_stageOneSingleBodyAt {n : Nat} (d : Fin 15 → Fin n) (f : Fin 7 → Fin n)
    (t u w lower : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneSingleBodyAt d f t u w lower) env ↔
      stageOneRawSingleBody M (fun j => env (d j)) (fun j => env (f j))
        (env t) (env u) (env w) (env lower) := by
  apply and_congr
  · exact Iff.rfl
  apply and_congr
  · exact Iff.rfl
  apply and_congr
  · exact Iff.rfl
  apply and_congr
  · exact Iff.rfl
  apply and_congr
  · exact M.realize_stageOnePairLookup _ _ _ env members
  apply and_congr
  · exact M.realize_stageOnePairLookup _ _ _ env members
  apply and_congr
  · exact M.realize_stageOnePairLookup _ _ _ env members
  apply and_congr
  · exact M.realize_stageOnePairLookup _ _ _ env members
  apply and_congr
  · exact M.realize_stageOnePairLookup _ _ _ env members
  apply and_congr
  · exact M.realize_stageOneClassAt _ _ _ _ _ _ _ env
  apply and_congr
  · exact M.realize_stageOneClassAt _ _ _ _ _ _ _ env
  apply and_congr
  · rw [M.realize_stageOneForcingAt, map_three]
  apply and_congr
  · exact M.realize_stageOneProfileAt _ _ _ _ _ _ _ _ _ env members
  exact M.realize_stageOneCompatibilityAt _ _ _ _ _ _ _ _ _ env members

theorem realize_stageOneSingleAt {n : Nat} (d : Fin 15 → Fin n)
    (t u w lower : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneSingleAt d t u w lower) env ↔
      stageOneRawSingle M (fun j => env (d j)) (env t) (env u) (env w) (env lower) := by
  rw [stageOneSingleAt, realize_exBlock]
  unfold stageOneRawSingle
  apply exists_congr
  intro fields
  apply and_congr_right
  intro fieldMembers
  rw [M.realize_stageOneSingleBodyAt _ _ _ _ _ _ _ (extendMany_members 7 fields env fieldMembers members)]
  simp only [extendMany_prefix, extendMany_suffix]

end TransitiveGround





def stageOneRawCollisionBody (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    (f : Fin 6 → ZFSet.{u}) (t u u' w w' lower : ZFSet.{u}) : Prop :=
  f 2 ∈ d 14 ∧
  f 3 ∈ d 14 ∧
  f 4 ∈ d 14 ∧
  f 5 ∈ d 14 ∧
  ZFSet.pair t (f 0) ∈ d 4 ∧
  ZFSet.pair t (f 1) ∈ d 5 ∧
  stageOneRawClass M (d 6) (d 7) (d 8) (d 9) (f 1) u (f 2) ∧
  stageOneRawClass M (d 6) (d 7) (d 8) (d 9) (f 1) u' (f 3) ∧
  stageOneRawClass M (d 6) (d 7) (d 8) (d 9) (f 0) w (f 4) ∧
  stageOneRawClass M (d 6) (d 7) (d 8) (d 9) (f 0) w' (f 5) ∧
  stageOneRawForces M (d 7) (d 8) lower refinementCollisionFormula ![f 2, f 3, f 4, f 5]

def stageOneRawCollision (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    (t u u' w w' lower : ZFSet.{u}) : Prop :=
  ∃ f : Fin 6 → ZFSet.{u}, (∀ j, f j ∈ M.sets) ∧ stageOneRawCollisionBody M d f t u u' w w' lower

namespace SetFormula

def stageOneCollisionBodyAt {n : Nat} (d : Fin 15 → Fin n) (f : Fin 6 → Fin n)
    (t u u' w w' lower : Fin n) : SetFormula n :=
  .conj (.mem (f 2) (d 14))
    (.conj (.mem (f 3) (d 14))
    (.conj (.mem (f 4) (d 14))
    (.conj (.mem (f 5) (d 14))
    (.conj ((BoundedFormula.pairMembershipFormula t (f 0) (d 4)).toFormula)
    (.conj ((BoundedFormula.pairMembershipFormula t (f 1) (d 5)).toFormula)
    (.conj (stageOneClassAt (f 2) (d 6) (f 1) u (d 7) (d 8) (d 9))
    (.conj (stageOneClassAt (f 3) (d 6) (f 1) u' (d 7) (d 8) (d 9))
    (.conj (stageOneClassAt (f 4) (d 6) (f 0) w (d 7) (d 8) (d 9))
    (.conj (stageOneClassAt (f 5) (d 6) (f 0) w' (d 7) (d 8) (d 9))
    ((stageOneForcingAt refinementCollisionFormula lower (d 7) (d 8) (extend (f 2) (extend (f 3) (extend (f 4) (extend (f 5) Fin.elim0)))))))))))))))

def stageOneCollisionAt {n : Nat} (d : Fin 15 → Fin n) (t u u' w w' lower : Fin n) : SetFormula n :=
  exBlock 6 (stageOneCollisionBodyAt (fun j => suffixIndex n 6 (d j)) (prefixIndex n 6)
    (suffixIndex n 6 t) (suffixIndex n 6 u) (suffixIndex n 6 u')
    (suffixIndex n 6 w) (suffixIndex n 6 w') (suffixIndex n 6 lower))

end SetFormula

private theorem map_four {α β : Type*} (f : α → β) (a b c d : α) :
    (fun j : Fin 4 => f ((extend a (extend b (extend c (extend d Fin.elim0)))) j)) = ![f a, f b, f c, f d] := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) j

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_stageOneCollisionBodyAt {n : Nat} (d : Fin 15 → Fin n) (f : Fin 6 → Fin n)
    (t u u' w w' lower : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneCollisionBodyAt d f t u u' w w' lower) env ↔
      stageOneRawCollisionBody M (fun j => env (d j)) (fun j => env (f j))
        (env t) (env u) (env u') (env w) (env w') (env lower) := by
  apply and_congr
  · exact Iff.rfl
  apply and_congr
  · exact Iff.rfl
  apply and_congr
  · exact Iff.rfl
  apply and_congr
  · exact Iff.rfl
  apply and_congr
  · exact M.realize_stageOnePairLookup _ _ _ env members
  apply and_congr
  · exact M.realize_stageOnePairLookup _ _ _ env members
  apply and_congr
  · exact M.realize_stageOneClassAt _ _ _ _ _ _ _ env
  apply and_congr
  · exact M.realize_stageOneClassAt _ _ _ _ _ _ _ env
  apply and_congr
  · exact M.realize_stageOneClassAt _ _ _ _ _ _ _ env
  apply and_congr
  · exact M.realize_stageOneClassAt _ _ _ _ _ _ _ env
  rw [M.realize_stageOneForcingAt, map_four]

theorem realize_stageOneCollisionAt {n : Nat} (d : Fin 15 → Fin n)
    (t u u' w w' lower : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneCollisionAt d t u u' w w' lower) env ↔
      stageOneRawCollision M (fun j => env (d j)) (env t) (env u) (env u') (env w) (env w') (env lower) := by
  rw [stageOneCollisionAt, realize_exBlock]
  unfold stageOneRawCollision
  apply exists_congr
  intro fields
  apply and_congr_right
  intro fieldMembers
  rw [M.realize_stageOneCollisionBodyAt _ _ _ _ _ _ _ _ _ (extendMany_members 6 fields env fieldMembers members)]
  simp only [extendMany_prefix, extendMany_suffix]

end TransitiveGround





def stageOneRawTests (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    (A lower : ZFSet.{u}) : Prop :=
  (∀ t ∈ d 0, ∀ u ∈ d 6, ∀ w ∈ d 6, stageOneAssignment t u w ∈ A →
    stageOneRawSingle M d t u w lower) ∧
  (∀ t ∈ d 0, ∀ u ∈ d 6, ∀ u' ∈ d 6, ∀ w ∈ d 6, ∀ w' ∈ d 6,
    stageOneAssignment t u w ∈ A → stageOneAssignment t u' w' ∈ A →
    stageOneRawCollision M d t u u' w w' lower)

namespace SetFormula

def stageOneSinglesFormula {n : Nat} (d : Fin 15 → Fin n) (A lower : Fin n) : SetFormula n :=
  let old := suffixIndex n 3
  let v := prefixIndex n 3
  allBlock 3 (imp (BoundedFormula.conj (.mem (v 0) (old (d 0)))
    (.conj (.mem (v 1) (old (d 6))) (.conj (.mem (v 2) (old (d 6)))
      (BoundedFormula.rightTripleMembershipFormula (v 0) (v 1) (v 2) (old A))))).toFormula
    (stageOneSingleAt (fun j => old (d j)) (v 0) (v 1) (v 2) (old lower)))

def stageOneCollisionsFormula {n : Nat} (d : Fin 15 → Fin n) (A lower : Fin n) : SetFormula n :=
  let old := suffixIndex n 5
  let v := prefixIndex n 5
  allBlock 5 (imp (BoundedFormula.conj (.mem (v 0) (old (d 0)))
    (.conj (.mem (v 1) (old (d 6))) (.conj (.mem (v 2) (old (d 6)))
      (.conj (.mem (v 3) (old (d 6))) (.conj (.mem (v 4) (old (d 6)))
        (.conj (BoundedFormula.rightTripleMembershipFormula (v 0) (v 1) (v 3) (old A))
          (BoundedFormula.rightTripleMembershipFormula (v 0) (v 2) (v 4) (old A)))))))).toFormula
    (stageOneCollisionAt (fun j => old (d j)) (v 0) (v 1) (v 2) (v 3) (v 4) (old lower)))

def stageOneTestsFormula {n : Nat} (d : Fin 15 → Fin n) (A lower : Fin n) : SetFormula n :=
  .conj (stageOneSinglesFormula d A lower) (stageOneCollisionsFormula d A lower)

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_stageOneSinglesFormula {n : Nat} (d : Fin 15 → Fin n) (A lower : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneSinglesFormula d A lower) env ↔
      ∀ t ∈ env (d 0), ∀ u ∈ env (d 6), ∀ w ∈ env (d 6), stageOneAssignment t u w ∈ env A →
        stageOneRawSingle M (fun j => env (d j)) t u w (env lower) := by
  rw [stageOneSinglesFormula, realize_allBlock]
  have actual (v : Fin 3 → ZFSet.{u}) (ground : ∀ j, v j ∈ M.sets) :
      Realize M.sets (imp (BoundedFormula.conj (.mem (prefixIndex n 3 0) (suffixIndex n 3 (d 0)))
    (.conj (.mem (prefixIndex n 3 1) (suffixIndex n 3 (d 6))) (.conj (.mem (prefixIndex n 3 2) (suffixIndex n 3 (d 6)))
      (BoundedFormula.rightTripleMembershipFormula (prefixIndex n 3 0) (prefixIndex n 3 1) (prefixIndex n 3 2) (suffixIndex n 3 A))))).toFormula
    (stageOneSingleAt (fun j => suffixIndex n 3 (d j)) (prefixIndex n 3 0) (prefixIndex n 3 1) (prefixIndex n 3 2) (suffixIndex n 3 lower))) (extendMany 3 v env) ↔
        (v 0 ∈ env (d 0) ∧ v 1 ∈ env (d 6) ∧ v 2 ∈ env (d 6) ∧ stageOneAssignment (v 0) (v 1) (v 2) ∈ env A) →
          stageOneRawSingle M (fun j => env (d j)) (v 0) (v 1) (v 2) (env lower) := by
    rw [realize_imp, BoundedFormula.realize_toFormula M _ _ (extendMany_members 3 v env ground members),
      M.realize_stageOneSingleAt _ _ _ _ _ _ (extendMany_members 3 v env ground members)]
    simp only [BoundedFormula.Truth, BoundedFormula.truth_rightTripleMembershipFormula,
      extendMany_prefix, extendMany_suffix, stageOneAssignment]
  constructor
  · intro h t ht u hu w hw entry
    have ground : ∀ j : Fin 3, (![t,u,w] : Fin 3 → ZFSet.{u}) j ∈ M.sets :=
      Fin.cases (M.transitive (members (d 0)) ht)
        (Fin.cases (M.transitive (members (d 6)) hu)
          (Fin.cases (M.transitive (members (d 6)) hw) (fun j => Fin.elim0 j)))
    exact (actual ![t,u,w] ground).1 (h _ ground) ⟨ht,hu,hw,entry⟩
  · intro h v ground
    apply (actual v ground).2
    rintro ⟨ht,hu,hw,entry⟩
    exact h (v 0) ht (v 1) hu (v 2) hw entry

theorem realize_stageOneCollisionsFormula {n : Nat} (d : Fin 15 → Fin n) (A lower : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneCollisionsFormula d A lower) env ↔
      ∀ t ∈ env (d 0), ∀ u ∈ env (d 6), ∀ u' ∈ env (d 6), ∀ w ∈ env (d 6), ∀ w' ∈ env (d 6),
        stageOneAssignment t u w ∈ env A → stageOneAssignment t u' w' ∈ env A →
          stageOneRawCollision M (fun j => env (d j)) t u u' w w' (env lower) := by
  rw [stageOneCollisionsFormula, realize_allBlock]
  have actual (v : Fin 5 → ZFSet.{u}) (ground : ∀ j, v j ∈ M.sets) :
      Realize M.sets (imp (BoundedFormula.conj (.mem (prefixIndex n 5 0) (suffixIndex n 5 (d 0)))
    (.conj (.mem (prefixIndex n 5 1) (suffixIndex n 5 (d 6))) (.conj (.mem (prefixIndex n 5 2) (suffixIndex n 5 (d 6)))
      (.conj (.mem (prefixIndex n 5 3) (suffixIndex n 5 (d 6))) (.conj (.mem (prefixIndex n 5 4) (suffixIndex n 5 (d 6)))
        (.conj (BoundedFormula.rightTripleMembershipFormula (prefixIndex n 5 0) (prefixIndex n 5 1) (prefixIndex n 5 3) (suffixIndex n 5 A))
          (BoundedFormula.rightTripleMembershipFormula (prefixIndex n 5 0) (prefixIndex n 5 2) (prefixIndex n 5 4) (suffixIndex n 5 A)))))))).toFormula
    (stageOneCollisionAt (fun j => suffixIndex n 5 (d j)) (prefixIndex n 5 0) (prefixIndex n 5 1) (prefixIndex n 5 2) (prefixIndex n 5 3) (prefixIndex n 5 4) (suffixIndex n 5 lower))) (extendMany 5 v env) ↔
        (v 0 ∈ env (d 0) ∧ v 1 ∈ env (d 6) ∧ v 2 ∈ env (d 6) ∧ v 3 ∈ env (d 6) ∧ v 4 ∈ env (d 6) ∧
          stageOneAssignment (v 0) (v 1) (v 3) ∈ env A ∧ stageOneAssignment (v 0) (v 2) (v 4) ∈ env A) →
          stageOneRawCollision M (fun j => env (d j)) (v 0) (v 1) (v 2) (v 3) (v 4) (env lower) := by
    rw [realize_imp, BoundedFormula.realize_toFormula M _ _ (extendMany_members 5 v env ground members),
      M.realize_stageOneCollisionAt _ _ _ _ _ _ _ _ (extendMany_members 5 v env ground members)]
    simp only [BoundedFormula.Truth, BoundedFormula.truth_rightTripleMembershipFormula,
      extendMany_prefix, extendMany_suffix, stageOneAssignment]
  constructor
  · intro h t ht u hu u' hu' w hw w' hw' first second
    have ground : ∀ j : Fin 5, (![t,u,u',w,w'] : Fin 5 → ZFSet.{u}) j ∈ M.sets :=
      Fin.cases (M.transitive (members (d 0)) ht)
        (Fin.cases (M.transitive (members (d 6)) hu)
          (Fin.cases (M.transitive (members (d 6)) hu')
            (Fin.cases (M.transitive (members (d 6)) hw)
              (Fin.cases (M.transitive (members (d 6)) hw') (fun j => Fin.elim0 j)))))
    exact (actual ![t,u,u',w,w'] ground).1 (h _ ground) ⟨ht,hu,hu',hw,hw',first,second⟩
  · intro h v ground
    apply (actual v ground).2
    rintro ⟨ht,hu,hu',hw,hw',first,second⟩
    exact h (v 0) ht (v 1) hu (v 2) hu' (v 3) hw (v 4) hw' first second

theorem realize_stageOneTestsFormula {n : Nat} (d : Fin 15 → Fin n) (A lower : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneTestsFormula d A lower) env ↔
      stageOneRawTests M (fun j => env (d j)) (env A) (env lower) := by
  exact and_congr (M.realize_stageOneSinglesFormula d A lower env members)
    (M.realize_stageOneCollisionsFormula d A lower env members)

end TransitiveGround





def StageTwoConditionCode (M : TransitiveGround.{u}) (levels alpha : ZFSet.{u})
    (d : Fin 15 → ZFSet.{u}) (z : ZFSet.{u}) : Prop :=
  ∃ row A, z = ZFSet.pair row A ∧
    ZFSet.pair row (assignmentCut levels alpha A) ∈ d 7 ∧
    stageOneRawTests M d A (ZFSet.pair row (assignmentCut levels alpha A))

namespace SetFormula

def stageTwoConditionFormula {n : Nat} (d : Fin 15 → Fin n)
    (levels alpha z : Fin n) : SetFormula n :=
  let old := suffixIndex n 4
  let v := prefixIndex n 4
  exBlock 4 (.conj
    (BoundedFormula.orderedPairFormula (old z) (v 0) (v 1)).toFormula
    (.conj (BoundedFormula.assignmentCutFormula (v 2) (old levels) (old alpha) (v 1)).toFormula
      (.conj (BoundedFormula.orderedPairFormula (v 3) (v 0) (v 2)).toFormula
        (.conj (.mem (v 3) (old (d 7)))
          (stageOneTestsFormula (fun j => old (d j)) (v 1) (v 3))))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_stageTwoConditionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets)
    {n : Nat} (d : Fin 15 → Fin n) (levels alpha z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageTwoConditionFormula d levels alpha z) env ↔
      StageTwoConditionCode M (env levels) (env alpha) (fun j => env (d j)) (env z) := by
  rw [stageTwoConditionFormula, realize_exBlock]
  have actual (f : Fin 4 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (.conj
        (BoundedFormula.orderedPairFormula (suffixIndex n 4 z)
          (prefixIndex n 4 0) (prefixIndex n 4 1)).toFormula
        (.conj (BoundedFormula.assignmentCutFormula (prefixIndex n 4 2)
          (suffixIndex n 4 levels) (suffixIndex n 4 alpha) (prefixIndex n 4 1)).toFormula
          (.conj (BoundedFormula.orderedPairFormula (prefixIndex n 4 3)
            (prefixIndex n 4 0) (prefixIndex n 4 2)).toFormula
            (.conj (.mem (prefixIndex n 4 3) (suffixIndex n 4 (d 7)))
              (stageOneTestsFormula (fun j => suffixIndex n 4 (d j))
                (prefixIndex n 4 1) (prefixIndex n 4 3))))))
          (extendMany 4 f env) ↔
        env z = ZFSet.pair (f 0) (f 1) ∧
          f 2 = assignmentCut (env levels) (env alpha) (f 1) ∧
          f 3 = ZFSet.pair (f 0) (f 2) ∧ f 3 ∈ env (d 7) ∧
          stageOneRawTests M (fun j => env (d j)) (f 1) (f 3) := by
    have allground := extendMany_members 4 f env ground members
    apply and_congr
    · rw [BoundedFormula.realize_toFormula M _ _ allground,
        BoundedFormula.truth_orderedPairFormula]
      simp only [extendMany_prefix, extendMany_suffix]
    apply and_congr
    · rw [M.realize_assignmentCutFormula _ _ _ _ _ allground]
      simp only [extendMany_prefix, extendMany_suffix]
    apply and_congr
    · rw [BoundedFormula.realize_toFormula M _ _ allground,
        BoundedFormula.truth_orderedPairFormula]
      simp only [extendMany_prefix]
    apply and_congr
    · rfl
    rw [M.realize_stageOneTestsFormula _ _ _ _ allground]
    simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, body⟩
    obtain ⟨pair, cut, lower, valid, tests⟩ := (actual f ground).1 body
    rw [cut] at lower
    exact ⟨f 0, f 1, pair, lower ▸ valid, lower ▸ tests⟩
  · rintro ⟨row, A, equal, valid, tests⟩
    have hrow : row ∈ M.sets := M.pair_left (equal ▸ members z)
    have hA : A ∈ M.sets := M.pair_right (equal ▸ members z)
    have hcut := M.assignmentCut_mem separation (members levels) (members alpha) hA
    have hlower := M.orderedPair_mem pairing hrow hcut
    let cut := assignmentCut (env levels) (env alpha) A
    let f : Fin 4 → ZFSet.{u} := ![row, A, cut, ZFSet.pair row cut]
    have ground : ∀ j, f j ∈ M.sets :=
      Fin.cases hrow (Fin.cases hA (Fin.cases hcut
        (Fin.cases hlower (fun j => Fin.elim0 j))))
    exact ⟨f, ground, (actual f ground).2 ⟨equal, rfl, rfl, valid, tests⟩⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def refinementFormulaDataCode (d : Fin 15 → ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 14 d

theorem refinementFormulaDataCode_injective :
    Function.Injective (refinementFormulaDataCode.{u}) :=
  nonemptyTupleCode_injective 14

def PackedSuccessorConditionCode (M : TransitiveGround.{u})
    (levels alpha data z : ZFSet.{u}) : Prop :=
  ∃ d : Fin 15 → ZFSet.{u}, data = refinementFormulaDataCode d ∧
    StageTwoConditionCode M levels alpha d z

theorem packedSuccessorConditionCode_code_iff (M : TransitiveGround.{u})
    (levels alpha : ZFSet.{u}) (d : Fin 15 → ZFSet.{u}) (z : ZFSet.{u}) :
    PackedSuccessorConditionCode M levels alpha (refinementFormulaDataCode d) z ↔
      StageTwoConditionCode M levels alpha d z := by
  constructor
  · rintro ⟨stored, equal, valid⟩
    have same := refinementFormulaDataCode_injective equal
    exact same.symm ▸ valid
  · intro valid
    exact ⟨d, rfl, valid⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem refinementFormulaDataCode_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (d : Fin 15 → ZFSet.{u}) (members : ∀ j, d j ∈ M.sets) :
    refinementFormulaDataCode d ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 14 d members

theorem refinementFormulaDataCode_fields_mem (d : Fin 15 → ZFSet.{u})
    (ground : refinementFormulaDataCode d ∈ M.sets) : ∀ j, d j ∈ M.sets :=
  M.nonemptyTupleCode_field_mem 14 d ground

theorem refinementFormulaDataCode_mem_iff
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (d : Fin 15 → ZFSet.{u}) :
    refinementFormulaDataCode d ∈ M.sets ↔ ∀ j, d j ∈ M.sets :=
  ⟨M.refinementFormulaDataCode_fields_mem d, M.refinementFormulaDataCode_mem pairing d⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)

noncomputable def refinementLevelFormulaData : Fin 15 → ZFSet.{u} :=
  let I := M.niceRefinementIndices a s b d level T T2 valid
  let bounds := M.niceRefinementIndexBounds s b level T T2
  ![I, refinementIndexFieldGraph I (bounds 1) 1, refinementIndexFieldGraph I (bounds 2) 2,
    refinementIndexFieldGraph I (bounds 3) 3, refinementIndexFieldGraph I (bounds 4) 4,
    refinementIndexFieldGraph I (bounds 5) 5, T, s.carrier, s.conditionOrder, s.encode ⊤,
    b.carrier, b.conditionOrder, M.niceRefinementNameGraph a s b d 2 level T T2 valid,
    M.niceVisibilityGraph a s b T d.principalFix, M.groundRelations T s.carrier]

theorem refinementLevelFormulaData_members
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hT : T ∈ M.sets) (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (nodeOrder : b.conditionOrder ∈ M.sets)
    (valid2 : ∀ z ∈ T2, IsName s z)
    (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (system : NiceNameSystem M a s b d base directed T valid) :
    ∀ j, M.refinementLevelFormulaData a s b d level T T2 valid j ∈ M.sets := by
  have mapGround := M.niceRefinementNameGraph_mem a s b d indices pairing unions powers separation
    hT carrier order 2
  have classes := M.groundRelations_mem pairing unions powers separation hT carrier
  exact Fin.cases indices.index_ground (Fin.cases (indices.field_ground 1)
    (Fin.cases (indices.field_ground 2) (Fin.cases (indices.field_ground 3)
      (Fin.cases (indices.field_ground 4) (Fin.cases (indices.field_ground 5)
        (Fin.cases hT (Fin.cases carrier (Fin.cases order
          (Fin.cases (M.transitive carrier (s.encode_mem ⊤)) (Fin.cases nodes
            (Fin.cases nodeOrder (Fin.cases mapGround (Fin.cases system.visibility_graph_ground
              (Fin.cases classes (fun j => Fin.elim0 j)))))))))))))))

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace SetFormula

def packedSuccessorConditionFormula {n : Nat} (levels alpha data z : Fin n) : SetFormula n :=
  exBlock 15 (.conj
    (BoundedFormula.nonemptyTupleFormula 14 (suffixIndex n 15 data) (prefixIndex n 15)).toFormula
    (stageTwoConditionFormula (prefixIndex n 15) (suffixIndex n 15 levels)
      (suffixIndex n 15 alpha) (suffixIndex n 15 z)))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_packedSuccessorConditionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets)
    {n : Nat} (levels alpha data z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (packedSuccessorConditionFormula levels alpha data z) env ↔
      PackedSuccessorConditionCode M (env levels) (env alpha) (env data) (env z) := by
  rw [packedSuccessorConditionFormula, realize_exBlock]
  constructor
  · rintro ⟨fields, ground, tuple, valid⟩
    have bounds := extendMany_members 15 fields env ground members
    have equal := (BoundedFormula.truth_nonemptyTupleFormula 14
      (suffixIndex n 15 data) (prefixIndex n 15) _).1
      ((BoundedFormula.realize_toFormula M _ _ bounds).1 tuple)
    have actual := (M.realize_stageTwoConditionFormula pairing separation (prefixIndex n 15)
      (suffixIndex n 15 levels) (suffixIndex n 15 alpha) (suffixIndex n 15 z)
      (extendMany 15 fields env) bounds).1 valid
    simp only [extendMany_prefix, extendMany_suffix] at equal actual
    exact ⟨fields, equal, actual⟩
  · rintro ⟨fields, equal, valid⟩
    have ground := M.refinementFormulaDataCode_fields_mem fields (equal ▸ members data)
    have bounds := extendMany_members 15 fields env ground members
    refine ⟨fields, ground, ?_, ?_⟩
    · apply (BoundedFormula.realize_toFormula M _ _ bounds).2
      apply (BoundedFormula.truth_nonemptyTupleFormula 14
        (suffixIndex n 15 data) (prefixIndex n 15) _).2
      simpa only [extendMany_prefix, extendMany_suffix, refinementFormulaDataCode] using equal
    · apply (M.realize_stageTwoConditionFormula pairing separation (prefixIndex n 15)
        (suffixIndex n 15 levels) (suffixIndex n 15 alpha) (suffixIndex n 15 z)
        (extendMany 15 fields env) bounds).2
      simpa only [extendMany_prefix, extendMany_suffix] using valid

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)

noncomputable def refinementLevelFormulaDataCode : ZFSet.{u} :=
  refinementFormulaDataCode (M.refinementLevelFormulaData a s b d level T T2 valid)

theorem refinementLevelFormulaDataCode_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hT : T ∈ M.sets) (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (nodeOrder : b.conditionOrder ∈ M.sets)
    (valid2 : ∀ z ∈ T2, IsName s z)
    (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (system : NiceNameSystem M a s b d base directed T valid) :
    M.refinementLevelFormulaDataCode a s b d level T T2 valid ∈ M.sets :=
  M.refinementFormulaDataCode_mem pairing _
    (M.refinementLevelFormulaData_members a s b d level T T2 valid
      pairing unions powers separation hT carrier order nodes nodeOrder valid2 indices base directed system)

theorem packedSuccessorConditionCode_refinementLevel_iff (levels alpha z : ZFSet.{u}) :
    PackedSuccessorConditionCode M levels alpha
      (M.refinementLevelFormulaDataCode a s b d level T T2 valid) z ↔
    StageTwoConditionCode M levels alpha
      (M.refinementLevelFormulaData a s b d level T T2 valid) z :=
  packedSuccessorConditionCode_code_iff M levels alpha _ z

end PartitionPilot.Forcing.TransitiveGround

end OAI
