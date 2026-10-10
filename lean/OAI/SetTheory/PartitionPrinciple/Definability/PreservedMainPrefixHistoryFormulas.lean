import OAI.SetTheory.PartitionPrinciple.Forcing.MainPrefixConditionalStepCodes
import OAI.SetTheory.PartitionPrinciple.Transfinite.PreservedMainPrefixHistoryValues

namespace OAI

namespace PartitionPilot.Forcing

namespace BoundedFormula
open SetFormula
universe u

def nonzeroLimitOrdinalFormula {n} (T : Fin n) : BoundedFormula n :=
  .conj (.neg (emptyFormula T)) (.allMem T (exMem T.succ (.mem 1 0)))

theorem truth_nonzeroLimitOrdinalFormula {n} (T : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (nonzeroLimitOrdinalFormula T) env ↔ NonzeroLimitOrdinalCode (env T) := by
  simp only [nonzeroLimitOrdinalFormula, Truth, truth_emptyFormula, truth_exMem]
  rfl

theorem realize_nonzeroLimitOrdinalFormula (M : TransitiveGround.{u}) {n}
    (T : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (nonzeroLimitOrdinalFormula T).toFormula env ↔
      NonzeroLimitOrdinalCode (env T) :=
  (realize_toFormula M _ env members).trans (truth_nonzeroLimitOrdinalFormula T env)

end BoundedFormula

open SetFormula
universe u

namespace BoundedFormula
def mainPrefixFieldExtensionFormula {n} (T S E T' S' E' : Fin n) : BoundedFormula n :=
  .conj (subsetFormula T T') (.conj (subsetFormula S S') (subsetFormula E E'))

theorem truth_mainPrefixFieldExtensionFormula {n} (T S E T' S' E' : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (mainPrefixFieldExtensionFormula T S E T' S' E') env ↔
      env T ⊆ env T' ∧ env S ⊆ env S' ∧ env E ⊆ env E' := by
  simp only [mainPrefixFieldExtensionFormula, Truth, truth_subsetFormula]

end BoundedFormula

namespace SetFormula
def mainPrefixExtensionFormula {n} (old next : Fin n) : SetFormula n :=
  let outer := suffixIndex n 6
  let field := prefixIndex n 6
  exBlock 6 (.conj
    (BoundedFormula.mainPrefixTupleFormula (outer old) (field 0) (field 1) (field 2)).toFormula
    (.conj (BoundedFormula.mainPrefixTupleFormula (outer next) (field 3) (field 4) (field 5)).toFormula
      (BoundedFormula.mainPrefixFieldExtensionFormula
        (field 0) (field 1) (field 2) (field 3) (field 4) (field 5)).toFormula))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixExtensionFormula {n} (old next : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixExtensionFormula old next) env ↔
      MainPrefixExtends (env old) (env next) := by
  rw [mainPrefixExtensionFormula, realize_exBlock]
  let outer := suffixIndex n 6
  let field := prefixIndex n 6
  have actual (f : Fin 6 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      (Realize M.sets (BoundedFormula.mainPrefixTupleFormula (outer old) (field 0) (field 1) (field 2)).toFormula
        (extendMany 6 f env) ∧
      Realize M.sets (BoundedFormula.mainPrefixTupleFormula (outer next) (field 3) (field 4) (field 5)).toFormula
        (extendMany 6 f env) ∧
      Realize M.sets (BoundedFormula.mainPrefixFieldExtensionFormula
        (field 0) (field 1) (field 2) (field 3) (field 4) (field 5)).toFormula (extendMany 6 f env)) ↔
      env old = mainPrefixCode (f 0) (f 1) (f 2) ∧
        env next = mainPrefixCode (f 3) (f 4) (f 5) ∧ f 0 ⊆ f 3 ∧ f 1 ⊆ f 4 ∧ f 2 ⊆ f 5 := by
    have mems := extendMany_members 6 f env ground members
    rw [BoundedFormula.realize_mainPrefixTupleFormula M _ _ _ _ _ mems,
      BoundedFormula.realize_mainPrefixTupleFormula M _ _ _ _ _ mems,
      BoundedFormula.realize_toFormula M _ _ mems, BoundedFormula.truth_mainPrefixFieldExtensionFormula]
    simp only [outer, field, extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, clauses⟩
    have result := (actual f ground).1 clauses
    exact ⟨f 0, f 1, f 2, f 3, f 4, f 5, result⟩
  · rintro ⟨T, S, E, U, F, G, first, second, indices, stages, transitions⟩
    have left := M.mainPrefixCode_fields_mem (first ▸ members old)
    have right := M.mainPrefixCode_fields_mem (second ▸ members next)
    let f : Fin 6 → ZFSet.{u} := Fin.cases T (Fin.cases S (Fin.cases E
      (Fin.cases U (Fin.cases F (fun _ => G)))))
    have ground : ∀ j, f j ∈ M.sets := Fin.cases left.1 (Fin.cases left.2.1
      (Fin.cases left.2.2 (Fin.cases right.1 (Fin.cases right.2.1 (fun _ => right.2.2)))))
    exact ⟨f, ground, (actual f ground).2 ⟨first, second, indices, stages, transitions⟩⟩

end TransitiveGround

namespace SetFormula

def mainPrefixLimitStepRawFormula {n} (K Labels C D rD N old next : Fin n)
    (w : Fin 32 → Fin n) : SetFormula n :=
  let v := mainPrefixLimitTargetFields w
  .conj (BoundedFormula.successorFormula (w 7) (w 0)).toFormula
  (.conj (BoundedFormula.mainPrefixTupleFormula old (w 0) (w 1) (w 2)).toFormula
  (.conj (BoundedFormula.mainPrefixTupleFormula next (w 7) (w 3) (w 4)).toFormula
  (.conj (mainPrefixExtensionFormula old next)
  (.conj (BoundedFormula.pairMembershipFormula (w 0) (w 5) (w 3)).toFormula
  (.conj (linkedMainStageRawFormula K Labels C D rD N (w 5) v)
  (.conj (BoundedFormula.pairMembershipFormula (v 11) (w 6) (v 17)).toFormula
    (BoundedFormula.mainLimitCoverageFormula (w 0) (w 1) (w 4)
      (v 0) (v 3) (v 1) (v 9) (v 11) (w 6)).toFormula))))))

def mainPrefixLimitStepFormula {n} (K Labels C D rD N old next : Fin n) : SetFormula n :=
  let outer := suffixIndex n 32
  exBlock 32 (mainPrefixLimitStepRawFormula (outer K) (outer Labels) (outer C)
    (outer D) (outer rD) (outer N) (outer old) (outer next) (prefixIndex n 32))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixLimitStepRawFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n} (K Labels C D rD N old next : Fin n)
    (w : Fin 32 → Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixLimitStepRawFormula K Labels C D rD N old next w) env ↔
      MainPrefixLimitStepRawCode M (env K) (env Labels) (env C) (env D) (env rD) (env N)
        (env old) (env next) (fun j => env (w j)) := by
  have linked := M.realize_linkedMainStageRawFormula pairing unions powers separation collection
    K Labels C D rD N (w 5) (mainPrefixLimitTargetFields w) env members omega ordinal
  have extension := M.realize_mainPrefixExtensionFormula old next env members
  simp only [mainPrefixLimitStepRawFormula, Realize, BoundedFormula.realize_toFormula M _ env members,
    BoundedFormula.truth_successorFormula, BoundedFormula.truth_mainPrefixTupleFormula,
    extension, BoundedFormula.truth_pairMembershipFormula, linked,
    BoundedFormula.truth_mainLimitCoverageFormula]
  rfl

theorem realize_mainPrefixLimitStepFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n} (K Labels C D rD N old next : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixLimitStepFormula K Labels C D rD N old next) env ↔
      MainPrefixLimitStepCode M (env K) (env Labels) (env C) (env D) (env rD) (env N)
        (env old) (env next) := by
  rw [mainPrefixLimitStepFormula, realize_exBlock]
  have actual (w : Fin 32 → ZFSet.{u}) (ground : ∀ j, w j ∈ M.sets) :=
    M.realize_mainPrefixLimitStepRawFormula pairing unions powers separation collection
      (suffixIndex n 32 K) (suffixIndex n 32 Labels) (suffixIndex n 32 C) (suffixIndex n 32 D)
      (suffixIndex n 32 rD) (suffixIndex n 32 N) (suffixIndex n 32 old) (suffixIndex n 32 next)
      (prefixIndex n 32) (extendMany 32 w env) (extendMany_members 32 w env ground members)
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)
  simp only [extendMany_prefix, extendMany_suffix] at actual
  exact ⟨fun ⟨w, ground, recognized⟩ => ⟨w, ground, (actual w ground).1 recognized⟩,
    fun ⟨w, ground, raw⟩ => ⟨w, ground, (actual w ground).2 raw⟩⟩

end TransitiveGround

namespace BoundedFormula
def mainPrefixSelectedStepBody {n} (f old next : Fin n) (v : Fin 10 → Fin n) : BoundedFormula n :=
  .conj (successorFormula (v 8) (v 0))
  (.conj (successorFormula (v 9) (v 8))
  (.conj (mainPrefixTupleFormula old (v 8) (v 1) (v 2))
  (.conj (mainPrefixTupleFormula next (v 9) (v 3) (v 4))
  (.conj (mainPrefixFieldExtensionFormula (v 8) (v 1) (v 2) (v 9) (v 3) (v 4))
  (.conj (pairMembershipFormula (v 0) (v 5) (v 1))
  (.conj (rightTripleMembershipFormula (v 5) (v 6) (v 7) f)
  (.conj (pairMembershipFormula (v 8) (v 6) (v 3))
    (tripleMembershipFormula (v 8) (v 0) (v 7) (v 4)))))))))

theorem truth_mainPrefixSelectedStepBody {n} (f old next : Fin n) (v : Fin 10 → Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (mainPrefixSelectedStepBody f old next v) env ↔
      env (v 8) = insert (env (v 0)) (env (v 0)) ∧
      env (v 9) = insert (env (v 8)) (env (v 8)) ∧
      env old = mainPrefixCode (env (v 8)) (env (v 1)) (env (v 2)) ∧
      env next = mainPrefixCode (env (v 9)) (env (v 3)) (env (v 4)) ∧
      (env (v 8) ⊆ env (v 9) ∧ env (v 1) ⊆ env (v 3) ∧ env (v 2) ⊆ env (v 4)) ∧
      ZFSet.pair (env (v 0)) (env (v 5)) ∈ env (v 1) ∧
      ZFSet.pair (env (v 5)) (ZFSet.pair (env (v 6)) (env (v 7))) ∈ env f ∧
      ZFSet.pair (env (v 8)) (env (v 6)) ∈ env (v 3) ∧
      ZFSet.pair (ZFSet.pair (env (v 8)) (env (v 0))) (env (v 7)) ∈ env (v 4) := by
  simp only [mainPrefixSelectedStepBody, Truth, truth_successorFormula,
    truth_mainPrefixTupleFormula, truth_mainPrefixFieldExtensionFormula,
    truth_pairMembershipFormula, truth_rightTripleMembershipFormula, truth_tripleMembershipFormula]

end BoundedFormula

namespace SetFormula
def mainPrefixSelectedStepFormula {n} (f old next : Fin n) : SetFormula n :=
  exBlock 10 (BoundedFormula.mainPrefixSelectedStepBody
    (suffixIndex n 10 f) (suffixIndex n 10 old) (suffixIndex n 10 next)
    (prefixIndex n 10)).toFormula

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixSelectedStepFormula {n} (f old next : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixSelectedStepFormula f old next) env ↔
      MainPrefixSelectedStepCode (env f) (env old) (env next) := by
  rw [mainPrefixSelectedStepFormula, realize_exBlock]
  have actual (v : Fin 10 → ZFSet.{u}) (ground : ∀ j, v j ∈ M.sets) :=
    (BoundedFormula.realize_toFormula M _ (extendMany 10 v env)
      (extendMany_members 10 v env ground members)).trans
      (BoundedFormula.truth_mainPrefixSelectedStepBody
        (suffixIndex n 10 f) (suffixIndex n 10 old) (suffixIndex n 10 next)
        (prefixIndex n 10) (extendMany 10 v env))
  simp only [extendMany_prefix, extendMany_suffix] at actual
  constructor
  · rintro ⟨v, ground, recognized⟩
    obtain ⟨first, second, oldCode, nextCode, extension, source, selected, target, crossing⟩ :=
      (actual v ground).1 recognized
    refine ⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, ?_, ?_, ?_, source, selected, ?_, ?_⟩
    · simpa only [first] using oldCode
    · simpa only [second, first] using nextCode
    · rw [oldCode, nextCode]
      exact mainPrefixExtends_iff.2 extension
    · simpa only [first] using target
    · simpa only [first] using crossing
  · rintro ⟨b, S, E, S', E', a, target, z, oldCode, nextCode,
      extension, source, selected, targetEntry, crossing⟩
    have left := M.mainPrefixCode_fields_mem (oldCode ▸ members old)
    have right := M.mainPrefixCode_fields_mem (nextCode ▸ members next)
    have sourceGround := M.transitive left.2.1 source
    have selectedGround := M.transitive (members f) selected
    let v : Fin 10 → ZFSet.{u} := Fin.cases b (Fin.cases S (Fin.cases E
      (Fin.cases S' (Fin.cases E' (Fin.cases a (Fin.cases target (Fin.cases z
        (Fin.cases (insert b b) (fun _ => insert (insert b b) (insert b b))))))))))
    have ground : ∀ j, v j ∈ M.sets := Fin.cases (M.pair_left sourceGround)
      (Fin.cases left.2.1 (Fin.cases left.2.2 (Fin.cases right.2.1 (Fin.cases right.2.2
      (Fin.cases (M.pair_right sourceGround) (Fin.cases (M.pair_left (M.pair_right selectedGround))
      (Fin.cases (M.pair_right (M.pair_right selectedGround)) (Fin.cases left.1 (fun _ => right.1)))))))))
    rw [oldCode, nextCode] at extension
    exact ⟨v, ground, (actual v ground).2 ⟨rfl, rfl, oldCode, nextCode,
      mainPrefixExtends_iff.1 extension, source, selected, targetEntry, crossing⟩⟩

end TransitiveGround

namespace SetFormula
def mainPrefixConditionalStepFormula {n} (K Labels C D rD N f old next : Fin n) : SetFormula n :=
  let outer := suffixIndex n 3
  let field := prefixIndex n 3
  disj (mainPrefixSelectedStepFormula f old next)
    (exBlock 3 (.conj
      (BoundedFormula.mainPrefixTupleFormula (outer old) (field 0) (field 1) (field 2)).toFormula
      (.conj (BoundedFormula.nonzeroLimitOrdinalFormula (field 0)).toFormula
        (mainPrefixLimitStepFormula (outer K) (outer Labels) (outer C) (outer D)
          (outer rD) (outer N) (outer old) (outer next)))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixConditionalStepFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n}
    (K Labels C D rD N f old next : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) (omega : env N = ZFSet.omega)
    (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixConditionalStepFormula K Labels C D rD N f old next) env ↔
      MainPrefixConditionalStepCode M (env K) (env Labels) (env C) (env D) (env rD)
        (env N) (env f) (env old) (env next) := by
  rw [mainPrefixConditionalStepFormula, realize_disj,
    M.realize_mainPrefixSelectedStepFormula f old next env members, realize_exBlock]
  apply or_congr Iff.rfl
  let outer := suffixIndex n 3
  let field := prefixIndex n 3
  have actual (w : Fin 3 → ZFSet.{u}) (ground : ∀ j, w j ∈ M.sets) :
      Realize M.sets (.conj
        (BoundedFormula.mainPrefixTupleFormula (outer old) (field 0) (field 1) (field 2)).toFormula
        (.conj (BoundedFormula.nonzeroLimitOrdinalFormula (field 0)).toFormula
          (mainPrefixLimitStepFormula (outer K) (outer Labels) (outer C) (outer D)
            (outer rD) (outer N) (outer old) (outer next)))) (extendMany 3 w env) ↔
      env old = mainPrefixCode (w 0) (w 1) (w 2) ∧ NonzeroLimitOrdinalCode (w 0) ∧
        MainPrefixLimitStepCode M (env K) (env Labels) (env C) (env D) (env rD) (env N)
          (env old) (env next) := by
    have mems := extendMany_members 3 w env ground members
    change (Realize M.sets _ _ ∧ Realize M.sets _ _ ∧ Realize M.sets _ _) ↔ _
    rw [BoundedFormula.realize_mainPrefixTupleFormula M _ _ _ _ _ mems,
      BoundedFormula.realize_nonzeroLimitOrdinalFormula M _ _ mems,
      M.realize_mainPrefixLimitStepFormula pairing unions powers separation collection
        _ _ _ _ _ _ _ _ _ mems (by simpa only [outer, extendMany_suffix] using omega)
          (by simpa only [outer, extendMany_suffix] using ordinal)]
    simp only [outer, field, extendMany_suffix, extendMany_prefix]
  constructor
  · rintro ⟨w, ground, recognized⟩
    exact ⟨w 0, w 1, w 2, (actual w ground).1 recognized⟩
  · rintro ⟨T, S, E, oldCode, nonzero, code⟩
    have fields := M.mainPrefixCode_fields_mem (oldCode ▸ members old)
    let w : Fin 3 → ZFSet.{u} := Fin.cases T (Fin.cases S (fun _ => E))
    have ground : ∀ j, w j ∈ M.sets := Fin.cases fields.1 (Fin.cases fields.2.1 (fun _ => fields.2.2))
    exact ⟨w, ground, (actual w ground).2 ⟨oldCode, nonzero, code⟩⟩

end TransitiveGround

namespace SetFormula
def preservedMainPrefixHistoryValuesFormula {n} (K Labels C D rD N p : Fin n) : SetFormula n :=
  let old := suffixIndex n 2
  let field := prefixIndex n 2
  allBlock 2 (imp (BoundedFormula.pairMembershipFormula (field 0) (field 1) (old p)).toFormula
    (preservedMainPrefixHistoryValueFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
      (field 0) (field 1)))

def preservedMainPrefixHistoryCompatibilityFormula {n} (p : Fin n) : SetFormula n :=
  let old := suffixIndex n 4
  let field := prefixIndex n 4
  allBlock 4 (imp (BoundedFormula.conj
    (BoundedFormula.pairMembershipFormula (field 0) (field 2) (old p))
    (.conj (BoundedFormula.pairMembershipFormula (field 1) (field 3) (old p))
      (BoundedFormula.disj (.equal (field 0) (field 1)) (.mem (field 0) (field 1))))).toFormula
    (mainPrefixExtensionFormula (field 2) (field 3)))

def preservedMainPrefixHistoryFormula {n} (K Labels C D rD N A p : Fin n) : SetFormula n :=
  .conj (functionGraphOnFormula A p)
    (.conj (preservedMainPrefixHistoryValuesFormula K Labels C D rD N p)
      (preservedMainPrefixHistoryCompatibilityFormula p))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_preservedMainPrefixHistoryValuesFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n} (K Labels C D rD N p : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (preservedMainPrefixHistoryValuesFormula K Labels C D rD N p) env ↔
      ∀ i q, ZFSet.pair i q ∈ env p →
        ∃ S E, q = mainPrefixCode (insert i i) S E ∧
          MainPrefixGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (insert i i) S E ∧
          MainPrefixProfileGraphCode M (env K) (env Labels) (env C) (env D) (env rD) S E := by
  rw [preservedMainPrefixHistoryValuesFormula, realize_allBlock]
  have actual (f : Fin 2 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets
        (imp (BoundedFormula.pairMembershipFormula (prefixIndex n 2 0) (prefixIndex n 2 1)
          (suffixIndex n 2 p)).toFormula
          (preservedMainPrefixHistoryValueFormula (suffixIndex n 2 K) (suffixIndex n 2 Labels)
            (suffixIndex n 2 C) (suffixIndex n 2 D) (suffixIndex n 2 rD) (suffixIndex n 2 N)
            (prefixIndex n 2 0) (prefixIndex n 2 1))) (extendMany 2 f env) ↔
        (ZFSet.pair (f 0) (f 1) ∈ env p →
          ∃ S E, f 1 = mainPrefixCode (insert (f 0) (f 0)) S E ∧
            MainPrefixGraphCode M (env K) (env Labels) (env C) (env D) (env rD)
              (insert (f 0) (f 0)) S E ∧
            MainPrefixProfileGraphCode M (env K) (env Labels) (env C) (env D) (env rD) S E) := by
    have mems := extendMany_members 2 f env ground members
    rw [realize_imp, BoundedFormula.realize_toFormula M _ _ mems,
      BoundedFormula.truth_pairMembershipFormula]
    rw [M.realize_preservedMainPrefixHistoryValueFormula pairing unions powers separation collection
      _ _ _ _ _ _ _ _ _ mems
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)]
    simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · intro recognized i q entry
    have ground := M.transitive (members p) entry
    let f : Fin 2 → ZFSet.{u} := Fin.cases i (fun _ => q)
    have grounds : ∀ j, f j ∈ M.sets := Fin.cases (M.pair_left ground) (fun _ => M.pair_right ground)
    exact (actual f grounds).1 (recognized f grounds) entry
  · intro law f ground
    exact (actual f ground).2 (law (f 0) (f 1))

theorem realize_preservedMainPrefixHistoryCompatibilityFormula {n} (p : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (preservedMainPrefixHistoryCompatibilityFormula p) env ↔
      ∀ i j q r, ZFSet.pair i q ∈ env p → ZFSet.pair j r ∈ env p →
        (i = j ∨ i ∈ j) → MainPrefixExtends q r := by
  rw [preservedMainPrefixHistoryCompatibilityFormula, realize_allBlock]
  have actual (f : Fin 4 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (imp (BoundedFormula.conj
        (BoundedFormula.pairMembershipFormula (prefixIndex n 4 0) (prefixIndex n 4 2) (suffixIndex n 4 p))
        (.conj (BoundedFormula.pairMembershipFormula (prefixIndex n 4 1) (prefixIndex n 4 3) (suffixIndex n 4 p))
          (BoundedFormula.disj (.equal (prefixIndex n 4 0) (prefixIndex n 4 1))
            (.mem (prefixIndex n 4 0) (prefixIndex n 4 1))))).toFormula
        (mainPrefixExtensionFormula (prefixIndex n 4 2) (prefixIndex n 4 3))) (extendMany 4 f env) ↔
      ((ZFSet.pair (f 0) (f 2) ∈ env p ∧ ZFSet.pair (f 1) (f 3) ∈ env p ∧
        (f 0 = f 1 ∨ f 0 ∈ f 1)) → MainPrefixExtends (f 2) (f 3)) := by
    have mems := extendMany_members 4 f env ground members
    rw [realize_imp, BoundedFormula.realize_toFormula M _ _ mems]
    simp only [BoundedFormula.Truth, BoundedFormula.truth_pairMembershipFormula, BoundedFormula.truth_disj]
    rw [M.realize_mainPrefixExtensionFormula _ _ _ mems]
    simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · intro recognized i j q r first second before
    have hfirst := M.transitive (members p) first
    have hsecond := M.transitive (members p) second
    let f : Fin 4 → ZFSet.{u} := Fin.cases i (Fin.cases j (Fin.cases q (fun _ => r)))
    have grounds : ∀ k, f k ∈ M.sets := Fin.cases (M.pair_left hfirst)
      (Fin.cases (M.pair_left hsecond) (Fin.cases (M.pair_right hfirst) (fun _ => M.pair_right hsecond)))
    exact (actual f grounds).1 (recognized f grounds) ⟨first, second, before⟩
  · intro law f ground
    exact (actual f ground).2 (fun entries => law (f 0) (f 1) (f 2) (f 3) entries.1 entries.2.1 entries.2.2)

theorem realize_preservedMainPrefixHistoryFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n} (K Labels C D rD N A p : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (preservedMainPrefixHistoryFormula K Labels C D rD N A p) env ↔
      PreservedMainPrefixHistoryCode M (env K) (env Labels) (env C) (env D) (env rD) (env A) (env p) := by
  change (Realize M.sets (functionGraphOnFormula A p) env ∧
    Realize M.sets (preservedMainPrefixHistoryValuesFormula K Labels C D rD N p) env ∧
    Realize M.sets (preservedMainPrefixHistoryCompatibilityFormula p) env) ↔ _
  rw [M.realize_functionGraphOnFormula unions A p env members,
    M.realize_preservedMainPrefixHistoryValuesFormula pairing unions powers separation collection
      K Labels C D rD N p env members omega ordinal,
    M.realize_preservedMainPrefixHistoryCompatibilityFormula p env members]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.function, h.values, h.compatible⟩⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
