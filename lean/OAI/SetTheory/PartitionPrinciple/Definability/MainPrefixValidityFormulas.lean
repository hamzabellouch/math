import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundLinkedMainStageLevels

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace BoundedFormula

def pairedTransitionEntryFormula {n} (i j p a E : Fin n) : BoundedFormula n :=
  exMem E (exMem 0 (exMem 0 (.conj
    (orderedPairFormula 0 p.succ.succ.succ a.succ.succ.succ)
    (orderedTripleFormula 2 j.succ.succ.succ i.succ.succ.succ 0))))

theorem truth_pairedTransitionEntryFormula {n} (i j p a E : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (pairedTransitionEntryFormula i j p a E) env ↔
      ZFSet.pair (ZFSet.pair (env j) (env i)) (ZFSet.pair (env p) (env a)) ∈ env E := by
  simp only [pairedTransitionEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_orderedTripleFormula]
  change (∃ w ∈ env E, ∃ b ∈ w, ∃ c ∈ b, c = ZFSet.pair (env p) (env a) ∧
    w = ZFSet.pair (ZFSet.pair (env j) (env i)) c) ↔ _
  constructor
  · rintro ⟨w, hw, b, _, c, _, rfl, rfl⟩
    exact hw
  · intro entry
    refine ⟨_, entry, {ZFSet.pair (env j) (env i), ZFSet.pair (env p) (env a)},
      ZFSet.mem_pair.2 (Or.inr rfl), _, ZFSet.mem_pair.2 (Or.inr rfl), rfl, rfl⟩

end BoundedFormula

namespace SetFormula

def mainPrefixIdentityFormula {n} (E : Fin n) : SetFormula n :=
  let v := prefixIndex n 3
  allBlock 3 (BoundedFormula.imp
    (BoundedFormula.pairedTransitionEntryFormula (v 0) (v 0) (v 1) (v 2) (suffixIndex n 3 E))
    (.conj (BoundedFormula.graphDiagonalFormula (v 1))
      (BoundedFormula.graphDiagonalFormula (v 2)))).toFormula

def mainPrefixCompositionFormula {n} (E : Fin n) : SetFormula n :=
  let v := prefixIndex n 9
  let old := suffixIndex n 9 E
  allBlock 9 (BoundedFormula.imp
    (BoundedFormula.pairedTransitionEntryFormula (v 0) (v 1) (v 3) (v 4) old)
    (BoundedFormula.imp
      (BoundedFormula.pairedTransitionEntryFormula (v 1) (v 2) (v 5) (v 6) old)
      (BoundedFormula.imp
        (BoundedFormula.pairedTransitionEntryFormula (v 0) (v 2) (v 7) (v 8) old)
        (.conj (BoundedFormula.graphCompositionFormula (v 3) (v 5) (v 7))
          (BoundedFormula.graphCompositionFormula (v 4) (v 6) (v 8)))))).toFormula

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixIdentityFormula {n} (E : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixIdentityFormula E) env ↔
      ∀ i p a, ZFSet.pair (ZFSet.pair i i) (ZFSet.pair p a) ∈ env E →
        GraphDiagonalCode p ∧ GraphDiagonalCode a := by
  rw [mainPrefixIdentityFormula, realize_allBlock]
  have actual (fields : Fin 3 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :=
    BoundedFormula.realize_toFormula M
      (BoundedFormula.imp
        (BoundedFormula.pairedTransitionEntryFormula (prefixIndex n 3 0) (prefixIndex n 3 0)
          (prefixIndex n 3 1) (prefixIndex n 3 2) (suffixIndex n 3 E))
        (.conj (BoundedFormula.graphDiagonalFormula (prefixIndex n 3 1))
          (BoundedFormula.graphDiagonalFormula (prefixIndex n 3 2))))
      (extendMany 3 fields env) (extendMany_members 3 fields env ground members)
  simp only [BoundedFormula.truth_imp, BoundedFormula.Truth,
    BoundedFormula.truth_pairedTransitionEntryFormula, BoundedFormula.truth_graphDiagonalFormula,
    extendMany_prefix, extendMany_suffix] at actual
  constructor
  · intro recognized i p a entry
    have hg := M.transitive (members E) entry
    let fields : Fin 3 → ZFSet.{u} := Fin.cases i (Fin.cases p (fun _ => a))
    have ground : ∀ j, fields j ∈ M.sets := Fin.cases (M.pair_left (M.pair_left hg))
      (Fin.cases (M.pair_left (M.pair_right hg)) (fun _ => M.pair_right (M.pair_right hg)))
    exact (actual fields ground).1 (recognized fields ground) entry
  · intro law fields ground
    exact (actual fields ground).2 (law (fields 0) (fields 1) (fields 2))

theorem realize_mainPrefixCompositionFormula {n} (E : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixCompositionFormula E) env ↔
      ∀ i j k p₁ a₁ p₂ a₂ p₃ a₃,
        ZFSet.pair (ZFSet.pair j i) (ZFSet.pair p₁ a₁) ∈ env E →
        ZFSet.pair (ZFSet.pair k j) (ZFSet.pair p₂ a₂) ∈ env E →
        ZFSet.pair (ZFSet.pair k i) (ZFSet.pair p₃ a₃) ∈ env E →
        GraphCompositionCode p₁ p₂ p₃ ∧ GraphCompositionCode a₁ a₂ a₃ := by
  rw [mainPrefixCompositionFormula, realize_allBlock]
  have actual (fields : Fin 9 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :=
    BoundedFormula.realize_toFormula M
      (BoundedFormula.imp
        (BoundedFormula.pairedTransitionEntryFormula (prefixIndex n 9 0) (prefixIndex n 9 1)
          (prefixIndex n 9 3) (prefixIndex n 9 4) (suffixIndex n 9 E))
        (BoundedFormula.imp
          (BoundedFormula.pairedTransitionEntryFormula (prefixIndex n 9 1) (prefixIndex n 9 2)
            (prefixIndex n 9 5) (prefixIndex n 9 6) (suffixIndex n 9 E))
          (BoundedFormula.imp
            (BoundedFormula.pairedTransitionEntryFormula (prefixIndex n 9 0) (prefixIndex n 9 2)
              (prefixIndex n 9 7) (prefixIndex n 9 8) (suffixIndex n 9 E))
            (.conj (BoundedFormula.graphCompositionFormula (prefixIndex n 9 3) (prefixIndex n 9 5) (prefixIndex n 9 7))
              (BoundedFormula.graphCompositionFormula (prefixIndex n 9 4) (prefixIndex n 9 6) (prefixIndex n 9 8))))))
      (extendMany 9 fields env) (extendMany_members 9 fields env ground members)
  simp only [BoundedFormula.truth_imp, BoundedFormula.Truth,
    BoundedFormula.truth_pairedTransitionEntryFormula, BoundedFormula.truth_graphCompositionFormula,
    extendMany_prefix, extendMany_suffix] at actual
  constructor
  · intro recognized i j k p₁ a₁ p₂ a₂ p₃ a₃ first second third
    have h₁ := M.transitive (members E) first
    have h₂ := M.transitive (members E) second
    have h₃ := M.transitive (members E) third
    let fields : Fin 9 → ZFSet.{u} := Fin.cases i (Fin.cases j (Fin.cases k (Fin.cases p₁
      (Fin.cases a₁ (Fin.cases p₂ (Fin.cases a₂ (Fin.cases p₃ (fun _ => a₃))))))))
    have ground : ∀ a, fields a ∈ M.sets := Fin.cases (M.pair_right (M.pair_left h₁))
      (Fin.cases (M.pair_left (M.pair_left h₁)) (Fin.cases (M.pair_left (M.pair_left h₂))
      (Fin.cases (M.pair_left (M.pair_right h₁)) (Fin.cases (M.pair_right (M.pair_right h₁))
      (Fin.cases (M.pair_left (M.pair_right h₂)) (Fin.cases (M.pair_right (M.pair_right h₂))
      (Fin.cases (M.pair_left (M.pair_right h₃)) (fun _ => M.pair_right (M.pair_right h₃)))))))))
    exact (actual fields ground).1 (recognized fields ground) first second third
  · intro law fields ground
    exact (actual fields ground).2 (law (fields 0) (fields 1) (fields 2) (fields 3)
      (fields 4) (fields 5) (fields 6) (fields 7) (fields 8))

end TransitiveGround

namespace SetFormula

def mainPrefixStagesFormula {n} (K Labels C D rD N S : Fin n) : SetFormula n :=
  let old := suffixIndex n 2
  let v := prefixIndex n 2
  allBlock 2 (imp (BoundedFormula.pairMembershipFormula (v 0) (v 1) (old S)).toFormula
    (linkedMainStageFormula (old K) (old Labels) (old C) (old D) (old rD) (old N) (v 1)))

def mainPrefixTransitionsFormula {n} (K Labels C D rD N S E : Fin n) : SetFormula n :=
  let old := suffixIndex n 5
  let v := prefixIndex n 5
  allBlock 5 (imp (BoundedFormula.conj
    (BoundedFormula.pairMembershipFormula (v 0) (v 2) (old S))
    (.conj (BoundedFormula.pairMembershipFormula (v 1) (v 3) (old S))
      (BoundedFormula.tripleMembershipFormula (v 1) (v 0) (v 4) (old E)))).toFormula
    (linkedMainTransitionFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
      (v 2) (v 3) (v 4)))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_mainPrefixStagesFormula {n} (K Labels C D rD N S : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixStagesFormula K Labels C D rD N S) env ↔
      ∀ i a, ZFSet.pair i a ∈ env S →
        ∃ linked : GroundLinkedMainStage M (env K) (env Labels) (env C) (env D) (env rD),
          linked.code = a := by
  rw [mainPrefixStagesFormula, realize_allBlock]
  have actual (fields : Fin 2 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :
      Realize M.sets
        (imp (BoundedFormula.pairMembershipFormula (prefixIndex n 2 0) (prefixIndex n 2 1)
          (suffixIndex n 2 S)).toFormula
          (linkedMainStageFormula (suffixIndex n 2 K) (suffixIndex n 2 Labels)
            (suffixIndex n 2 C) (suffixIndex n 2 D) (suffixIndex n 2 rD)
            (suffixIndex n 2 N) (prefixIndex n 2 1))) (extendMany 2 fields env) ↔
        ZFSet.pair (fields 0) (fields 1) ∈ env S →
          ∃ linked : GroundLinkedMainStage M (env K) (env Labels) (env C) (env D) (env rD),
            linked.code = fields 1 := by
    rw [realize_imp, BoundedFormula.realize_toFormula M _ _
      (extendMany_members 2 fields env ground members), BoundedFormula.truth_pairMembershipFormula,
      M.realize_linkedMainStageFormula pairing unions powers separation collection _ _ _ _ _ _ _ _
        (extendMany_members 2 fields env ground members)
        (by simpa only [extendMany_suffix] using omega)
        (by simpa only [extendMany_suffix] using ordinal)]
    simp only [extendMany_prefix, extendMany_suffix]
    rfl
  constructor
  · intro recognized i a entry
    have hg := M.transitive (members S) entry
    let fields : Fin 2 → ZFSet.{u} := Fin.cases i (fun _ => a)
    have ground : ∀ j, fields j ∈ M.sets := Fin.cases (M.pair_left hg) (fun _ => M.pair_right hg)
    exact (actual fields ground).1 (recognized fields ground) entry
  · intro law fields ground
    exact (actual fields ground).2 (law (fields 0) (fields 1))

theorem realize_mainPrefixTransitionsFormula {n} (K Labels C D rD N S E : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixTransitionsFormula K Labels C D rD N S E) env ↔
      ∀ i j a b z, ZFSet.pair i a ∈ env S → ZFSet.pair j b ∈ env S →
        ZFSet.pair (ZFSet.pair j i) z ∈ env E →
        LinkedMainTransitionCode M (env K) (env Labels) (env C) (env D) (env rD) a b z := by
  rw [mainPrefixTransitionsFormula, realize_allBlock]
  have actual (fields : Fin 5 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :
      Realize M.sets
        (imp (BoundedFormula.conj
          (BoundedFormula.pairMembershipFormula (prefixIndex n 5 0) (prefixIndex n 5 2) (suffixIndex n 5 S))
          (.conj (BoundedFormula.pairMembershipFormula (prefixIndex n 5 1) (prefixIndex n 5 3) (suffixIndex n 5 S))
            (BoundedFormula.tripleMembershipFormula (prefixIndex n 5 1) (prefixIndex n 5 0) (prefixIndex n 5 4)
              (suffixIndex n 5 E)))).toFormula
          (linkedMainTransitionFormula (suffixIndex n 5 K) (suffixIndex n 5 Labels) (suffixIndex n 5 C)
            (suffixIndex n 5 D) (suffixIndex n 5 rD) (suffixIndex n 5 N)
            (prefixIndex n 5 2) (prefixIndex n 5 3) (prefixIndex n 5 4))) (extendMany 5 fields env) ↔
        (ZFSet.pair (fields 0) (fields 2) ∈ env S ∧ ZFSet.pair (fields 1) (fields 3) ∈ env S ∧
          ZFSet.pair (ZFSet.pair (fields 1) (fields 0)) (fields 4) ∈ env E) →
        LinkedMainTransitionCode M (env K) (env Labels) (env C) (env D) (env rD)
          (fields 2) (fields 3) (fields 4) := by
    rw [realize_imp, BoundedFormula.realize_toFormula M _ _
      (extendMany_members 5 fields env ground members)]
    simp only [BoundedFormula.Truth, BoundedFormula.truth_pairMembershipFormula,
      BoundedFormula.truth_tripleMembershipFormula]
    rw [M.realize_linkedMainTransitionFormula pairing unions powers separation collection _ _ _ _ _ _ _ _ _ _
      (extendMany_members 5 fields env ground members)
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)]
    simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · intro recognized i j a b z first second third
    have h₁ := M.transitive (members S) first
    have h₂ := M.transitive (members S) second
    have h₃ := M.transitive (members E) third
    let fields : Fin 5 → ZFSet.{u} := Fin.cases i (Fin.cases j (Fin.cases a (Fin.cases b (fun _ => z))))
    have ground : ∀ k, fields k ∈ M.sets := Fin.cases (M.pair_left h₁)
      (Fin.cases (M.pair_left h₂) (Fin.cases (M.pair_right h₁)
        (Fin.cases (M.pair_right h₂) (fun _ => M.pair_right h₃))))
    exact (actual fields ground).1 (recognized fields ground) ⟨first, second, third⟩
  · intro law fields ground
    exact (actual fields ground).2 (fun entries =>
      law (fields 0) (fields 1) (fields 2) (fields 3) (fields 4) entries.1 entries.2.1 entries.2.2)

end TransitiveGround
end PartitionPilot.Forcing

end OAI
