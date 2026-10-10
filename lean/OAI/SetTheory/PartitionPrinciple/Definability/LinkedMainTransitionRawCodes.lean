import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundLinkedMainStageCodeLaws

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def chronologicalMainTransitionFormula {n}
    (z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth : Fin n)
    (sourceGraphs targetGraphs : Fin 5 → Fin n) : BoundedFormula n :=
  .conj (validMainTransitionCodeFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors)
    (chronologicalTransitionExtraFormula P Q points sourceCutoff targetCutoff sourceBirth targetBirth
      sourceGraphs targetGraphs)

theorem truth_chronologicalMainTransitionFormula {n}
    (z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth : Fin n)
    (sourceGraphs targetGraphs : Fin 5 → Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (chronologicalMainTransitionFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth sourceGraphs targetGraphs) env ↔
      env z = ZFSet.pair (env points) (env actors) ∧
      MainTransitionLaws (env P) (env Q) (env rP) (env rQ) (env μP) (env μQ) (env G) (env H) (env mG) (env mH) (env oneG) (env oneH) (env AP) (env AQ) (env bP) (env bQ) (env heightP) (env heightQ) (env points) (env actors) ∧
      ChronologicalTransitionLaws (env points) (env sourceCutoff) (env targetCutoff)
        (env sourceBirth) (env targetBirth) (fun j => env (sourceGraphs j))
          (fun j => env (targetGraphs j)) := by
  change (Truth (validMainTransitionCodeFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors) env ∧
    Truth (chronologicalTransitionExtraFormula P Q points sourceCutoff targetCutoff sourceBirth targetBirth
      sourceGraphs targetGraphs) env) ↔ _
  rw [truth_validMainTransitionCodeFormula]
  constructor
  · rintro ⟨⟨encoded, laws⟩, chronological⟩
    exact ⟨encoded, laws, (truth_chronologicalTransitionExtraFormula P Q points sourceCutoff targetCutoff
      sourceBirth targetBirth sourceGraphs targetGraphs env laws.point_embedding.injection.function.1).1 chronological⟩
  · rintro ⟨encoded, laws, chronological⟩
    exact ⟨⟨encoded, laws⟩, (truth_chronologicalTransitionExtraFormula P Q points sourceCutoff targetCutoff
      sourceBirth targetBirth sourceGraphs targetGraphs env laws.point_embedding.injection.function.1).2 chronological⟩

theorem realize_chronologicalMainTransitionFormula (M : TransitiveGround.{u}) {n}
    (z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth : Fin n)
    (sourceGraphs targetGraphs : Fin 5 → Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (chronologicalMainTransitionFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth
      sourceGraphs targetGraphs).toFormula env ↔
      env z = ZFSet.pair (env points) (env actors) ∧
      MainTransitionLaws (env P) (env Q) (env rP) (env rQ) (env μP) (env μQ) (env G) (env H) (env mG) (env mH) (env oneG) (env oneH) (env AP) (env AQ) (env bP) (env bQ) (env heightP) (env heightQ) (env points) (env actors) ∧
      ChronologicalTransitionLaws (env points) (env sourceCutoff) (env targetCutoff)
        (env sourceBirth) (env targetBirth) (fun j => env (sourceGraphs j))
          (fun j => env (targetGraphs j)) :=
  (realize_toFormula M _ env members).trans
    (truth_chronologicalMainTransitionFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth sourceGraphs targetGraphs env)

def coveredChronologicalMainTransitionFormula {n}
    (z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth : Fin n)
    (sourceGraphs targetGraphs : Fin 5 → Fin n) : BoundedFormula n :=
  .conj (chronologicalMainTransitionFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth sourceGraphs targetGraphs)
    (oldBirthFiberCoverageFormula P points targetBirth sourceCutoff)

theorem truth_coveredChronologicalMainTransitionFormula {n}
    (z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth : Fin n)
    (sourceGraphs targetGraphs : Fin 5 → Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (coveredChronologicalMainTransitionFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth sourceGraphs targetGraphs) env ↔
      (env z = ZFSet.pair (env points) (env actors) ∧
      MainTransitionLaws (env P) (env Q) (env rP) (env rQ) (env μP) (env μQ) (env G) (env H) (env mG) (env mH) (env oneG) (env oneH) (env AP) (env AQ) (env bP) (env bQ) (env heightP) (env heightQ) (env points) (env actors) ∧
      ChronologicalTransitionLaws (env points) (env sourceCutoff) (env targetCutoff)
        (env sourceBirth) (env targetBirth) (fun j => env (sourceGraphs j))
          (fun j => env (targetGraphs j))) ∧
      OldBirthFiberCoverageCode (env P) (env points) (env targetBirth) (env sourceCutoff) := by
  simp only [coveredChronologicalMainTransitionFormula, Truth,
    truth_chronologicalMainTransitionFormula, truth_oldBirthFiberCoverageFormula]

theorem realize_coveredChronologicalMainTransitionFormula (M : TransitiveGround.{u}) {n}
    (z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth : Fin n)
    (sourceGraphs targetGraphs : Fin 5 → Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (coveredChronologicalMainTransitionFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth
      sourceGraphs targetGraphs).toFormula env ↔
      (env z = ZFSet.pair (env points) (env actors) ∧
      MainTransitionLaws (env P) (env Q) (env rP) (env rQ) (env μP) (env μQ) (env G) (env H) (env mG) (env mH) (env oneG) (env oneH) (env AP) (env AQ) (env bP) (env bQ) (env heightP) (env heightQ) (env points) (env actors) ∧
      ChronologicalTransitionLaws (env points) (env sourceCutoff) (env targetCutoff)
        (env sourceBirth) (env targetBirth) (fun j => env (sourceGraphs j))
          (fun j => env (targetGraphs j))) ∧
      OldBirthFiberCoverageCode (env P) (env points) (env targetBirth) (env sourceCutoff) :=
  (realize_toFormula M _ env members).trans
    (truth_coveredChronologicalMainTransitionFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth sourceGraphs targetGraphs env)

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing
open SetFormula
universe u

def LinkedTransitionLawsCode (z points actors sourceBirth targetBirth : ZFSet.{u})
    (source target : Fin 24 → ZFSet.{u}) : Prop :=
  ZFSet.pair (source 11) sourceBirth ∈ source 17 ∧
  ZFSet.pair (target 11) targetBirth ∈ target 17 ∧
  (z = ZFSet.pair points actors ∧
    MainTransitionLaws (source 0) (target 0) (source 1) (target 1) (source 2) (target 2) (source 3) (target 3) (source 4) (target 4) (source 6) (target 6) (source 7) (target 7) (source 8) (target 8) (source 10) (target 10) points actors ∧
    ChronologicalTransitionLaws points (source 11) (target 11) sourceBirth targetBirth
      (linkedChronologyGraphs source) (linkedChronologyGraphs target)) ∧
  OldBirthFiberCoverageCode (source 0) points targetBirth (source 11)

def LinkedMainTransitionRawCode (M : TransitiveGround.{u})
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth : ZFSet.{u})
    (source target : Fin 24 → ZFSet.{u}) : Prop :=
  LinkedMainStageRawCode M K Labels C D rD N sourceCode source ∧
  LinkedMainStageRawCode M K Labels C D rD N targetCode target ∧
  LinkedTransitionLawsCode z points actors sourceBirth targetBirth source target

namespace BoundedFormula

def linkedTransitionLawsFormula {n} (z points actors sourceBirth targetBirth : Fin n)
    (f g : Fin 24 → Fin n) : BoundedFormula n :=
  .conj (pairMembershipFormula (f 11) sourceBirth (f 17))
    (.conj (pairMembershipFormula (g 11) targetBirth (g 17))
      (coveredChronologicalMainTransitionFormula z (f 0) (g 0) (f 1) (g 1) (f 2) (g 2) (f 3) (g 3) (f 4) (g 4) (f 6) (g 6) (f 7) (g 7) (f 8) (g 8) (f 10) (g 10)
        points actors (f 11) (g 11) sourceBirth targetBirth
          (linkedChronologyGraphs f) (linkedChronologyGraphs g)))

theorem truth_linkedTransitionLawsFormula {n} (z points actors sourceBirth targetBirth : Fin n)
    (f g : Fin 24 → Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (linkedTransitionLawsFormula z points actors sourceBirth targetBirth f g) env ↔
      LinkedTransitionLawsCode (env z) (env points) (env actors) (env sourceBirth) (env targetBirth)
        (fun j => env (f j)) (fun j => env (g j)) := by
  have map (h : Fin 24 → Fin n) : (fun j => env (linkedChronologyGraphs h j)) =
      linkedChronologyGraphs (fun j => env (h j)) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) j
  simp only [linkedTransitionLawsFormula, Truth, truth_pairMembershipFormula,
    truth_coveredChronologicalMainTransitionFormula, map, LinkedTransitionLawsCode]

end BoundedFormula

namespace SetFormula

def linkedMainTransitionRawFormula {n}
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth : Fin n)
    (source target : Fin 24 → Fin n) : SetFormula n :=
  .conj (linkedMainStageRawFormula K Labels C D rD N sourceCode source)
    (.conj (linkedMainStageRawFormula K Labels C D rD N targetCode target)
      (BoundedFormula.linkedTransitionLawsFormula z points actors sourceBirth targetBirth source target).toFormula)

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_linkedMainTransitionRawFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n}
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth : Fin n)
    (source target : Fin 24 → Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainTransitionRawFormula K Labels C D rD N sourceCode targetCode z
      points actors sourceBirth targetBirth source target) env ↔
      LinkedMainTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD) (env N)
        (env sourceCode) (env targetCode) (env z) (env points) (env actors) (env sourceBirth) (env targetBirth)
          (fun j => env (source j)) (fun j => env (target j)) := by
  have first := M.realize_linkedMainStageRawFormula pairing unions powers separation collection
    K Labels C D rD N sourceCode source env members omega ordinal
  have second := M.realize_linkedMainStageRawFormula pairing unions powers separation collection
    K Labels C D rD N targetCode target env members omega ordinal
  have laws := (BoundedFormula.realize_toFormula M _ env members).trans
    (BoundedFormula.truth_linkedTransitionLawsFormula z points actors sourceBirth targetBirth source target env)
  exact and_congr first (and_congr second laws)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
