import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainTransitionValidity
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundChronologyFieldAppend

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

def OldBirthFiberCoverageCode (P e born cutoff : ZFSet.{u}) : Prop :=
  ∀ y t, ZFSet.pair y t ∈ born → (t = cutoff ∨ t ∈ cutoff) →
    ∃ x ∈ P, ZFSet.pair x y ∈ e

namespace OldBirthFiberCoverageCode
variable {P e old born cutoff : ZFSet.{u}}
variable (coverage : OldBirthFiberCoverageCode P e born cutoff)
include coverage

theorem fiber_entry_iff
    (preserves : ∀ x y t, ZFSet.pair x y ∈ e →
      (ZFSet.pair y t ∈ born ↔ ZFSet.pair x t ∈ old))
    {t : ZFSet.{u}} (before : t = cutoff ∨ t ∈ cutoff) (y : ZFSet.{u}) :
    ZFSet.pair y t ∈ born ↔ ∃ x ∈ P, ZFSet.pair x y ∈ e ∧ ZFSet.pair x t ∈ old := by
  constructor
  · intro entry
    obtain ⟨x, hx, image⟩ := coverage y t entry before
    exact ⟨x, hx, image, (preserves x y t image).1 entry⟩
  · rintro ⟨x, _, image, entry⟩
    exact (preserves x y t image).2 entry

theorem mono_cutoff {earlier : ZFSet.{u}} (ordinal : ordinalSetProperty cutoff)
    (before : earlier = cutoff ∨ earlier ∈ cutoff) :
    OldBirthFiberCoverageCode P e born earlier := by
  intro y t entry oldTime
  apply coverage y t entry
  rcases before with rfl | before
  · exact oldTime
  · exact Or.inr (oldTime.elim (fun equal => equal.symm ▸ before)
      (fun member => ordinal.1 earlier before t member))

end OldBirthFiberCoverageCode

structure GroundChronologicalMainStage (M : TransitiveGround.{u}) (C D rD : ZFSet.{u}) where
  stage : GroundMainStage M C D rD
  cutoff : ZFSet.{u}
  cutoff_ground : cutoff ∈ M.sets
  cutoff_ordinal : ordinalSetProperty cutoff
  history : GroundChronologicalHistory M (insert cutoff cutoff) C D rD
  carrier_eq : history.space cutoff = stage.carrier
  order_eq : history.order cutoff = stage.order
  meet_eq : history.meetGraph cutoff = stage.meetGraph
  height_eq : history.height cutoff = stage.height

namespace GroundChronologicalMainStage
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundChronologicalMainStage M C D rD)

def birth : ZFSet.{u} := stage.history.birth stage.cutoff

theorem birth_ground : stage.birth ∈ M.sets :=
  stage.history.birth_mem stage.cutoff (ZFSet.mem_insert _ _)

theorem birth_function : ZFSet.IsFunc stage.stage.carrier (insert stage.cutoff stage.cutoff) stage.birth := by
  rw [← stage.carrier_eq]
  exact stage.history.birth_function stage.cutoff (ZFSet.mem_insert _ _)

theorem birth_bound {x t : ZFSet.{u}} (entry : ZFSet.pair x t ∈ stage.birth) :
    t = stage.cutoff ∨ t ∈ stage.cutoff := by
  have hx := (ZFSet.pair_mem_prod.1 (stage.birth_function.1 entry)).1
  rw [← stage.carrier_eq] at hx
  exact stage.history.birth_bound stage.cutoff (ZFSet.mem_insert _ _) x hx t entry

theorem old_meet : OldMeetCode stage.stage.order stage.stage.meetGraph stage.birth := by
  rw [← stage.order_eq, ← stage.meet_eq]
  exact stage.history.old_meet stage.cutoff (ZFSet.mem_insert _ _)

def ofHistory (main : GroundMainStage M C D rD) {T t : ZFSet.{u}}
    (prior : GroundChronologicalHistory M T C D rD) (ordinal : ordinalSetProperty T)
    (ht : t ∈ T) (htGround : t ∈ M.sets)
    (carrier : prior.space t = main.carrier) (order : prior.order t = main.order)
    (meet : prior.meetGraph t = main.meetGraph) (height : prior.height t = main.height) :
    GroundChronologicalMainStage M C D rD where
  stage := main
  cutoff := t
  cutoff_ground := htGround
  cutoff_ordinal := ordinalSetProperty_member ordinal ht
  history := prior.restrictToCutoff ordinal ht
  carrier_eq := carrier
  order_eq := order
  meet_eq := meet
  height_eq := height

end GroundChronologicalMainStage

structure GroundChronologicalMainTransition {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
    (source target : GroundChronologicalMainStage M C D rD) where
  map : GroundMainTransition source.stage target.stage
  cutoff_le : source.cutoff = target.cutoff ∨ source.cutoff ∈ target.cutoff
  birth : ∀ x y t, ZFSet.pair x y ∈ map.points →
    (ZFSet.pair y t ∈ target.birth ↔ ZFSet.pair x t ∈ source.birth)
  history_prefix : ∀ s, s = source.cutoff ∨ s ∈ source.cutoff →
    target.history.space s = source.history.space s ∧
    target.history.order s = source.history.order s ∧
    target.history.meetGraph s = source.history.meetGraph s ∧
    target.history.birth s = source.history.birth s ∧
    target.history.height s = source.history.height s

namespace GroundChronologicalMainTransition
open SetFormula
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

theorem prefix_bound {source target : GroundChronologicalMainStage M C D rD}
    (transition : GroundChronologicalMainTransition source target) {s : ZFSet.{u}}
    (before : s = source.cutoff ∨ s ∈ source.cutoff) : s = target.cutoff ∨ s ∈ target.cutoff := by
  rcases transition.cutoff_le with equal | lower
  · exact equal ▸ before
  · right
    rcases before with rfl | before
    · exact lower
    · exact target.cutoff_ordinal.1 source.cutoff lower s before

noncomputable def identity (stage : GroundChronologicalMainStage M C D rD) :
    GroundChronologicalMainTransition stage stage where
  map := GroundMainTransition.identity pairing unions powers separation stage.stage
  cutoff_le := Or.inl rfl
  birth := by
    intro x y t entry
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 entry
    exact Iff.rfl
  history_prefix := fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩

noncomputable def comp {source middle target : GroundChronologicalMainStage M C D rD}
    (first : GroundChronologicalMainTransition source middle)
    (second : GroundChronologicalMainTransition middle target) :
    GroundChronologicalMainTransition source target where
  map := first.map.comp pairing unions powers separation second.map
  cutoff_le := second.prefix_bound first.cutoff_le
  birth := by
    intro x y t entry
    obtain ⟨_, _, z, _, xz, zy⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    exact (second.birth z y t zy).trans (first.birth x z t xz)
  history_prefix := by
    intro s before
    have a := first.history_prefix s before
    have b := second.history_prefix s (first.prefix_bound before)
    exact ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.1.trans a.2.2.1,
      b.2.2.2.1.trans a.2.2.2.1, b.2.2.2.2.trans a.2.2.2.2⟩

@[ext] theorem ext {source target : GroundChronologicalMainStage M C D rD}
    {first second : GroundChronologicalMainTransition source target} (same : first.map = second.map) :
    first = second := by
  cases first
  cases second
  cases same
  rfl

end GroundChronologicalMainTransition

end

section
open SetFormula
universe u

def ChronologyGraphPrefixCode (cutoff : ZFSet.{u}) (source target : Fin 5 → ZFSet.{u}) : Prop :=
  ∀ j s, s = cutoff ∨ s ∈ cutoff → ∀ x,
    ZFSet.pair s x ∈ source j ↔ ZFSet.pair s x ∈ target j

structure ChronologicalTransitionLaws (points sourceCutoff targetCutoff sourceBirth targetBirth : ZFSet.{u})
    (sourceGraphs targetGraphs : Fin 5 → ZFSet.{u}) : Prop where
  cutoff_le : sourceCutoff = targetCutoff ∨ sourceCutoff ∈ targetCutoff
  birth : ∀ x y t, ZFSet.pair x y ∈ points →
    (ZFSet.pair y t ∈ targetBirth ↔ ZFSet.pair x t ∈ sourceBirth)
  history_prefix : ChronologyGraphPrefixCode sourceCutoff sourceGraphs targetGraphs

namespace BoundedFormula

def graphCutoffEqualityFormula {n} (cutoff source target : Fin n) : BoundedFormula n :=
  .conj (graphFiberEqualityFormula cutoff cutoff source target)
    (.allMem cutoff (graphFiberEqualityFormula 0 0 source.succ target.succ))

theorem truth_graphCutoffEqualityFormula {n} (cutoff source target : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (graphCutoffEqualityFormula cutoff source target) env ↔
      ∀ s, s = env cutoff ∨ s ∈ env cutoff → ∀ x,
        ZFSet.pair s x ∈ env source ↔ ZFSet.pair s x ∈ env target := by
  simp only [graphCutoffEqualityFormula, Truth, truth_graphFiberEqualityFormula]
  constructor
  · rintro ⟨terminal, earlier⟩ s (rfl | hs) x
    · exact terminal x
    · exact earlier s hs x
  · intro h
    exact ⟨h _ (Or.inl rfl), fun s hs => h s (Or.inr hs)⟩

def chronologyGraphPrefixFormula {n} (cutoff : Fin n) (source target : Fin 5 → Fin n) :
    BoundedFormula n :=
  .conj (graphCutoffEqualityFormula cutoff (source 0) (target 0))
    (.conj (graphCutoffEqualityFormula cutoff (source 1) (target 1))
      (.conj (graphCutoffEqualityFormula cutoff (source 2) (target 2))
        (.conj (graphCutoffEqualityFormula cutoff (source 3) (target 3))
          (graphCutoffEqualityFormula cutoff (source 4) (target 4)))))

theorem truth_chronologyGraphPrefixFormula {n} (cutoff : Fin n) (source target : Fin 5 → Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (chronologyGraphPrefixFormula cutoff source target) env ↔
      ChronologyGraphPrefixCode (env cutoff) (fun j => env (source j)) (fun j => env (target j)) := by
  simp only [chronologyGraphPrefixFormula, Truth, truth_graphCutoffEqualityFormula]
  exact ⟨fun ⟨a, b, c, d, e⟩ => Fin.cases a (Fin.cases b (Fin.cases c
      (Fin.cases d (Fin.cases e (fun i => Fin.elim0 i))))),
    fun h => ⟨h 0, h 1, h 2, h 3, h 4⟩⟩

def chronologicalTransitionExtraFormula {n}
    (P Q points sourceCutoff targetCutoff sourceBirth targetBirth : Fin n)
    (sourceGraphs targetGraphs : Fin 5 → Fin n) : BoundedFormula n :=
  .conj (disj (.equal sourceCutoff targetCutoff) (.mem sourceCutoff targetCutoff))
    (.conj (transitionHeightFormula P Q sourceBirth targetBirth points)
      (chronologyGraphPrefixFormula sourceCutoff sourceGraphs targetGraphs))

theorem truth_chronologicalTransitionExtraFormula {n}
    (P Q points sourceCutoff targetCutoff sourceBirth targetBirth : Fin n)
    (sourceGraphs targetGraphs : Fin 5 → Fin n) (env : Fin n → ZFSet.{u})
    (shape : env points ⊆ ZFSet.prod (env P) (env Q)) :
    Truth (chronologicalTransitionExtraFormula P Q points sourceCutoff targetCutoff
      sourceBirth targetBirth sourceGraphs targetGraphs) env ↔
      ChronologicalTransitionLaws (env points) (env sourceCutoff) (env targetCutoff)
        (env sourceBirth) (env targetBirth) (fun j => env (sourceGraphs j))
          (fun j => env (targetGraphs j)) := by
  simp only [chronologicalTransitionExtraFormula, Truth, truth_disj, transitionHeightFormula,
    truth_imp, truth_pairMembershipFormula, truth_graphFiberEqualityFormula,
    truth_chronologyGraphPrefixFormula]
  constructor
  · rintro ⟨cutoff, birth, history⟩
    refine ⟨cutoff, ?_, history⟩
    intro x y t entry
    have bounds := ZFSet.pair_mem_prod.1 (shape entry)
    exact birth x bounds.1 y bounds.2 entry t
  · intro h
    exact ⟨h.cutoff_le, fun x _ y _ entry t => h.birth x y t entry, h.history_prefix⟩

theorem realize_chronologicalTransitionExtraFormula (M : TransitiveGround.{u}) {n}
    (P Q points sourceCutoff targetCutoff sourceBirth targetBirth : Fin n)
    (sourceGraphs targetGraphs : Fin 5 → Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (shape : env points ⊆ ZFSet.prod (env P) (env Q)) :
    Realize M.sets (chronologicalTransitionExtraFormula P Q points sourceCutoff targetCutoff
      sourceBirth targetBirth sourceGraphs targetGraphs).toFormula env ↔
      ChronologicalTransitionLaws (env points) (env sourceCutoff) (env targetCutoff)
        (env sourceBirth) (env targetBirth) (fun j => env (sourceGraphs j))
          (fun j => env (targetGraphs j)) :=
  (realize_toFormula M _ env members).trans
    (truth_chronologicalTransitionExtraFormula P Q points sourceCutoff targetCutoff
      sourceBirth targetBirth sourceGraphs targetGraphs env shape)

def oldBirthFiberCoverageFormula {n} (P points birth cutoff : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ
  .allMem birth (.allMem 0 (.allMem 0 (.allMem 2 (.allMem 0
    (imp (.conj (orderedPairFormula 4 2 0)
      (disj (.equal 0 (lift cutoff)) (.mem 0 (lift cutoff))))
      (exMem (lift P) (pairMembershipFormula 0 3 (lift points).succ)))))))

theorem truth_oldBirthFiberCoverageFormula {n} (P points birth cutoff : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (oldBirthFiberCoverageFormula P points birth cutoff) env ↔
      OldBirthFiberCoverageCode (env P) (env points) (env birth) (env cutoff) := by
  simp only [oldBirthFiberCoverageFormula, Truth, truth_imp, truth_orderedPairFormula,
    truth_disj, truth_exMem, truth_pairMembershipFormula]
  change (∀ p ∈ env birth, ∀ a ∈ p, ∀ y ∈ a, ∀ b ∈ p, ∀ t ∈ b,
    (p = ZFSet.pair y t ∧ (t = env cutoff ∨ t ∈ env cutoff)) →
      ∃ x ∈ env P, ZFSet.pair x y ∈ env points) ↔ _
  constructor
  · intro h y t entry before
    exact h (ZFSet.pair y t) entry {y, t} (ZFSet.mem_pair.2 (Or.inr rfl)) y
      (ZFSet.mem_pair.2 (Or.inl rfl)) {y, t} (ZFSet.mem_pair.2 (Or.inr rfl)) t
      (ZFSet.mem_pair.2 (Or.inr rfl)) ⟨rfl, before⟩
  · intro h p hp a _ y _ b _ t _ data
    exact h y t (data.1 ▸ hp) data.2

end BoundedFormula

end

namespace GroundChronologicalMainTransition
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source middle target : GroundChronologicalMainStage M C D rD}

def CoversOldBirths (transition : GroundChronologicalMainTransition source target) : Prop :=
  OldBirthFiberCoverageCode source.stage.carrier transition.map.points target.birth source.cutoff

theorem CoversOldBirths.fiber_entry_iff
    {transition : GroundChronologicalMainTransition source target} (coverage : transition.CoversOldBirths)
    {t : ZFSet.{u}} (before : t = source.cutoff ∨ t ∈ source.cutoff) (y : ZFSet.{u}) :
    ZFSet.pair y t ∈ target.birth ↔ ∃ x ∈ source.stage.carrier,
      ZFSet.pair x y ∈ transition.map.points ∧ ZFSet.pair x t ∈ source.birth :=
  OldBirthFiberCoverageCode.fiber_entry_iff coverage transition.birth before y

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

theorem identity_coversOldBirths (stage : GroundChronologicalMainStage M C D rD) :
    (identity pairing unions powers separation stage).CoversOldBirths := by
  intro y t entry _
  have hy := (ZFSet.pair_mem_prod.1 (stage.birth_function.1 entry)).1
  exact ⟨y, hy, (pair_mem_identityFunctionGraph _ _ _).2 ⟨rfl, hy⟩⟩

theorem CoversOldBirths.comp
    {first : GroundChronologicalMainTransition source middle}
    {second : GroundChronologicalMainTransition middle target}
    (firstCoverage : first.CoversOldBirths) (secondCoverage : second.CoversOldBirths) :
    (first.comp pairing unions powers separation second).CoversOldBirths := by
  intro y t entry before
  have middleTime := first.prefix_bound before
  obtain ⟨z, hz, zy⟩ := secondCoverage y t entry middleTime
  have intermediate := (second.birth z y t zy).1 entry
  obtain ⟨x, hx, xz⟩ := firstCoverage z t intermediate before
  have hy := (ZFSet.pair_mem_prod.1 (target.birth_function.1 entry)).1
  exact ⟨x, hx, (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hx, hy, z, hz, xz, zy⟩⟩

end GroundChronologicalMainTransition

namespace GroundChronologicalMainTransition
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

@[simp] theorem identity_comp {source target : GroundChronologicalMainStage M C D rD}
    (f : GroundChronologicalMainTransition source target) :
    comp pairing unions powers separation (identity pairing unions powers separation source) f = f := by
  apply ext
  exact GroundMainTransition.identity_comp pairing unions powers separation f.map

@[simp] theorem comp_identity {source target : GroundChronologicalMainStage M C D rD}
    (f : GroundChronologicalMainTransition source target) :
    comp pairing unions powers separation f (identity pairing unions powers separation target) = f := by
  apply ext
  exact GroundMainTransition.comp_identity pairing unions powers separation f.map

theorem comp_assoc {source first second target : GroundChronologicalMainStage M C D rD}
    (f : GroundChronologicalMainTransition source first)
    (g : GroundChronologicalMainTransition first second)
    (h : GroundChronologicalMainTransition second target) :
    comp pairing unions powers separation (comp pairing unions powers separation f g) h =
      comp pairing unions powers separation f (comp pairing unions powers separation g h) := by
  apply ext
  exact GroundMainTransition.comp_assoc pairing unions powers separation f.map g.map h.map

end GroundChronologicalMainTransition

section
open SetFormula
universe u v

structure GroundChronologicalMainDiagram (M : TransitiveGround.{u}) (C D rD : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (I : Type v) [Preorder I] where
  stage : I → GroundChronologicalMainStage M C D rD
  transition : ∀ {i j}, i ≤ j → GroundChronologicalMainTransition (stage i) (stage j)
  self : ∀ i, transition (le_refl i) =
    GroundChronologicalMainTransition.identity pairing unions powers separation (stage i)
  comp : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k), transition (le_trans hij hjk) =
    (transition hij).comp pairing unions powers separation (transition hjk)

namespace GroundChronologicalMainDiagram
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Preorder I]

def CoversOldBirths (diagram : GroundChronologicalMainDiagram M C D rD pairing unions powers separation I) : Prop :=
  ∀ {i j} (before : i ≤ j), (diagram.transition before).CoversOldBirths

end GroundChronologicalMainDiagram

end

namespace GroundChronologicalMainDiagram
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {source target : GroundChronologicalMainStage M C D rD}
variable (step : GroundChronologicalMainTransition source target)

def twoStageStage (source target : GroundChronologicalMainStage M C D rD) :
    Fin 2 → GroundChronologicalMainStage M C D rD :=
  Fin.cases source (fun _ => target)

noncomputable def twoStageTransition : ∀ {i j : Fin 2}, i ≤ j →
    GroundChronologicalMainTransition (twoStageStage source target i) (twoStageStage source target j) := by
  intro i j before
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact GroundChronologicalMainTransition.identity pairing unions powers separation source
    | succ j => exact step
  | succ i =>
    cases j using Fin.cases with
    | zero => exact False.elim (Nat.not_succ_le_zero i.val before)
    | succ j => exact GroundChronologicalMainTransition.identity pairing unions powers separation target

theorem twoStage_index_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  obtain ⟨n, bound⟩ := i
  cases n with
  | zero => exact Or.inl rfl
  | succ n =>
    have zero : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ bound))
    subst n
    exact Or.inr rfl

theorem twoStageTransition_self (i : Fin 2) :
    twoStageTransition pairing unions powers separation step (le_refl i) =
      GroundChronologicalMainTransition.identity pairing unions powers separation (twoStageStage source target i) := by
  rcases twoStage_index_cases i with rfl | rfl <;> rfl

theorem twoStageTransition_comp {i j k : Fin 2} (hij : i ≤ j) (hjk : j ≤ k) :
    twoStageTransition pairing unions powers separation step (le_trans hij hjk) =
      (twoStageTransition pairing unions powers separation step hij).comp pairing unions powers separation
        (twoStageTransition pairing unions powers separation step hjk) := by
  rcases twoStage_index_cases i with rfl | rfl <;>
    rcases twoStage_index_cases j with rfl | rfl <;>
      rcases twoStage_index_cases k with rfl | rfl
  · exact (GroundChronologicalMainTransition.identity_comp pairing unions powers separation _).symm
  · exact (GroundChronologicalMainTransition.identity_comp pairing unions powers separation step).symm
  · exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hjk)
  · exact (GroundChronologicalMainTransition.comp_identity pairing unions powers separation step).symm
  · exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hij)
  · exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hij)
  · exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hjk)
  · exact (GroundChronologicalMainTransition.identity_comp pairing unions powers separation _).symm

noncomputable def twoStage : GroundChronologicalMainDiagram M C D rD pairing unions powers separation (Fin 2) where
  stage := twoStageStage source target
  transition := twoStageTransition pairing unions powers separation step
  self := twoStageTransition_self pairing unions powers separation step
  comp := twoStageTransition_comp pairing unions powers separation step

theorem twoStage_stage_zero : (twoStage pairing unions powers separation step).stage 0 = source := rfl

theorem twoStage_stage_one : (twoStage pairing unions powers separation step).stage 1 = target := rfl

theorem twoStage_transition_zero_one :
    (twoStage pairing unions powers separation step).transition (show (0 : Fin 2) ≤ 1 from by decide) = step := rfl

theorem twoStage_coversOldBirths (coverage : step.CoversOldBirths) :
    (twoStage pairing unions powers separation step).CoversOldBirths := by
  intro i j before
  rcases twoStage_index_cases i with rfl | rfl <;> rcases twoStage_index_cases j with rfl | rfl
  · exact GroundChronologicalMainTransition.identity_coversOldBirths pairing unions powers separation source
  · exact coverage
  · exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) before)
  · exact GroundChronologicalMainTransition.identity_coversOldBirths pairing unions powers separation target

end GroundChronologicalMainDiagram

end PartitionPilot.Forcing

end OAI
