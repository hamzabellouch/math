import OAI.SetTheory.PartitionPrinciple.Definability.GroundRefinementLevelSingleCodes
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStageOneTestEquivalence

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

def refinementLevelTests (level T2 A : ZFSet.{u}) (p : P) : Prop :=
  ∀ (C E : L) (U Rf Rc : (M.nameDomain s).names),
    let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    idx ∈ M.niceRefinementIndices a s b d level T T2 valid →
    (∀ u w : (M.nameDomain s).names, u.val.val ∈ T → w.val.val ∈ T →
      stageOneAssignment idx u.val.val w.val.val ∈ A →
      M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
        a b d base directed system C E U Rf Rc u w p) ∧
    (∀ u u' w w' : (M.nameDomain s).names,
      u.val.val ∈ T → u'.val.val ∈ T → w.val.val ∈ T → w'.val.val ∈ T →
      stageOneAssignment idx u.val.val w.val.val ∈ A →
      stageOneAssignment idx u'.val.val w'.val.val ∈ A →
      M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
        Rf Rc u u' w w' p)

theorem refinementLevelTests_zero (T2 A : ZFSet.{u}) (p : P) :
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system ∅ T2 A p =
    M.stageOneTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system T2 A p := rfl

theorem refinementLevelTests_mono (level T2 A : ZFSet.{u}) {p q : P}
    (tests : M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 A p) (below : q ≤ p) :
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 A q := by
  intro C E U Rf Rc
  dsimp only
  intro member
  obtain ⟨single, collision⟩ := tests C E U Rf Rc member
  refine ⟨?_, ?_⟩
  · intro u w hu hw entry
    exact M.stageOneSingleTests_mono s pairing unions powers separation collection carrier order hT valid
      a b d base directed system C E U Rf Rc u w (single u w hu hw entry) below
  · intro u u' w w' hu hu' hw hw' entry entry'
    exact M.stageOneCollisionTest_mono s pairing unions powers separation collection carrier order hT valid
      Rf Rc u u' w w' (collision u u' w w' hu hu' hw hw' entry entry') below

theorem refinementLevelTests_subset (level T2 : ZFSet.{u}) {A B : ZFSet.{u}} (p : P)
    (tests : M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 A p) (subset : B ⊆ A) :
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 B p := by
  intro C E U Rf Rc
  dsimp only
  intro member
  obtain ⟨single, collision⟩ := tests C E U Rf Rc member
  exact ⟨fun u w hu hw entry => single u w hu hw (subset entry),
    fun u u' w w' hu hu' hw hw' entry entry' =>
      collision u u' w w' hu hu' hw hw' (subset entry) (subset entry')⟩

theorem refinementLevelTests_empty (level T2 : ZFSet.{u}) (p : P) :
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 ∅ p := by
  intro C E U Rf Rc
  dsimp only
  intro member
  exact ⟨fun _ _ _ _ entry => False.elim (ZFSet.notMem_empty _ entry),
    fun _ _ _ _ _ _ _ _ entry _ => False.elim (ZFSet.notMem_empty _ entry)⟩

theorem refinementLevelTests_transfer (level T2 : ZFSet.{u}) {A B : ZFSet.{u}} (p : P)
    (tests : M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 A p)
    (guards : ∀ t ∈ M.niceRefinementIndices a s b d level T T2 valid,
      ∀ u ∈ T, ∀ w ∈ T, stageOneAssignment t u w ∈ B → stageOneAssignment t u w ∈ A) :
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 B p := by
  intro C E U Rf Rc
  dsimp only
  intro member
  obtain ⟨single, collision⟩ := tests C E U Rf Rc member
  exact ⟨fun u w hu hw entry => single u w hu hw
      (guards _ member u.val.val hu w.val.val hw entry),
    fun u u' w w' hu hu' hw hw' entry entry' =>
      collision u u' w w' hu hu' hw hw'
        (guards _ member u.val.val hu w.val.val hw entry)
        (guards _ member u'.val.val hu' w'.val.val hw' entry')⟩

theorem refinementLevelTests_congr (level T2 A B : ZFSet.{u}) (p : P)
    (guards : ∀ t ∈ M.niceRefinementIndices a s b d level T T2 valid,
      ∀ u ∈ T, ∀ w ∈ T, stageOneAssignment t u w ∈ A ↔ stageOneAssignment t u w ∈ B) :
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 A p ↔
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 B p := by
  constructor
  · intro tests
    exact M.refinementLevelTests_transfer s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 p tests
      (fun t ht u hu w hw entry => (guards t ht u hu w hw).2 entry)
  · intro tests
    exact M.refinementLevelTests_transfer s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 p tests
      (fun t ht u hu w hw entry => (guards t ht u hu w hw).1 entry)

theorem refinementLevelTests_of_no_assignments (level T2 A : ZFSet.{u}) (p : P)
    (absent : ∀ t ∈ M.niceRefinementIndices a s b d level T T2 valid,
      ∀ u ∈ T, ∀ w ∈ T, stageOneAssignment t u w ∉ A) :
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 A p :=
  M.refinementLevelTests_transfer s pairing unions powers separation collection carrier order hT valid
    a b d base directed system level T2 p
    (M.refinementLevelTests_empty s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 p)
    (fun t ht u hu w hw entry => False.elim (absent t ht u hu w hw entry))

variable {I0 T2 : ZFSet.{u}}
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) (natSetCode 1))
include first second

theorem refinementLevelTests_stageTwoSplice (Aq Ap : ZFSet.{u}) (p : P) :
    let I1 := M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system (natSetCode 1) T2
        (assignmentSplice (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1) Aq Ap) p ↔
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system (natSetCode 1) T2 Ap p := by
  apply M.refinementLevelTests_congr s pairing unions powers separation collection carrier order hT valid
    a b d base directed system
  intro t ht u _ w _
  exact stageTwoAssignmentSplice_upper_iff first second Aq Ap ht

theorem refinementLevelTests_stageTwoOld {A : ZFSet.{u}} (p : P)
    (subsetOld : A ⊆ stageOneAssignments I0 T) :
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system (natSetCode 1) T2 A p := by
  apply M.refinementLevelTests_of_no_assignments s pairing unions powers separation collection carrier order
    hT valid a b d base directed system
  intro t ht u _ w _
  exact stageTwoAssignment_old_no_upper first second subsetOld ht

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

theorem refinementLevelTests_union (level T2 : ZFSet.{u}) (family : Nat → ZFSet.{u}) (rows : Nat → P) (p : P)
    (increasing : ∀ n m, n ≤ m → family n ⊆ family m)
    (below : ∀ n, p ≤ rows n)
    (tests : ∀ n, M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 (family n) (rows n)) :
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 (stageOneAssignmentUnion family) p := by
  intro C E U Rf Rc
  dsimp only
  intro index
  refine ⟨?_, ?_⟩
  · intro u w hu hw entry
    obtain ⟨n, hn⟩ := (mem_stageOneAssignmentUnion family _).1 entry
    exact M.stageOneSingleTests_mono s pairing unions powers separation collection carrier order hT valid
      a b d base directed system C E U Rf Rc u w ((tests n C E U Rf Rc index).1 u w hu hw hn) (below n)
  · intro u u' w w' hu hu' hw hw' entry entry'
    obtain ⟨n, hn⟩ := (mem_stageOneAssignmentUnion family _).1 entry
    obtain ⟨m, hm⟩ := (mem_stageOneAssignmentUnion family _).1 entry'
    have first := increasing n (max n m) (Nat.le_max_left n m) hn
    have second := increasing m (max n m) (Nat.le_max_right n m) hm
    exact M.stageOneCollisionTest_mono s pairing unions powers separation collection carrier order hT valid
      Rf Rc u u' w w' ((tests (max n m) C E U Rf Rc index).2 u u' w w' hu hu' hw hw' first second)
      (below (max n m))

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

variable {I0 T2 : ZFSet.{u}}
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) (natSetCode 1))
include first second

theorem refinementLevelTests_stageTwoUnion (A0 A1 : ZFSet.{u}) (p : P)
    (lower : A0 ⊆ stageOneAssignments I0 T) :
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system (natSetCode 1) T2 (A0 ∪ A1) p ↔
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system (natSetCode 1) T2 A1 p := by
  apply M.refinementLevelTests_congr s pairing unions powers separation collection carrier order hT valid
    a b d base directed system
  intro t ht u _ w _
  rw [ZFSet.mem_union]
  have absent := stageTwoAssignment_old_no_upper first second lower (u := u) (w := w) ht
  exact ⟨fun h => h.elim (fun impossible => False.elim (absent impossible)) id, Or.inr⟩

end

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable {T T2 : ZFSet.{u}} (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

include nodes indices in
theorem refinementLevelRawSingle_iff (C E : L) (U Rf Rc u w : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid) (p : P) :
    stageOneRawSingle M (M.refinementLevelFormulaData a s b d level T T2 valid)
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val.val w.val.val (s.encode p) ↔
      M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
        a b d base directed system C E U Rf Rc u w p := by
  have meaning := M.refinementLevelRawSingle_codes a s b d level pairing unions powers separation collection
    carrier order nodes hT valid indices C E U Rf Rc u w member p
  let bu := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rc u
  let aw := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rf w
  have codes : (fun j : Fin 3 => ((![u, w, U] : Assignment (M.nameDomain s) 3) j).val.val) =
      ![u.val.val, w.val.val, U.val.val] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) j
  have activity := M.stageOneRawForces_iff s pairing unions powers separation collection carrier order
    refinementActivityFormula p ![u, w, U]
  rw [codes] at activity
  have profile := M.stageOneRawProfile_iff s pairing unions powers separation collection carrier order
    valid a b d (T2 := T2) base directed system E bu aw p
  change stageOneRawProfile M s.carrier s.conditionOrder (s.encode p) b.carrier b.conditionOrder
    (M.niceVisibilityGraph a s b T d.principalFix) (b.encode E) bu.val.val aw.val.val ↔ _ at profile
  have compatible := M.refinementLevelRawCompatibility_iff s pairing unions powers separation collection carrier order
    hT valid a b d level base directed system indices C E U Rf Rc bu aw p member
  exact meaning.trans (and_congr activity (and_congr profile compatible))

include nodes indices in
theorem refinementLevelRawTests_iff (A : ZFSet.{u}) (p : P) :
    stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) A (s.encode p) ↔
      M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
        a b d base directed system level T2 A p := by
  have single := M.refinementLevelRawSingle_iff a s b d level pairing unions powers separation collection
    carrier order nodes hT valid indices base directed system
  have collision := M.refinementLevelRawCollision_iff a s b d level pairing unions powers separation collection
    carrier order hT valid indices
  let lift (r : ZFSet.{u}) (hr : r ∈ T) : (M.nameDomain s).names :=
    ⟨⟨r, valid r hr⟩, M.transitive hT hr⟩
  constructor
  · intro raw C E U Rf Rc
    dsimp only
    intro member
    refine ⟨?_, ?_⟩
    · intro u w hu hw entry
      exact (single C E U Rf Rc u w member p).1
        (raw.1 _ member u.val.val hu w.val.val hw entry)
    · intro u u' w w' hu hu' hw hw' entry entry'
      exact (collision C E U Rf Rc u u' w w' member p).1
        (raw.2 _ member u.val.val hu u'.val.val hu' w.val.val hw w'.val.val hw' entry entry')
  · intro typed
    refine ⟨?_, ?_⟩
    · intro t ht rawU hu rawW hw entry
      obtain ⟨C, E, U, Rf, Rc, rfl⟩ := indices.decoded t ht
      exact (single C E U Rf Rc (lift rawU hu) (lift rawW hw) ht p).2
        ((typed C E U Rf Rc ht).1 (lift rawU hu) (lift rawW hw) hu hw entry)
    · intro t ht rawU hu rawU' hu' rawW hw rawW' hw' entry entry'
      obtain ⟨C, E, U, Rf, Rc, rfl⟩ := indices.decoded t ht
      exact (collision C E U Rf Rc (lift rawU hu) (lift rawU' hu') (lift rawW hw) (lift rawW' hw') ht p).2
        ((typed C E U Rf Rc ht).2 (lift rawU hu) (lift rawU' hu') (lift rawW hw) (lift rawW' hw')
          hu hu' hw hw' entry entry')

include pairing unions powers separation collection carrier order nodes hT indices system

theorem refinementLevelRawTests_mono (A : ZFSet.{u}) {p q : P}
    (tests : stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) A (s.encode p))
    (below : q ≤ p) :
    stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) A (s.encode q) := by
  have meaning := M.refinementLevelRawTests_iff a s b d level pairing unions powers separation
    collection carrier order nodes hT valid indices base directed system
  exact (meaning A q).2 (M.refinementLevelTests_mono s pairing unions powers separation collection
    carrier order hT valid a b d base directed system level T2 A ((meaning A p).1 tests) below)

theorem refinementLevelRawTests_order_mono (A : ZFSet.{u}) {p q : ZFSet.{u}}
    (tests : stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) A p)
    (below : ZFSet.pair q p ∈ s.conditionOrder) :
    stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) A q := by
  rw [Presentation.conditionOrder, Presentation.mem_subset] at below
  obtain ⟨⟨q', p'⟩, below, equal⟩ := below
  change ZFSet.pair (s.encode q') (s.encode p') = ZFSet.pair q p at equal
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  exact M.refinementLevelRawTests_mono a s b d level pairing unions powers separation collection
    carrier order nodes hT valid indices base directed system A tests below

end PartitionPilot.Forcing.TransitiveGround

end OAI
