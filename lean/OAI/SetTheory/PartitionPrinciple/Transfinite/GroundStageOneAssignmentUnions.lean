import OAI.SetTheory.PartitionPrinciple.Geometry.GroundNiceRefinementVisibility

namespace OAI

namespace PartitionPilot.Forcing

section
universe u
namespace BoundedFormula

def refinementActivityFormula : BoundedFormula 3 :=
  .conj (.mem 0 2) (.mem 1 2)

def refinementCollisionFormula : BoundedFormula 4 :=
  .conj (imp (.equal 0 1) (.equal 2 3)) (imp (.equal 2 3) (.equal 0 1))

def refinementProfileFormula : BoundedFormula 3 :=
  .conj (imp (.mem 0 2) (.mem 1 2)) (imp (.mem 1 2) (.mem 0 2))

def refinementCompatibilityFormula : BoundedFormula 4 :=
  imp (.mem 0 1) (pairMembershipFormula 0 2 3)

theorem truth_refinementActivityFormula (env : Fin 3 → ZFSet.{u}) :
    Truth refinementActivityFormula env ↔ env 0 ∈ env 2 ∧ env 1 ∈ env 2 := Iff.rfl

theorem truth_refinementCollisionFormula (env : Fin 4 → ZFSet.{u}) :
    Truth refinementCollisionFormula env ↔ (env 0 = env 1 ↔ env 2 = env 3) := by
  simp only [refinementCollisionFormula, Truth, truth_imp]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem truth_refinementProfileFormula (env : Fin 3 → ZFSet.{u}) :
    Truth refinementProfileFormula env ↔ (env 0 ∈ env 2 ↔ env 1 ∈ env 2) := by
  simp only [refinementProfileFormula, Truth, truth_imp]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem truth_refinementCompatibilityFormula (env : Fin 4 → ZFSet.{u}) :
    Truth refinementCompatibilityFormula env ↔
      (env 0 ∈ env 1 → ZFSet.pair (env 0) (env 2) ∈ env 3) := by
  rw [refinementCompatibilityFormula, truth_imp, truth_pairMembershipFormula]
  rfl

end BoundedFormula
namespace SetFormula

def refinementActivityFormula : SetFormula 3 := BoundedFormula.refinementActivityFormula.toFormula

def refinementCollisionFormula : SetFormula 4 := BoundedFormula.refinementCollisionFormula.toFormula

def refinementProfileFormula : SetFormula 3 := BoundedFormula.refinementProfileFormula.toFormula

def refinementCompatibilityFormula : SetFormula 4 := BoundedFormula.refinementCompatibilityFormula.toFormula

end SetFormula
namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_refinementActivityFormula (env : Fin 3 → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets refinementActivityFormula env ↔ env 0 ∈ env 2 ∧ env 1 ∈ env 2 :=
  (BoundedFormula.realize_toFormula M _ _ members).trans
    (BoundedFormula.truth_refinementActivityFormula env)

theorem realize_refinementCollisionFormula (env : Fin 4 → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets refinementCollisionFormula env ↔ (env 0 = env 1 ↔ env 2 = env 3) :=
  (BoundedFormula.realize_toFormula M _ _ members).trans
    (BoundedFormula.truth_refinementCollisionFormula env)

theorem realize_refinementProfileFormula (env : Fin 3 → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets refinementProfileFormula env ↔ (env 0 ∈ env 2 ↔ env 1 ∈ env 2) :=
  (BoundedFormula.realize_toFormula M _ _ members).trans
    (BoundedFormula.truth_refinementProfileFormula env)

theorem realize_refinementCompatibilityFormula (env : Fin 4 → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets refinementCompatibilityFormula env ↔
      (env 0 ∈ env 1 → ZFSet.pair (env 0) (env 2) ∈ env 3) :=
  (BoundedFormula.realize_toFormula M _ _ members).trans
    (BoundedFormula.truth_refinementCompatibilityFormula env)

end TransitiveGround
end

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem refinementTest_forcing_mono {n : Nat} (formula : SetFormula n)
    (env : Assignment (M.nameDomain s) n) {p q : P}
    (forced : Forces (M.nameDomain s) formula env p) (below : q ≤ p) :
    Forces (M.nameDomain s) formula env q :=
  forces_mono (M.nameDomain s) formula env forced below

theorem refinementActivity_eval (env : Assignment (M.nameDomain s) 3)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    {p : P} (hp : H.mem p)
    (forced : Forces (M.nameDomain s) refinementActivityFormula env p) :
    Name.eval {q | H.mem q} (env 0).val ∈ Name.eval {q | H.mem q} (env 2).val ∧
      Name.eval {q | H.mem q} (env 1).val ∈ Name.eval {q | H.mem q} (env 2).val := by
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive {q | H.mem q}⟩
  exact (evaluated.realize_refinementActivityFormula (evalAssignment {q | H.mem q} env)
    (fun j => ⟨env j, rfl⟩)).1
      (forces_sound (M.nameDomain s) H generic _ env hp forced)

theorem refinementCollision_eval (env : Assignment (M.nameDomain s) 4)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    {p : P} (hp : H.mem p)
    (forced : Forces (M.nameDomain s) refinementCollisionFormula env p) :
    (Name.eval {q | H.mem q} (env 0).val = Name.eval {q | H.mem q} (env 1).val ↔
      Name.eval {q | H.mem q} (env 2).val = Name.eval {q | H.mem q} (env 3).val) := by
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive {q | H.mem q}⟩
  exact (evaluated.realize_refinementCollisionFormula (evalAssignment {q | H.mem q} env)
    (fun j => ⟨env j, rfl⟩)).1
      (forces_sound (M.nameDomain s) H generic _ env hp forced)

theorem refinementProfile_eval (env : Assignment (M.nameDomain s) 3)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    {p : P} (hp : H.mem p)
    (forced : Forces (M.nameDomain s) refinementProfileFormula env p) :
    (Name.eval {q | H.mem q} (env 0).val ∈ Name.eval {q | H.mem q} (env 2).val ↔
      Name.eval {q | H.mem q} (env 1).val ∈ Name.eval {q | H.mem q} (env 2).val) := by
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive {q | H.mem q}⟩
  exact (evaluated.realize_refinementProfileFormula (evalAssignment {q | H.mem q} env)
    (fun j => ⟨env j, rfl⟩)).1
      (forces_sound (M.nameDomain s) H generic _ env hp forced)

theorem refinementCompatibility_eval (env : Assignment (M.nameDomain s) 4)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    {p : P} (hp : H.mem p)
    (forced : Forces (M.nameDomain s) refinementCompatibilityFormula env p) :
    Name.eval {q | H.mem q} (env 0).val ∈ Name.eval {q | H.mem q} (env 1).val →
      ZFSet.pair (Name.eval {q | H.mem q} (env 0).val)
        (Name.eval {q | H.mem q} (env 2).val) ∈ Name.eval {q | H.mem q} (env 3).val := by
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive {q | H.mem q}⟩
  exact (evaluated.realize_refinementCompatibilityFormula (evalAssignment {q | H.mem q} env)
    (fun j => ⟨env j, rfl⟩)).1
      (forces_sound (M.nameDomain s) H generic _ env hp forced)

end TransitiveGround

namespace TransitiveGround
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

def stageOneCollisionTest (Rf Rc u u' w w' : (M.nameDomain s).names) (p : P) : Prop :=
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  Forces (M.nameDomain s) refinementCollisionFormula ![cls Rc u, cls Rc u', cls Rf w, cls Rf w'] p

variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

def stageOneSingleTests (C E : L) (U Rf Rc u w : (M.nameDomain s).names) (p : P) : Prop :=
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let vis := M.stageOneVisibilityName s valid a b d base directed system
  let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
  Forces (M.nameDomain s) refinementActivityFormula ![u, w, U] p ∧
    (∀ v : L, E ≤ v →
      Forces (M.nameDomain s) refinementProfileFormula ![cls Rc u, cls Rf w, vis v] p) ∧
    Forces (M.nameDomain s) refinementCompatibilityFormula ![cls Rf w, vis C, cls Rc u, map] p

def stageOneTests (T2 A : ZFSet.{u}) (p : P) : Prop :=
  ∀ (C E : L) (U Rf Rc : (M.nameDomain s).names),
    let idx := refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    idx ∈ M.niceRefinementIndices a s b d ∅ T T2 valid →
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

end TransitiveGround

namespace TransitiveGround
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

theorem stageOneCollisionTest_mono (Rf Rc u u' w w' : (M.nameDomain s).names)
    {p q : P} (forced : M.stageOneCollisionTest s pairing unions powers separation collection
      carrier order hT valid Rf Rc u u' w w' p) (below : q ≤ p) :
    M.stageOneCollisionTest s pairing unions powers separation collection
      carrier order hT valid Rf Rc u u' w w' q :=
  forces_mono (M.nameDomain s) _ _ forced below

variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

theorem stageOneSingleTests_mono (C E : L) (U Rf Rc u w : (M.nameDomain s).names)
    {p q : P} (forced : M.stageOneSingleTests s pairing unions powers separation collection
      carrier order hT valid a b d base directed system C E U Rf Rc u w p) (below : q ≤ p) :
    M.stageOneSingleTests s pairing unions powers separation collection
      carrier order hT valid a b d base directed system C E U Rf Rc u w q :=
  ⟨forces_mono (M.nameDomain s) _ _ forced.1 below,
    fun v above => forces_mono (M.nameDomain s) _ _ (forced.2.1 v above) below,
    forces_mono (M.nameDomain s) _ _ forced.2.2 below⟩

theorem stageOneTests_mono (T2 A : ZFSet.{u}) {p q : P}
    (tests : M.stageOneTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system T2 A p) (below : q ≤ p) :
    M.stageOneTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system T2 A q := by
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

theorem stageOneTests_subset (T2 : ZFSet.{u}) {A B : ZFSet.{u}} (p : P)
    (tests : M.stageOneTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system T2 A p) (subset : B ⊆ A) :
    M.stageOneTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system T2 B p := by
  intro C E U Rf Rc
  dsimp only
  intro member
  obtain ⟨single, collision⟩ := tests C E U Rf Rc member
  exact ⟨fun u w hu hw entry => single u w hu hw (subset entry),
    fun u u' w w' hu hu' hw hw' entry entry' =>
      collision u u' w w' hu hu' hw hw' (subset entry) (subset entry')⟩

theorem stageOneTests_empty (T2 : ZFSet.{u}) (p : P) :
    M.stageOneTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system T2 ∅ p := by
  intro C E U Rf Rc
  dsimp only
  intro member
  exact ⟨fun _ _ _ _ entry => False.elim (ZFSet.notMem_empty _ entry),
    fun _ _ _ _ _ _ _ _ entry _ => False.elim (ZFSet.notMem_empty _ entry)⟩

end TransitiveGround

open SetRealization SetFormula
universe u

noncomputable def stageOneAssignmentUnion (family : Nat → ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.range family).sUnion

theorem mem_stageOneAssignmentUnion (family : Nat → ZFSet.{u}) (z : ZFSet.{u}) :
    z ∈ stageOneAssignmentUnion family ↔ ∃ n, z ∈ family n := by
  rw [stageOneAssignmentUnion, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨A, hA, member⟩
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.1 hA
    exact ⟨n, member⟩
  · rintro ⟨n, member⟩
    exact ⟨family n, ZFSet.mem_range.2 ⟨n, rfl⟩, member⟩

theorem stageOneAssignmentUnion_contains (family : Nat → ZFSet.{u}) (n : Nat) :
    family n ⊆ stageOneAssignmentUnion family :=
  fun z member => (mem_stageOneAssignmentUnion family z).2 ⟨n, member⟩

theorem stageOneAssignmentUnion_subset {family : Nat → ZFSet.{u}} {J : ZFSet.{u}}
    (subsets : ∀ n, family n ⊆ J) : stageOneAssignmentUnion family ⊆ J := by
  intro z member
  obtain ⟨n, hn⟩ := (mem_stageOneAssignmentUnion family z).1 member
  exact subsets n hn

namespace TransitiveGround
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

theorem stageOneTests_union (T2 : ZFSet.{u}) (family : Nat → ZFSet.{u}) (rows : Nat → P) (p : P)
    (increasing : ∀ n m, n ≤ m → family n ⊆ family m)
    (below : ∀ n, p ≤ rows n)
    (tests : ∀ n, M.stageOneTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system T2 (family n) (rows n)) :
    M.stageOneTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system T2 (stageOneAssignmentUnion family) p := by
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

end TransitiveGround

theorem stageOneAssignmentUnion_raw_eq {B : ZFSet.{u}} (seq : Nat → SetMembers B) :
    stageOneAssignmentUnion (fun n => SetMembers.raw (seq n)) = groundSequenceUnion seq := by
  apply ZFSet.ext
  intro z
  rw [mem_stageOneAssignmentUnion, mem_groundSequenceUnion]

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem groundSmallSubset_union_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {J : ZFSet.{u}} (hJ : J ∈ M.sets)
    (seq : Nat → SetMembers (M.groundSmallSubsets J ZFSet.omega))
    (graph : groundSequenceGraph seq ∈ M.sets) :
    stageOneAssignmentUnion (fun n => SetMembers.raw (seq n)) ∈ M.groundSmallSubsets J ZFSet.omega := by
  have hB := M.groundSmallSubsets_mem powers separation hJ (M.omega_mem separation infinite)
  have subsets (A : ZFSet.{u}) (member : A ∈ M.groundSmallSubsets J ZFSet.omega) : A ⊆ J :=
    ((M.mem_groundSmallSubsets J ZFSet.omega A).1 member).2.1
  have small (A : ZFSet.{u}) (member : A ∈ M.groundSmallSubsets J ZFSet.omega) :
      M.groundEmbeddable A ZFSet.omega :=
    ((M.mem_groundSmallSubsets J ZFSet.omega A).1 member).2.2
  obtain ⟨ground, countable⟩ := M.countable_union_of_sequence_graph pairing unions powers separation
    infinite choice hB hJ graph
    (natPresentation.graph_isFunc (SetMembers.presentation (M.groundSmallSubsets J ZFSet.omega))
      (fun n => seq n.down)) subsets small
  have equal := stageOneAssignmentUnion_raw_eq seq
  apply (M.mem_groundSmallSubsets J ZFSet.omega _).2
  refine ⟨equal.symm ▸ ground, ?_, equal.symm ▸ countable⟩
  exact stageOneAssignmentUnion_subset (fun n => subsets _ (SetMembers.raw_mem (seq n)))

end TransitiveGround

end PartitionPilot.Forcing

end OAI
