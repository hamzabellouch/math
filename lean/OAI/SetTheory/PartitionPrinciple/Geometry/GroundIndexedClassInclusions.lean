import OAI.SetTheory.PartitionPrinciple.Definability.EquivalenceClassCodes

namespace OAI


namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def equivalenceClassFormula {n} (C A E y : Fin n) : BoundedFormula n :=
  .conj (.allMem C (.mem 0 A.succ))
    (.allMem A (.conj
      (imp (.mem 0 C.succ) (pairMembershipFormula 0 y.succ E.succ))
      (imp (pairMembershipFormula 0 y.succ E.succ) (.mem 0 C.succ))))

theorem truth_equivalenceClassFormula {n} (C A E y : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (equivalenceClassFormula C A E y) env ↔
      env C = equivalenceClass (env A) (env E) (env y) := by
  simp only [equivalenceClassFormula, Truth, truth_imp, truth_pairMembershipFormula]
  change ((∀ x ∈ env C, x ∈ env A) ∧ ∀ x ∈ env A,
    (x ∈ env C → ZFSet.pair x (env y) ∈ env E) ∧
    (ZFSet.pair x (env y) ∈ env E → x ∈ env C)) ↔ _
  constructor
  · rintro ⟨subset, complete⟩
    apply ZFSet.ext
    intro x
    rw [mem_equivalenceClass]
    exact ⟨fun hx => ⟨subset x hx, (complete x (subset x hx)).1 hx⟩,
      fun hx => (complete x hx.1).2 hx.2⟩
  · intro equal
    rw [equal]
    exact ⟨fun _ hx => (mem_equivalenceClass _ _ _ _).1 hx |>.1,
      fun x hx => ⟨fun h => (mem_equivalenceClass _ _ _ x).1 h |>.2,
        fun h => (mem_equivalenceClass _ _ _ x).2 ⟨hx, h⟩⟩⟩

def equivalenceClassesFormula {n} (C A E : Fin n) : BoundedFormula n :=
  exMem A (equivalenceClassFormula C.succ A.succ E.succ 0)

theorem truth_equivalenceClassesFormula {n} (C A E : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (equivalenceClassesFormula C A E) env ↔
      env C ∈ equivalenceClasses (env A) (env E) := by
  simp only [equivalenceClassesFormula, truth_exMem, truth_equivalenceClassFormula,
    mem_equivalenceClasses]
  rfl

def equivalenceClassifierEntryFormula {n} (z A E Q : Fin n) : BoundedFormula n :=
  exMem A (exMem Q.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (equivalenceClassFormula 0 A.succ.succ E.succ.succ 1)))

theorem truth_equivalenceClassifierEntryFormula {n} (z A E Q : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (equivalenceClassifierEntryFormula z A E Q) env ↔
      ∃ y ∈ env A, ∃ C ∈ env Q,
        env z = ZFSet.pair y C ∧ C = equivalenceClass (env A) (env E) y := by
  simp only [equivalenceClassifierEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_equivalenceClassFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem equivalenceClass_mem (separation : SeparationSchema M.sets)
    {A E y : ZFSet.{u}} (hA : A ∈ M.sets) (hE : E ∈ M.sets) (hy : y ∈ M.sets) :
    equivalenceClass A E y ∈ M.sets := by
  let params := extend y (extend E Fin.elim0)
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.pairMembershipFormula 0 1 2) params
    (Fin.cases hy (Fin.cases hE (fun i => Fin.elim0 i))) hA
  have equal : ZFSet.sep (fun x => BoundedFormula.Truth
      (BoundedFormula.pairMembershipFormula 0 1 2) (extend x params)) A =
      equivalenceClass A E y := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_equivalenceClass]
    exact and_congr Iff.rfl (BoundedFormula.truth_pairMembershipFormula 0 1 2 _)
  exact equal ▸ selected

theorem equivalenceClasses_eq_sep_groundPower (separation : SeparationSchema M.sets)
    {A E : ZFSet.{u}} (hA : A ∈ M.sets) (hE : E ∈ M.sets) :
    equivalenceClasses A E = ZFSet.sep
      (fun C => ∃ y ∈ A, C = equivalenceClass A E y) (M.groundPower A) := by
  apply ZFSet.ext
  intro C
  rw [mem_equivalenceClasses, ZFSet.mem_sep, M.mem_groundPower]
  refine ⟨?_, And.right⟩
  rintro ⟨y, hy, rfl⟩
  exact ⟨⟨M.equivalenceClass_mem separation hA hE (M.transitive hA hy),
    equivalenceClass_subset A E y⟩, y, hy, rfl⟩

theorem equivalenceClasses_mem (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets)
    {A E : ZFSet.{u}} (hA : A ∈ M.sets) (hE : E ∈ M.sets) :
    equivalenceClasses A E ∈ M.sets := by
  let params := extend A (extend E Fin.elim0)
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.equivalenceClassesFormula 0 1 2) params
    (Fin.cases hA (Fin.cases hE (fun i => Fin.elim0 i))) (M.groundPower_mem powers hA)
  have equal : ZFSet.sep (fun C => BoundedFormula.Truth
      (BoundedFormula.equivalenceClassesFormula 0 1 2) (extend C params))
      (M.groundPower A) = equivalenceClasses A E := by
    rw [M.equivalenceClasses_eq_sep_groundPower separation hA hE]
    apply ZFSet.ext
    intro C
    rw [ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      ((BoundedFormula.truth_equivalenceClassesFormula 0 1 2 _).trans
        (mem_equivalenceClasses A E C))
  exact equal ▸ selected

theorem equivalenceClassifier_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A E : ZFSet.{u}} (hA : A ∈ M.sets) (hE : E ∈ M.sets) :
    equivalenceClassifier A E ∈ M.sets := by
  have hQ := M.equivalenceClasses_mem powers separation hA hE
  let params := extend A (extend E (extend (equivalenceClasses A E) Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.equivalenceClassifierEntryFormula 0 1 2 3) params
    (Fin.cases hA (Fin.cases hE (Fin.cases hQ (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hA hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.equivalenceClassifierEntryFormula 0 1 2 3) (extend z params))
      (ZFSet.prod A (equivalenceClasses A E)) = equivalenceClassifier A E := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_equivalenceClassifierEntryFormula,
      mem_equivalenceClassifier]
    constructor
    · rintro ⟨_, y, hy, C, _, equal, rfl⟩
      exact ⟨y, hy, equal⟩
    · rintro ⟨y, hy, rfl⟩
      have hyQ := Forcing.equivalenceClass_mem (E := E) hy
      exact ⟨ZFSet.pair_mem_prod.2 ⟨hy, hyQ⟩, y, hy,
        equivalenceClass A E y, hyQ, rfl, rfl⟩
  exact equal ▸ selected

theorem equivalenceClasses_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A E : ZFSet.{u}} (hA : A ∈ M.sets) (hE : E ∈ M.sets)
    (equivalence : EquivalenceRelationCode A E) :
    equivalenceClasses A E ∈ M.sets ∧ equivalenceClassifier A E ∈ M.sets ∧
      ZFSet.IsFunc A (equivalenceClasses A E) (equivalenceClassifier A E) ∧
      (∀ C ∈ equivalenceClasses A E, ∃ y ∈ A,
        ZFSet.pair y C ∈ equivalenceClassifier A E) ∧
      (∀ x y C D, ZFSet.pair x C ∈ equivalenceClassifier A E →
        ZFSet.pair y D ∈ equivalenceClassifier A E → (C = D ↔ ZFSet.pair x y ∈ E)) :=
  ⟨M.equivalenceClasses_mem powers separation hA hE,
    M.equivalenceClassifier_mem pairing unions powers separation hA hE,
    equivalenceClassifier_function A E, fun _ hC => equivalenceClassifier_onto hC,
    fun _ _ _ _ first second => equivalence.classifier_kernel first second⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def indexedClassInclusion (U L E i : ZFSet.{u}) : ZFSet.{u} :=
  indexedRelationSection U (equivalenceClasses L E) (equivalenceClassifier L E) i

theorem pair_mem_indexedClassInclusion (U L E i x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ indexedClassInclusion U L E i ↔
      x ∈ U ∧ ZFSet.pair i x ∈ L ∧ y = equivalenceClass L E (ZFSet.pair i x) := by
  rw [indexedClassInclusion, pair_mem_indexedRelationSection, pair_mem_equivalenceClassifier]
  constructor
  · rintro ⟨hu, _, label, equal⟩
    exact ⟨hu, label, equal⟩
  · rintro ⟨hu, label, rfl⟩
    exact ⟨hu, equivalenceClass_mem label, label, rfl⟩

theorem pair_mem_indexedClassInclusion_of_entry {T U A E i X x y : ZFSet.{u}}
    (family : FunctionGraphOn T A) (entry : ZFSet.pair i X ∈ A) (bound : X ⊆ U) :
    ZFSet.pair x y ∈ indexedClassInclusion U (indexedCarrierLabels T U A) E i ↔
      x ∈ X ∧ y = equivalenceClass (indexedCarrierLabels T U A) E (ZFSet.pair i x) := by
  rw [pair_mem_indexedClassInclusion, pair_mem_indexedCarrierLabels_of_entry family entry bound]
  exact ⟨fun h => h.2, fun h => ⟨bound h.1, h⟩⟩

theorem indexedClassInclusion_function {T U A E i X : ZFSet.{u}}
    (family : FunctionGraphOn T A) (entry : ZFSet.pair i X ∈ A) (bound : X ⊆ U) :
    ZFSet.IsFunc X (equivalenceClasses (indexedCarrierLabels T U A) E)
      (indexedClassInclusion U (indexedCarrierLabels T U A) E i) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨x, _, y, hy, rfl, _⟩ := (mem_indexedRelationSection _ _ _ _ z).1 hz
    exact ZFSet.pair_mem_prod.2
      ⟨((pair_mem_indexedClassInclusion_of_entry family entry bound).1 hz).1, hy⟩
  · intro x hx
    exact ⟨equivalenceClass (indexedCarrierLabels T U A) E (ZFSet.pair i x),
      (pair_mem_indexedClassInclusion_of_entry family entry bound).2 ⟨hx, rfl⟩,
      fun y hy => ((pair_mem_indexedClassInclusion_of_entry family entry bound).1 hy).2⟩

theorem indexedClassInclusion_kernel {U L E i j x y p q : ZFSet.{u}}
    (equivalence : EquivalenceRelationCode L E)
    (first : ZFSet.pair x p ∈ indexedClassInclusion U L E i)
    (second : ZFSet.pair y q ∈ indexedClassInclusion U L E j) :
    p = q ↔ ZFSet.pair (ZFSet.pair i x) (ZFSet.pair j y) ∈ E := by
  obtain ⟨_, hx, rfl⟩ := (pair_mem_indexedClassInclusion U L E i x p).1 first
  obtain ⟨_, hy, rfl⟩ := (pair_mem_indexedClassInclusion U L E j y q).1 second
  exact equivalence.class_eq_iff hx hy

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem indexedClassInclusion_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {U L E i : ZFSet.{u}} (hU : U ∈ M.sets) (hL : L ∈ M.sets)
    (hE : E ∈ M.sets) (hi : i ∈ M.sets) : indexedClassInclusion U L E i ∈ M.sets :=
  M.indexedRelationSection_mem pairing unions powers separation hU
    (M.equivalenceClasses_mem powers separation hL hE)
    (M.equivalenceClassifier_mem pairing unions powers separation hL hE) hi

noncomputable def indexedClassInclusions (T U L E : ZFSet.{u}) : ZFSet.{u} :=
  M.indexedRelationSections T U (equivalenceClasses L E) (equivalenceClassifier L E)

theorem pair_mem_indexedClassInclusions (T U L E i f : ZFSet.{u}) :
    ZFSet.pair i f ∈ M.indexedClassInclusions T U L E ↔
      i ∈ T ∧ f ∈ M.groundRelations U (equivalenceClasses L E) ∧
        f = indexedClassInclusion U L E i :=
  M.pair_mem_indexedRelationSections T U (equivalenceClasses L E) (equivalenceClassifier L E) i f

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {T U L E : ZFSet.{u}} (hT : T ∈ M.sets) (hU : U ∈ M.sets)
variable (hL : L ∈ M.sets) (hE : E ∈ M.sets)
include pairing unions powers separation hT hU hL hE

theorem indexedClassInclusions_mem : M.indexedClassInclusions T U L E ∈ M.sets :=
  M.indexedRelationSections_mem pairing unions powers separation hT hU
    (M.equivalenceClasses_mem powers separation hL hE)
    (M.equivalenceClassifier_mem pairing unions powers separation hL hE)

theorem indexedClassInclusions_function :
    ZFSet.IsFunc T (M.groundRelations U (equivalenceClasses L E))
      (M.indexedClassInclusions T U L E) :=
  M.indexedRelationSections_function pairing unions powers separation hT hU
    (M.equivalenceClasses_mem powers separation hL hE)
    (M.equivalenceClassifier_mem pairing unions powers separation hL hE)

theorem indexedClassInclusions_entries (i f : ZFSet.{u}) :
    ZFSet.pair i f ∈ M.indexedClassInclusions T U L E ↔
      i ∈ T ∧ f = indexedClassInclusion U L E i :=
  (M.indexedRelationSections_spec pairing unions powers separation hT hU
    (M.equivalenceClasses_mem powers separation hL hE)
    (M.equivalenceClassifier_mem pairing unions powers separation hL hE)).2.2 i f

end TransitiveGround

end PartitionPilot.Forcing

end OAI
