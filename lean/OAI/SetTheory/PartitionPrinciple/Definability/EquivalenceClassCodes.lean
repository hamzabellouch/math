import OAI.SetTheory.PartitionPrinciple.Models.GroundCountableQuotients

namespace OAI


namespace PartitionPilot.Forcing

universe u

noncomputable def equivalenceClass (A E y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ZFSet.pair x y ∈ E) A

theorem mem_equivalenceClass (A E y x : ZFSet.{u}) :
    x ∈ equivalenceClass A E y ↔ x ∈ A ∧ ZFSet.pair x y ∈ E :=
  ZFSet.mem_sep

theorem equivalenceClass_subset (A E y : ZFSet.{u}) : equivalenceClass A E y ⊆ A :=
  fun _ h => (mem_equivalenceClass A E y _).1 h |>.1

noncomputable def equivalenceClasses (A E : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun C => ∃ y ∈ A, C = equivalenceClass A E y) (ZFSet.powerset A)

theorem mem_equivalenceClasses (A E C : ZFSet.{u}) :
    C ∈ equivalenceClasses A E ↔ ∃ y ∈ A, C = equivalenceClass A E y := by
  rw [equivalenceClasses, ZFSet.mem_sep, ZFSet.mem_powerset]
  exact ⟨And.right, fun ⟨y, hy, equal⟩ =>
    ⟨equal ▸ equivalenceClass_subset A E y, y, hy, equal⟩⟩

theorem equivalenceClass_mem {A E y : ZFSet.{u}} (hy : y ∈ A) :
    equivalenceClass A E y ∈ equivalenceClasses A E :=
  (mem_equivalenceClasses A E _).2 ⟨y, hy, rfl⟩

noncomputable def equivalenceClassifier (A E : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ y ∈ A, z = ZFSet.pair y (equivalenceClass A E y))
    (ZFSet.prod A (equivalenceClasses A E))

theorem mem_equivalenceClassifier (A E z : ZFSet.{u}) :
    z ∈ equivalenceClassifier A E ↔
      ∃ y ∈ A, z = ZFSet.pair y (equivalenceClass A E y) := by
  rw [equivalenceClassifier, ZFSet.mem_sep]
  refine ⟨And.right, ?_⟩
  rintro ⟨y, hy, rfl⟩
  exact ⟨ZFSet.pair_mem_prod.2 ⟨hy, equivalenceClass_mem hy⟩, y, hy, rfl⟩

theorem pair_mem_equivalenceClassifier (A E y C : ZFSet.{u}) :
    ZFSet.pair y C ∈ equivalenceClassifier A E ↔
      y ∈ A ∧ C = equivalenceClass A E y := by
  rw [mem_equivalenceClassifier]
  constructor
  · rintro ⟨x, hx, equal⟩
    obtain ⟨rfl, equal⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx, equal⟩
  · rintro ⟨hy, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem equivalenceClassifier_function (A E : ZFSet.{u}) :
    ZFSet.IsFunc A (equivalenceClasses A E) (equivalenceClassifier A E) := by
  refine ⟨fun _ h => (ZFSet.mem_sep.1 h).1, ?_⟩
  intro y hy
  exact ⟨equivalenceClass A E y,
    (pair_mem_equivalenceClassifier A E y _).2 ⟨hy, rfl⟩,
    fun C hC => ((pair_mem_equivalenceClassifier A E y C).1 hC).2⟩

theorem equivalenceClassifier_onto {A E C : ZFSet.{u}}
    (hC : C ∈ equivalenceClasses A E) :
    ∃ y ∈ A, ZFSet.pair y C ∈ equivalenceClassifier A E := by
  obtain ⟨y, hy, rfl⟩ := (mem_equivalenceClasses A E C).1 hC
  exact ⟨y, hy, (pair_mem_equivalenceClassifier A E y _).2 ⟨hy, rfl⟩⟩

namespace EquivalenceRelationCode

theorem class_self {A E : ZFSet.{u}} (equivalence : EquivalenceRelationCode A E)
    {x : ZFSet.{u}} (hx : x ∈ A) : x ∈ equivalenceClass A E x :=
  (mem_equivalenceClass A E x x).2 ⟨hx, equivalence.refl x hx⟩

theorem class_eq_iff {A E : ZFSet.{u}} (equivalence : EquivalenceRelationCode A E)
    {x y : ZFSet.{u}} (hx : x ∈ A) (_hy : y ∈ A) :
    equivalenceClass A E x = equivalenceClass A E y ↔ ZFSet.pair x y ∈ E := by
  constructor
  · intro equal
    exact ((mem_equivalenceClass A E y x).1 (equal ▸ equivalence.class_self hx)).2
  · intro related
    apply ZFSet.ext
    intro z
    rw [mem_equivalenceClass, mem_equivalenceClass]
    exact and_congr_right (fun _ => ⟨
      fun h => equivalence.trans z x y h related,
      fun h => equivalence.trans z y x h (equivalence.symm x y related)⟩)

theorem classifier_kernel {A E : ZFSet.{u}} (equivalence : EquivalenceRelationCode A E)
    {x y C D : ZFSet.{u}}
    (first : ZFSet.pair x C ∈ equivalenceClassifier A E)
    (second : ZFSet.pair y D ∈ equivalenceClassifier A E) :
    C = D ↔ ZFSet.pair x y ∈ E := by
  obtain ⟨hx, rfl⟩ := (pair_mem_equivalenceClassifier A E x C).1 first
  obtain ⟨hy, rfl⟩ := (pair_mem_equivalenceClassifier A E y D).1 second
  exact equivalence.class_eq_iff hx hy

theorem class_nonempty {A E C : ZFSet.{u}} (equivalence : EquivalenceRelationCode A E)
    (hC : C ∈ equivalenceClasses A E) : ∃ x, x ∈ C := by
  obtain ⟨x, hx, rfl⟩ := (mem_equivalenceClasses A E C).1 hC
  exact ⟨x, equivalence.class_self hx⟩

end EquivalenceRelationCode

end PartitionPilot.Forcing

end OAI
