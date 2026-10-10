import OAI.SetTheory.PartitionPrinciple.Forcing.IndexedTupleNames

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

def partialCollectionFormula {n : Nat} (φ : SetFormula (n + 2)) : SetFormula (n + 2) :=
  imp (ex (binaryApplication φ (fun j => j.succ.succ.succ) 1 0)) φ

def relationImageFormula {n : Nat} (φ : SetFormula (n + 2)) : SetFormula (n + 2) :=
  ex (.conj (.mem 0 2) (binaryApplication φ (fun j => j.succ.succ.succ) 0 1))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_partialCollectionFormula {n : Nat} (φ : SetFormula (n + 2))
    (params : Fin n → ZFSet.{u}) (x y : ZFSet.{u}) :
    Realize M.sets (partialCollectionFormula φ) (extend x (extend y params)) ↔
      ((∃ z ∈ M.sets, Realize M.sets φ (extend x (extend z params))) →
        Realize M.sets φ (extend x (extend y params))) := by
  simp only [partialCollectionFormula, realize_imp, realize_ex, realize_binaryApplication]
  rfl

theorem realize_relationImageFormula {n : Nat} (φ : SetFormula (n + 2))
    (params : Fin n → ZFSet.{u}) (A y : ZFSet.{u}) (hA : A ∈ M.sets) :
    Realize M.sets (relationImageFormula φ) (extend y (extend A params)) ↔
      ∃ x ∈ A, Realize M.sets φ (extend x (extend y params)) := by
  rw [relationImageFormula, realize_ex]
  constructor
  · rintro ⟨x, _, member, rel⟩
    exact ⟨x, member, (realize_binaryApplication M.sets φ _ _ _ _).1 rel⟩
  · rintro ⟨x, hx, rel⟩
    exact ⟨x, M.transitive hA hx, hx, (realize_binaryApplication M.sets φ _ _ _ _).2 rel⟩

theorem partialCollection_witness (collection : CollectionSchema M.sets)
    {n : Nat} (φ : SetFormula (n + 2)) (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {A : ZFSet.{u}} (hA : A ∈ M.sets) :
    ∃ W ∈ M.sets, ∀ x ∈ A,
      (∃ y ∈ M.sets, Realize M.sets φ (extend x (extend y params))) →
      ∃ y ∈ W, Realize M.sets φ (extend x (extend y params)) := by
  classical
  have witnesses : ∀ x ∈ A, ∃ y ∈ M.sets,
      Realize M.sets (partialCollectionFormula φ) (extend x (extend y params)) := by
    intro x _
    by_cases possible : ∃ y ∈ M.sets, Realize M.sets φ (extend x (extend y params))
    · obtain ⟨y, hy, rel⟩ := possible
      exact ⟨y, hy, (M.realize_partialCollectionFormula φ params x y).2 (fun _ => rel)⟩
    · exact ⟨A, hA, (M.realize_partialCollectionFormula φ params x A).2 (fun h => False.elim (possible h))⟩
  obtain ⟨W, hW, bounds⟩ := M.collection_witness collection (partialCollectionFormula φ) params members hA witnesses
  refine ⟨W, hW, ?_⟩
  intro x hx possible
  obtain ⟨y, hy, rel⟩ := bounds x hx
  exact ⟨y, hy, (M.realize_partialCollectionFormula φ params x y).1 rel possible⟩

theorem definable_image_mem (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {n : Nat} (φ : SetFormula (n + 2)) (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {A C : ZFSet.{u}} (hA : A ∈ M.sets)
    (ground : ∀ y ∈ C, y ∈ M.sets)
    (correct : ∀ y ∈ M.sets, y ∈ C ↔ ∃ x ∈ A, Realize M.sets φ (extend x (extend y params)))
    (functional : ∀ x ∈ A, ∀ y ∈ M.sets, ∀ z ∈ M.sets,
      Realize M.sets φ (extend x (extend y params)) →
      Realize M.sets φ (extend x (extend z params)) → y = z) : C ∈ M.sets := by
  obtain ⟨W, hW, bounds⟩ := M.partialCollection_witness collection φ params members hA
  have bound : C ⊆ W := by
    intro y hy
    have hyM := ground y hy
    obtain ⟨x, hx, rel⟩ := (correct y hyM).1 hy
    obtain ⟨z, hz, relz⟩ := bounds x hx ⟨y, hyM, rel⟩
    exact (functional x hx y hyM z (M.transitive hW hz) rel relz).symm ▸ hz
  have selected := M.separation_mem separation (relationImageFormula φ) (extend A params)
    (Fin.cases hA members) hW
  have eq : ZFSet.sep (fun y => Realize M.sets (relationImageFormula φ) (extend y (extend A params))) W = C := by
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_sep, M.realize_relationImageFormula φ params A y hA]
    constructor
    · rintro ⟨hy, rel⟩
      exact (correct y (M.transitive hW hy)).2 rel
    · intro hy
      exact ⟨bound hy, (correct y (ground y hy)).1 hy⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.SetFormula

def separationCodeFormula {n : Nat} (φ : SetFormula (n + 1)) : SetFormula (n + 2) :=
  exactSetFormula 0 (.conj (.mem 0 2)
    (reindex (extend 0 (fun j : Fin n => j.succ.succ.succ)) φ))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

def definable_separation (separation : SeparationSchema M.sets)
    {n : Nat} (φ : SetFormula (n + 1)) :
    GroundDefinableFunction M (fun env : Fin (n + 1) → ZFSet.{u} =>
      ZFSet.sep (fun z => Realize M.sets φ (extend z (fun j => env j.succ))) (env 0)) where
  formula := separationCodeFormula φ
  closed := by
    intro env members
    exact M.separation_mem separation φ (fun j => env j.succ) (fun j => members j.succ) (members 0)
  correct := by
    intro env members z hz
    apply M.realize_exactSetFormula 0 _ (extend z env) hz
    · intro w hw
      exact M.transitive (members 0) (ZFSet.mem_sep.1 hw).1
    · intro w _
      rw [ZFSet.mem_sep]
      change (w ∈ env 0 ∧ Realize M.sets (reindex _ φ) _) ↔ _
      rw [realize_reindex, map_extend]
      rfl

end PartitionPilot.Forcing.TransitiveGround

end OAI
