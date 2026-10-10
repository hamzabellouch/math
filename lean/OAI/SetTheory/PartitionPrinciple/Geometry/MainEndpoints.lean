import OAI.SetTheory.PartitionPrinciple.Transfinite.LimitProfilePersistence

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.MainStage.Diagram

universe u
variable {I : Type u} [LinearOrder I]

theorem ext (d e : Diagram I) (stages : d.stage = e.stage)
    (transitions : HEq (@d.transition) (@e.transition)) : d = e := by
  cases d
  cases e
  cases stages
  cases eq_of_heq transitions
  rfl

theorem reindex_comp (d : Diagram I) {J K : Type u} [LinearOrder J] [LinearOrder K]
    (f : J → I) (hf : Monotone f) (g : K → J) (hg : Monotone g) :
    (d.reindex f hf).reindex g hg = d.reindex (fun i => f (g i)) (hf.comp hg) := rfl

theorem reindex_congr (d : Diagram I) {J : Type u} [LinearOrder J]
    (f g : J → I) (hf : Monotone f) (hg : Monotone g) (eq : f = g) :
    d.reindex f hf = d.reindex g hg := by cases eq; rfl

namespace Cone
variable {d : Diagram I} (c : d.Cone)

def augmentedStage : WithTop I → MainStage.{u}
  | none => c.apex
  | some i => d.stage i

def augmentedTransition {i j : WithTop I} (h : i ≤ j) :
    Transition (c.augmentedStage i) (c.augmentedStage j) := by
  cases i with
  | top =>
    cases j with
    | top => exact Transition.identity c.apex
    | coe j => exact False.elim (WithTop.not_top_le_coe j h)
  | coe i =>
    cases j with
    | top => exact c.leg i
    | coe j => exact d.transition (WithTop.coe_le_coe.mp h)

theorem augmentedTransition_self (i : WithTop I) :
    c.augmentedTransition (le_refl i) = Transition.identity (c.augmentedStage i) := by
  cases i with
  | top => rfl
  | coe i => exact d.self i

theorem augmentedTransition_comp {i j k : WithTop I} (hij : i ≤ j) (hjk : j ≤ k) :
    c.augmentedTransition (le_trans hij hjk) =
      (c.augmentedTransition hij).comp (c.augmentedTransition hjk) := by
  cases i with
  | top =>
    cases j with
    | coe j => exact False.elim (WithTop.not_top_le_coe j hij)
    | top =>
      cases k with
      | coe k => exact False.elim (WithTop.not_top_le_coe k hjk)
      | top => exact (Transition.identity_comp _).symm
  | coe i =>
    cases j with
    | top =>
      cases k with
      | coe k => exact False.elim (WithTop.not_top_le_coe k hjk)
      | top => exact (Transition.comp_identity _).symm
    | coe j =>
      cases k with
      | top => exact (c.coherent (WithTop.coe_le_coe.mp hij)).symm
      | coe k => exact d.comp (WithTop.coe_le_coe.mp hij) (WithTop.coe_le_coe.mp hjk)

def augmented : Diagram (WithTop I) where
  stage := c.augmentedStage
  transition := c.augmentedTransition
  self := c.augmentedTransition_self
  comp := c.augmentedTransition_comp

theorem augmented_restrict :
    c.augmented.reindex (fun i : I => (i : WithTop I)) WithTop.coe_mono = d := rfl

variable {a : I}

noncomputable def endIndex (i : Set.Iic a) : WithTop (Set.Iio a) :=
  if h : i.val < a then some ⟨i.val, h⟩ else none

theorem endIndex_old (i : Set.Iio a) :
    endIndex (⟨i.val, i.property.le⟩ : Set.Iic a) = some i := by
  exact dite_eq_left i.property

theorem endIndex_top : endIndex (⟨a, le_refl a⟩ : Set.Iic a) = none :=
  dite_eq_right (lt_irrefl a)

theorem endIndex_mono : Monotone (endIndex (a := a)) := by
  classical
  intro i j h
  by_cases hj : j.val < a
  · have hi : i.val < a := lt_of_le_of_lt h hj
    erw [endIndex, dite_eq_left hi, endIndex, dite_eq_left hj]
    exact WithTop.coe_le_coe.mpr h
  · have eq : endIndex j = none := dite_eq_right hj
    rw [eq]
    exact le_top

noncomputable def append {d : Diagram (Set.Iio a)} (c : d.Cone) : Diagram (Set.Iic a) :=
  c.augmented.reindex endIndex endIndex_mono

theorem append_stage_old {d : Diagram (Set.Iio a)} (c : d.Cone) (i : Set.Iio a) :
    c.append.stage ⟨i.val, i.property.le⟩ = d.stage i := by
  change c.augmentedStage (endIndex ⟨i.val, i.property.le⟩) = _
  rw [endIndex_old]
  rfl

theorem append_stage_top {d : Diagram (Set.Iio a)} (c : d.Cone) :
    c.append.stage ⟨a, le_refl a⟩ = c.apex := by
  change c.augmentedStage (endIndex ⟨a, le_refl a⟩) = _
  rw [endIndex_top]
  rfl

theorem append_restrict {d : Diagram (Set.Iio a)} (c : d.Cone) :
    c.append.reindex (fun i : Set.Iio a => (⟨i.val, i.property.le⟩ : Set.Iic a))
      (fun _ _ h => h) = d := by
  unfold append
  erw [reindex_comp]
  have eq : (fun i : Set.Iio a => endIndex (⟨i.val, i.property.le⟩ : Set.Iic a)) =
      (fun i : Set.Iio a => (i : WithTop (Set.Iio a))) := funext endIndex_old
  exact (reindex_congr c.augmented _ _ _ _ eq).trans c.augmented_restrict

end Cone

end PartitionPilot.Compression.RecursiveMaps.MainStage.Diagram

end

end OAI
