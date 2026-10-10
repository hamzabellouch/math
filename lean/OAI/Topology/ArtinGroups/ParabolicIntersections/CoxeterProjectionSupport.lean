import OAI.Topology.ArtinGroups.ParabolicIntersections.ParabolicCosetProjection

namespace OAI

/-! Parabolic projection preserves any standard subgroup containing its input. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

private lemma component_one (X : Set S) : parabolicComponent cs X 1=1 := by
  have hr : parabolicRep cs X 1=1 := parabolicRep_of_minimum cs X 1 (by
    intro a _
    rw [cs.length_one]
    exact Nat.zero_le _)
  simp only [parabolicComponent,hr,inv_one,mul_one]

lemma rep_mem_of_component_mem (X C : Set S) (w : W)
    (hw : w∈parabolic cs C) (hc : parabolicComponent cs X w∈parabolic cs C) :
    parabolicRep cs X w∈parabolic cs C := by
  have he : parabolicRep cs X w=(parabolicComponent cs X w)⁻¹*w := by
    exact (eq_inv_mul_iff_mul_eq).mpr (parabolicComponent_mul_rep cs X w)
  rw [he]
  exact (parabolic cs C).mul_mem ((parabolic cs C).inv_mem hc) hw

lemma component_step_mem (X C : Set S) (w : W) (s : S)
    (hw : w∈parabolic cs C) (hc : parabolicComponent cs X w∈parabolic cs C) (hs : s∈C) :
    parabolicComponent cs X (w*cs.simple s)∈parabolic cs C := by
  have hr := rep_mem_of_component_mem cs X C w hw hc
  have hh : parabolicStepRatio cs X w s∈parabolic cs C := by
    by_cases he : parabolicStepRatio cs X w s=1
    · rw [he]
      exact Subgroup.one_mem _
    · rw [parabolicStepRatio_reflection cs X w s he]
      exact (parabolic cs C).mul_mem
        ((parabolic cs C).mul_mem hr (simple_mem_parabolic cs C hs))
        ((parabolic cs C).inv_mem hr)
  have he : parabolicComponent cs X (w*cs.simple s)=
      parabolicComponent cs X w*parabolicStepRatio cs X w s := by
    unfold parabolicStepRatio
    rw [mul_inv_cancel_left]
  rw [he]
  exact (parabolic cs C).mul_mem hc hh

/-- The parabolic component of an element of `W_C` is again in `W_C`. -/
theorem component_mem_of_mem (X C : Set S) (w : W) (hw : w∈parabolic cs C) :
    parabolicComponent cs X w∈parabolic cs C := by
  obtain ⟨u,hu,rfl⟩ := (mem_parabolic_iff_word cs C w).mp hw
  induction u using List.reverseRecOn with
  | nil =>
    rw [cs.wordProd_nil,component_one]
    exact Subgroup.one_mem _
  | append_singleton u s ih =>
    have hu' : ∀ i∈u, i∈C := fun i hi => hu i (List.mem_append_left _ hi)
    have hs : s∈C := hu s (List.mem_append_right _ (by simp))
    rw [cs.wordProd_append,cs.wordProd_singleton]
    exact component_step_mem cs X C _ s (wordProd_mem_parabolic cs C u hu')
      (ih hu' (wordProd_mem_parabolic cs C u hu')) hs

/-- The canonical minimal representative also stays in `W_C`. -/
theorem rep_mem_of_mem (X C : Set S) (w : W) (hw : w∈parabolic cs C) :
    parabolicRep cs X w∈parabolic cs C :=
  rep_mem_of_component_mem cs X C w hw (component_mem_of_mem cs X C w hw)

/-- A minimal left representative outside `W_C` cannot lie in `W_X W_C`. -/
theorem minimum_not_product (X C : Set S) (w : W) (hmin : IsParabolicMinimum cs X w)
    (hw : w∉parabolic cs C) (a b : W) (ha : a∈parabolic cs X) (hb : b∈parabolic cs C) :
    w≠a*b := by
  intro he
  apply hw
  have hr := rep_mem_of_mem cs X C b hb
  rw [←parabolicRep_left_mul cs X a b ha,←he,parabolicRep_of_minimum cs X w hmin] at hr
  exact hr

end HarmonicArtin.ParabolicIntersections

end OAI
