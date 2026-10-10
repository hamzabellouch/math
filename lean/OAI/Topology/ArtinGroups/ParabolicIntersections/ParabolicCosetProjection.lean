import OAI.Topology.ArtinGroups.ParabolicIntersections.ParabolicMinimumStep

namespace OAI

/-! Canonical minimal coset representatives and their parabolic components. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
    (J : Set S)

private theorem exists_minimum_rep (w : W) :
    ∃ v, IsParabolicMinimum cs J v ∧ ∃ a ∈ parabolic cs J, w=a*v := by
  obtain ⟨a,v,ha,hv,hw,_⟩ := exists_parabolic_decomposition cs J w
  exact ⟨v,hv,a,ha,hw⟩

noncomputable def parabolicRep (w : W) : W :=
  Classical.choose (exists_minimum_rep cs J w)

lemma parabolicRep_min (w : W) : IsParabolicMinimum cs J (parabolicRep cs J w) :=
  (Classical.choose_spec (exists_minimum_rep cs J w)).1

noncomputable def parabolicComponent (w : W) : W := w*(parabolicRep cs J w)⁻¹

lemma parabolicComponent_mul_rep (w : W) :
    parabolicComponent cs J w*parabolicRep cs J w=w := by
  simp only [parabolicComponent,inv_mul_cancel_right]

lemma parabolicComponent_mem (w : W) : parabolicComponent cs J w ∈ parabolic cs J := by
  obtain ⟨a,ha,hw⟩ := (Classical.choose_spec (exists_minimum_rep cs J w)).2
  have he : w*(parabolicRep cs J w)⁻¹=a :=
    (congrArg (fun x => x*(parabolicRep cs J w)⁻¹) hw).trans (mul_inv_cancel_right _ _)
  change w*(parabolicRep cs J w)⁻¹ ∈ parabolic cs J
  exact he.symm ▸ ha

lemma parabolicRep_eq_of_decomposition (w a v : W) (ha : a ∈ parabolic cs J)
    (hv : IsParabolicMinimum cs J v) (hw : w=a*v) : parabolicRep cs J w=v := by
  apply parabolic_minimum_unique cs J hv (parabolicRep_min cs J w)
  refine ⟨(parabolicComponent cs J w)⁻¹*a,
    (parabolic cs J).mul_mem ((parabolic cs J).inv_mem (parabolicComponent_mem cs J w)) ha,?_⟩
  have he := parabolicComponent_mul_rep cs J w
  calc parabolicRep cs J w = (parabolicComponent cs J w)⁻¹*w :=
         (eq_inv_mul_iff_mul_eq).mpr he
       _ = (parabolicComponent cs J w)⁻¹*(a*v) := congrArg _ hw
       _ = _ := by group

lemma parabolicRep_of_minimum (v : W) (hv : IsParabolicMinimum cs J v) :
    parabolicRep cs J v=v :=
  parabolicRep_eq_of_decomposition cs J v 1 v (parabolic cs J).one_mem hv (one_mul v).symm

lemma parabolicRep_left_mul (a w : W) (ha : a ∈ parabolic cs J) :
    parabolicRep cs J (a*w)=parabolicRep cs J w := by
  apply parabolicRep_eq_of_decomposition cs J (a*w) (a*parabolicComponent cs J w)
    (parabolicRep cs J w) ((parabolic cs J).mul_mem ha (parabolicComponent_mem cs J w))
    (parabolicRep_min cs J w)
  rw [mul_assoc,parabolicComponent_mul_rep]

lemma parabolicComponent_left_mul (a w : W) (ha : a ∈ parabolic cs J) :
    parabolicComponent cs J (a*w)=a*parabolicComponent cs J w := by
  simp only [parabolicComponent,parabolicRep_left_mul cs J a w ha,mul_assoc]

noncomputable def parabolicStepRatio (w : W) (s : S) : W :=
  (parabolicComponent cs J w)⁻¹*parabolicComponent cs J (w*cs.simple s)

/-- The component changes by either no letter or a simple letter of `J`. -/
theorem parabolicStepRatio_cases (w : W) (s : S) :
    parabolicStepRatio cs J w s=1 ∨
      ∃ t : J, parabolicStepRatio cs J w s=cs.simple t := by
  rcases parabolic_minimum_step cs J (parabolicRep cs J w) (parabolicRep_min cs J w) s
    with hmin | ⟨t,ht,he⟩
  · left
    have hr : parabolicRep cs J (w*cs.simple s)=parabolicRep cs J w*cs.simple s := by
      apply parabolicRep_eq_of_decomposition cs J _ (parabolicComponent cs J w) _
        (parabolicComponent_mem cs J w) hmin
      rw [←mul_assoc,parabolicComponent_mul_rep]
    unfold parabolicStepRatio parabolicComponent
    rw [hr,mul_inv_rev]
    group
  · right
    have hr : parabolicRep cs J (w*cs.simple s)=parabolicRep cs J w := by
      apply parabolicRep_eq_of_decomposition cs J _
        (parabolicComponent cs J w*cs.simple t) _
        ((parabolic cs J).mul_mem (parabolicComponent_mem cs J w) (simple_mem_parabolic cs J ht))
        (parabolicRep_min cs J w)
      rw [mul_assoc,←he,←mul_assoc,parabolicComponent_mul_rep]
    refine ⟨⟨t,ht⟩,?_⟩
    unfold parabolicStepRatio parabolicComponent
    rw [hr]
    conv_rhs => rw [show cs.simple t=(parabolicRep cs J w*cs.simple s)*
        (parabolicRep cs J w)⁻¹ by rw [he,mul_inv_cancel_right]]
    group

lemma parabolicStepRatio_one_of_minimum (w : W) (s : S)
    (hmin : IsParabolicMinimum cs J (parabolicRep cs J w*cs.simple s)) :
    parabolicStepRatio cs J w s=1 := by
  have hr : parabolicRep cs J (w*cs.simple s)=parabolicRep cs J w*cs.simple s := by
    apply parabolicRep_eq_of_decomposition cs J _ (parabolicComponent cs J w) _
      (parabolicComponent_mem cs J w) hmin
    rw [←mul_assoc,parabolicComponent_mul_rep]
  unfold parabolicStepRatio parabolicComponent
  rw [hr,mul_inv_rev]
  group

lemma parabolicStepRatio_reflection (w : W) (s : S)
    (hne : parabolicStepRatio cs J w s ≠ 1) :
    parabolicStepRatio cs J w s =
      parabolicRep cs J w*cs.simple s*(parabolicRep cs J w)⁻¹ := by
  rcases parabolic_minimum_step cs J (parabolicRep cs J w) (parabolicRep_min cs J w) s
    with hmin | ⟨t,ht,he⟩
  · exact (hne (parabolicStepRatio_one_of_minimum cs J w s hmin)).elim
  have hr : parabolicRep cs J (w*cs.simple s)=parabolicRep cs J w := by
    apply parabolicRep_eq_of_decomposition cs J _ (parabolicComponent cs J w*cs.simple t) _
      ((parabolic cs J).mul_mem (parabolicComponent_mem cs J w) (simple_mem_parabolic cs J ht))
      (parabolicRep_min cs J w)
    rw [mul_assoc,←he,←mul_assoc,parabolicComponent_mul_rep]
  unfold parabolicStepRatio parabolicComponent
  rw [hr]
  group

lemma parabolicStepRatio_reverse (w : W) (s : S) :
    parabolicStepRatio cs J (w*cs.simple s) s=parabolicStepRatio cs J w s := by
  have he : parabolicStepRatio cs J (w*cs.simple s) s=(parabolicStepRatio cs J w s)⁻¹ := by
    simp only [parabolicStepRatio,cs.simple_mul_simple_cancel_right,mul_inv_rev,inv_inv]
  rw [he]
  rcases parabolicStepRatio_cases cs J w s with h | ⟨t,h⟩
  · rw [h,inv_one]
  · rw [h,cs.inv_simple]

end HarmonicArtin.ParabolicIntersections

end OAI
