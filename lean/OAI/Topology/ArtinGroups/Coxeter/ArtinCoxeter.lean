import Mathlib
import OAI.Topology.ArtinGroups.Realizations.FullSphericalCell

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} (M : CoxeterMatrix S)

lemma artinCoxeter_relators : ∀ r ∈ braidRelators M,
    FreeGroup.lift M.toCoxeterSystem.simple r = 1 := by
  rintro r ⟨⟨s,t⟩,rfl⟩
  rw [map_mul,map_inv,alternating_lift_prod,alternating_lift_prod]
  exact mul_inv_eq_one.mpr (altList_braid M.toCoxeterSystem s t)

noncomputable def artinCoxeter : Artin M →* M.Group := PresentedGroup.toGroup (artinCoxeter_relators M)

@[simp] lemma artinCoxeter_generator (s : S) :
    artinCoxeter M (generator M s) = M.toCoxeterSystem.simple s := PresentedGroup.toGroup.of _

lemma artinCoxeter_word (w : List S) : artinCoxeter M (wordArtin M w) = wordCoxeter M w := by
  induction w with
  | nil => exact map_one _
  | cons s w ih =>
    change artinCoxeter M (generator M s * wordArtin M w) = M.toCoxeterSystem.simple s * wordCoxeter M w
    rw [map_mul,artinCoxeter_generator,ih]

@[simp] lemma artinCoxeter_positiveLift (w : M.Group) :
    artinCoxeter M (positiveLift M w) = w := by
  rw [positiveLift,artinCoxeter_word,wordCoxeter_reducedExpression]

lemma positiveLift_injective : Function.Injective (positiveLift M) :=
  Function.LeftInverse.injective (artinCoxeter_positiveLift M)

def CoxeterCellFace := {c : M.Group × Set S //
  ∀ v ∈ coxeterParabolic M c.2,
    M.toCoxeterSystem.length c.1 ≤ M.toCoxeterSystem.length (c.1 * v)}

namespace CoxeterCellFace
variable {M}
def vertexSet (c : CoxeterCellFace M) : Set M.Group :=
  {w | c.val.1⁻¹ * w ∈ coxeterParabolic M c.val.2}

lemma source_mem (c : CoxeterCellFace M) : c.val.1 ∈ c.vertexSet := by
  change c.val.1⁻¹*c.val.1 ∈ coxeterParabolic M c.val.2
  simp

lemma vertices_subset_iff (c d : CoxeterCellFace M) (ht : c.val.2 ⊆ d.val.2) :
    c.vertexSet ⊆ d.vertexSet ↔ c.val.1 ∈ d.vertexSet := by
  constructor
  · intro h; exact h c.source_mem
  · intro h w hw
    have he : d.val.1⁻¹*w = (d.val.1⁻¹*c.val.1)*(c.val.1⁻¹*w) := by group
    change d.val.1⁻¹*w ∈ coxeterParabolic M d.val.2
    rw [he]
    exact (coxeterParabolic M d.val.2).mul_mem h (coxeterParabolic_mono M ht hw)

instance : PartialOrder (CoxeterCellFace M) where
  le c d := c.val.2 ⊆ d.val.2 ∧ c.vertexSet ⊆ d.vertexSet
  le_refl _ := ⟨Set.Subset.rfl,Set.Subset.rfl⟩
  le_trans _ _ _ h k := ⟨h.1.trans k.1,h.2.trans k.2⟩
  le_antisymm c d h k := by
    have ht := Set.Subset.antisymm h.1 k.1
    have hm := h.2 c.source_mem
    have hl := length_mul_of_right_minimum M.toCoxeterSystem d.val.2 d.val.1 d.property
      (d.val.1⁻¹*c.val.1) hm
    rw [mul_inv_cancel_left] at hl
    have hh := k.2 d.source_mem
    have hk := length_mul_of_right_minimum M.toCoxeterSystem c.val.2 c.val.1 c.property
      (c.val.1⁻¹*d.val.1) hh
    rw [mul_inv_cancel_left] at hk
    have hz : M.toCoxeterSystem.length (d.val.1⁻¹*c.val.1) = 0 := by omega
    have he := M.toCoxeterSystem.length_eq_zero_iff.mp hz
    exact Subtype.ext (Prod.ext (inv_mul_eq_one.mp he).symm ht)

lemma le_iff (c d : CoxeterCellFace M) : c ≤ d ↔
    c.val.2 ⊆ d.val.2 ∧ c.val.1 ∈ d.vertexSet := by
  change (_ ∧ _) ↔ _
  constructor
  · intro h; exact ⟨h.1,h.2 c.source_mem⟩
  · intro h; exact ⟨h.1,(vertices_subset_iff c d h.1).mpr h.2⟩

end CoxeterCellFace

variable [Finite S] [Finite M.Group]

noncomputable def coxeterFaceToLifted (c : CoxeterCellFace M) : LiftedCell M :=
  (positiveLift M c.val.1, ⟨c.val.2,show Finite (coxeterParabolic M c.val.2) from inferInstance⟩)

omit [Finite S] in
lemma coxeterFaceToLifted_full (c : CoxeterCellFace M) :
    coxeterFaceToLifted M c ≤ fullSphericalCell M := by
  rw [lifted_le_iff_face]
  let w := reducedExpression M c.val.1
  refine ⟨Set.subset_univ _,w,(by intros; trivial),reducedExpression_reduced M _,?_,?_⟩
  · intro v
    rw [wordCoxeter_reducedExpression]
    exact c.property v v.property
  · exact (one_mul _).symm

omit [Finite S] in
lemma coxeterFaceToLifted_injective : Function.Injective (coxeterFaceToLifted M) := by
  intro c d he
  have h1 : positiveLift M c.val.1 = positiveLift M d.val.1 := congrArg Prod.fst he
  have h2 : c.val.2 = d.val.2 := congrArg (fun b : LiftedCell M => b.2.val) he
  exact Subtype.ext (Prod.ext (positiveLift_injective M h1) h2)

lemma coxeterFaceToLifted_le_iff (c d : CoxeterCellFace M) :
    coxeterFaceToLifted M c ≤ coxeterFaceToLifted M d ↔ c ≤ d := by
  rw [lifted_le_iff_face,CoxeterCellFace.le_iff]
  constructor
  · rintro ⟨ht,u,hu,_,_,he⟩
    refine ⟨ht,?_⟩
    have hp := congrArg (artinCoxeter M) he
    simp only [coxeterFaceToLifted,map_mul,artinCoxeter_word,artinCoxeter_positiveLift] at hp
    change d.val.1⁻¹*c.val.1 ∈ coxeterParabolic M d.val.2
    rw [hp,inv_mul_cancel_left]
    exact wordCoxeter_mem_parabolic M _ u hu
  · rintro ⟨ht,hm⟩
    let q := d.val.1⁻¹*c.val.1
    have hq : q ∈ coxeterParabolic M d.val.2 := hm
    have hprod : d.val.1*q = c.val.1 := mul_inv_cancel_left _ _
    have hadd := length_mul_of_right_minimum M.toCoxeterSystem d.val.2 d.val.1 d.property q hq
    have hmin : ∀ v ∈ coxeterParabolic M c.val.2,
        M.toCoxeterSystem.length q ≤ M.toCoxeterSystem.length (q*v) := by
      intro v hv
      have H := c.property v hv
      have ha := length_mul_of_right_minimum M.toCoxeterSystem d.val.2 d.val.1 d.property
        (q*v) ((coxeterParabolic M d.val.2).mul_mem hq (coxeterParabolic_mono M ht hv))
      rw [←hprod,mul_assoc,ha] at H
      rw [hadd] at H
      omega
    obtain ⟨u,hu,hr,he⟩ := (mem_parabolic_iff_reduced_word M.toCoxeterSystem d.val.2 q).mp hq
    refine ⟨ht,u,hu,hr,?_,?_⟩
    · intro v
      change wordCoxeter M u = q at he
      rw [he]
      exact hmin v v.property
    · change positiveLift M c.val.1 = positiveLift M d.val.1 * wordArtin M u
      rw [←positiveLift_word M u hr]
      change wordCoxeter M u = q at he
      rw [he,←positiveLift_mul M _ _ hadd,hprod]

noncomputable def coxeterFacesClosedLiftedIso : CoxeterCellFace M ≃o
    {b : LiftedCell M // b ≤ fullSphericalCell M} :=
  OrderIso.ofSurjective
    (OrderEmbedding.ofMapLEIff
      (fun c : CoxeterCellFace M => (⟨coxeterFaceToLifted M c,coxeterFaceToLifted_full M c⟩ :
        {b : LiftedCell M // b ≤ fullSphericalCell M}))
      (fun c d => coxeterFaceToLifted_le_iff M c d)) (by
      rintro ⟨b,hb⟩
      obtain ⟨_,u,_,hr,hm,he⟩ := (lifted_le_iff_face M _ _).mp hb
      let c : CoxeterCellFace M := ⟨(wordCoxeter M u,b.2.val),fun v hv => hm ⟨v,hv⟩⟩
      refine ⟨c,Subtype.ext (Prod.ext ?_ (Subtype.ext rfl))⟩
      change positiveLift M (wordCoxeter M u) = b.1
      rw [positiveLift_word M u hr]
      simpa only [fullSphericalCell,one_mul] using he.symm)

end HarmonicArtin

end OAI
