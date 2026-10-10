import Mathlib

namespace OAI

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace FiberFunctorProof

universe v₁ v₂ u₁ u₂

section Tensor
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [RigidCategory C]

theorem tensorLeft_preservesFiniteLimits (X : C) :
    PreservesFiniteLimits (tensorLeft X) := by
  let : (tensorLeft X).IsRightAdjoint := (tensorLeftAdjunction X Xᘁ).isRightAdjoint
  infer_instance

theorem tensorLeft_preservesFiniteColimits (X : C) :
    PreservesFiniteColimits (tensorLeft X) := by
  let : (tensorLeft X).IsLeftAdjoint := (tensorLeftAdjunction (ᘁX) X).isLeftAdjoint
  infer_instance

theorem tensorRight_preservesFiniteLimits (X : C) :
    PreservesFiniteLimits (tensorRight X) := by
  let : (tensorRight X).IsRightAdjoint := (tensorRightAdjunction (ᘁX) X).isRightAdjoint
  infer_instance

theorem tensorRight_preservesFiniteColimits (X : C) :
    PreservesFiniteColimits (tensorRight X) := by
  let : (tensorRight X).IsLeftAdjoint := (tensorRightAdjunction X Xᘁ).isLeftAdjoint
  infer_instance

variable [Abelian C] [MonoidalPreadditive C]

lemma coevaluation_ne_zero (X : C) (hX : ¬ IsZero X) : η_ X Xᘁ ≠ 0 := by
  intro h
  apply hX
  apply (IsZero.iff_id_eq_zero _).2
  have he := ExactPairing.evaluation_coevaluation X Xᘁ
  rw [h] at he
  have hz : (λ_ X).hom ≫ (ρ_ X).inv = 0 := by simpa using he.symm
  have hz' := congrArg (fun f => (λ_ X).inv ≫ f ≫ (ρ_ X).hom) hz
  simpa using hz'

lemma tensorRight_faithful (X : C) [Simple (𝟙_ C)] (hX : ¬ IsZero X) :
    (tensorRight X).Faithful := by
  let : Mono (η_ X Xᘁ) := mono_of_nonzero_from_simple (coevaluation_ne_zero X hX)
  let : ∀ Y : C, Mono ((tensorRightAdjunction X Xᘁ).unit.app Y) := by
    intro Y
    let := tensorLeft_preservesFiniteLimits Y
    change Mono ((ρ_ Y).inv ≫ Y ◁ η_ X Xᘁ ≫ (α_ Y X Xᘁ).inv ≫ (𝟙 (Y ⊗ X)) ▷ Xᘁ)
    simp only [id_whiskerRight, Category.comp_id]
    have : Mono (Y ◁ η_ X Xᘁ) :=
      inferInstanceAs (Mono ((tensorLeft Y).map (η_ X Xᘁ)))
    infer_instance
  exact (tensorRightAdjunction X Xᘁ).faithful_L_of_mono_unit_app

lemma coevaluation_ne_zero_right (X : C) (hX : ¬ IsZero X) : η_ (ᘁX) X ≠ 0 := by
  intro h
  apply hX
  apply (IsZero.iff_id_eq_zero _).2
  have he := ExactPairing.coevaluation_evaluation (ᘁX) X
  rw [h] at he
  have hz : (ρ_ X).hom ≫ (λ_ X).inv = 0 := by simpa using he.symm
  have hz' := congrArg (fun f => (ρ_ X).inv ≫ f ≫ (λ_ X).hom) hz
  simpa using hz'

lemma tensorLeft_faithful (X : C) [Simple (𝟙_ C)] (hX : ¬ IsZero X) :
    (tensorLeft X).Faithful := by
  let : Mono (η_ (ᘁX) X) := mono_of_nonzero_from_simple (coevaluation_ne_zero_right X hX)
  let : ∀ Y : C, Mono ((tensorLeftAdjunction (ᘁX) X).unit.app Y) := by
    intro Y
    let := tensorRight_preservesFiniteLimits Y
    change Mono ((λ_ Y).inv ≫ η_ (ᘁX) X ▷ Y ≫ (α_ (ᘁX) X Y).hom ≫ (ᘁX) ◁ (𝟙 (X ⊗ Y)))
    simp only [whiskerLeft_id, Category.comp_id]
    have : Mono (η_ (ᘁX) X ▷ Y) :=
      inferInstanceAs (Mono ((tensorRight Y).map (η_ (ᘁX) X)))
    infer_instance
  exact (tensorLeftAdjunction (ᘁX) X).faithful_L_of_mono_unit_app

omit [Abelian C] [MonoidalPreadditive C] in
lemma projective_tensor (P X : C) [Projective P] : Projective (P ⊗ X) := by
  let := tensorRight_preservesFiniteColimits Xᘁ
  exact (tensorRightAdjunction X Xᘁ).map_projective P inferInstance

end Tensor

 
theorem exact_of_nonzero_projective
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [RigidCategory C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [MonoidalCategory D] [MonoidalPreadditive D] [RigidCategory D]
    [Simple (𝟙_ D)]
    (F : C ⥤ D) [F.Additive] [F.Monoidal]
    (P : C) [Projective P] (hP : ¬ IsZero (F.obj P))
    (S : ShortComplex C) (hS : S.ShortExact) :
    (S.map F).ShortExact := by
  let := tensorLeft_preservesFiniteLimits P
  let := tensorLeft_preservesFiniteColimits P
  have ht : (S.map (tensorLeft P)).ShortExact := hS.map_of_exact (tensorLeft P)
  let : Projective (S.map (tensorLeft P)).X₃ := projective_tensor P S.X₃
  have hs : ((S.map (tensorLeft P)).map F).ShortExact :=
    (ht.splittingOfProjective.map F).shortExact
  have he : ((S.map F).map (tensorLeft (F.obj P))).ShortExact :=
    ShortComplex.shortExact_of_iso
      (S.mapNatIso (Functor.Monoidal.commTensorLeft F P).symm) hs
  let := tensorLeft_faithful (F.obj P) hP
  exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful _ he

end FiberFunctorProof

end OAI
