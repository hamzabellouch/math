import OAI.RepresentationTheory.RestrictedTilting.TensorExactness

namespace OAI

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace FiberFunctorProof
universe v u
noncomputable section
variable {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [RigidCategory C]

 
omit [MonoidalPreadditive C] in
lemma cokernel_tensor_subunit_zero {U : C} (i : U ⟶ 𝟙_ C) [Mono i] :
    IsZero (cokernel i ⊗ U) := by
  let := tensorRight_preservesFiniteColimits U
  let := tensorLeft_preservesFiniteLimits (cokernel i)
  let q := cokernel.π i
  have hq : Epi (q ▷ U) := inferInstanceAs (Epi ((tensorRight U).map q))
  have hi : Mono ((cokernel i) ◁ i) :=
    inferInstanceAs (Mono ((tensorLeft (cokernel i)).map i))
  have h : q ▷ U ≫ (cokernel i) ◁ i = 0 := by
    calc
      _ = (λ_ U).hom ≫ i ≫ q ≫ (ρ_ (cokernel i)).inv := by
        rw [← whisker_exchange]
        monoidal
      _ = 0 := by simp [q]
  have hz : (cokernel i) ◁ i = 0 := (cancel_epi (q ▷ U)).1 (by simpa using h)
  exact IsZero.of_mono_eq_zero _ hz

 

def unitTranspose {U : C} (i : U ⟶ 𝟙_ C) : 𝟙_ C ⟶ Uᘁ :=
  η_ U Uᘁ ≫ i ▷ Uᘁ ≫ (λ_ Uᘁ).hom

omit [Abelian C] [MonoidalPreadditive C] in
lemma unitTranspose_homEquiv {U T X : C} (i : U ⟶ 𝟙_ C) (j : T ⟶ X) :
    tensorRightHomEquiv T U Uᘁ X (T ◁ i ≫ (ρ_ T).hom ≫ j) =
      j ≫ (ρ_ X).inv ≫ X ◁ unitTranspose i := by
  calc
    _ = (ρ_ T).inv ≫ T ◁ unitTranspose i ≫ j ▷ Uᘁ := by
      dsimp [tensorRightHomEquiv, unitTranspose]
      monoidal
    _ = (ρ_ T).inv ≫ j ▷ (𝟙_ C) ≫ X ◁ unitTranspose i := by
      rw [whisker_exchange]
    _ = _ := by monoidal

 

lemma unitTranspose_subobject_zero_iff {U T X : C} (i : U ⟶ 𝟙_ C) [Mono i]
    (j : T ⟶ X) [Mono j] :
    j ≫ (ρ_ X).inv ≫ X ◁ unitTranspose i = 0 ↔ IsZero (T ⊗ U) := by
  let := tensorLeft_preservesFiniteLimits T
  have : Mono (T ◁ i) := inferInstanceAs (Mono ((tensorLeft T).map i))
  have : Mono (T ◁ i ≫ (ρ_ T).hom ≫ j) := inferInstance
  have hzero : tensorRightHomEquiv T U Uᘁ X (0 : T ⊗ U ⟶ X) = 0 := by
    simp [tensorRightHomEquiv]
  rw [← unitTranspose_homEquiv, ← hzero, Equiv.apply_eq_iff_eq]
  constructor
  · exact IsZero.of_mono_eq_zero _
  · intro h
    exact h.eq_of_src _ _

variable [BraidedCategory C]

 

lemma subunit_cokernel_section {U : C} (i : U ⟶ 𝟙_ C) [Mono i] :
    ∃ s : cokernel i ⟶ 𝟙_ C, s ≫ cokernel.π i = 𝟙 (cokernel i) := by
  let V := cokernel i
  let q : 𝟙_ C ⟶ V := cokernel.π i
  let d := unitTranspose i
  let W := kernel d
  let w : W ⟶ 𝟙_ C := kernel.ι d
  have hw : IsZero (W ⊗ U) := (unitTranspose_subobject_zero_iff i w).1 (by
    change w ≫ (ρ_ (𝟙_ C)).inv ≫ (𝟙_ C) ◁ d = 0
    calc
      _ = w ≫ d ≫ (λ_ Uᘁ).inv := by monoidal
      _ = 0 := by simp [w])
  have hV : V ◁ d = 0 := by
    have h := (unitTranspose_subobject_zero_iff i (𝟙 V)).2
      (cokernel_tensor_subunit_zero i)
    simpa [d] using (cancel_epi (ρ_ V).inv).1 (by simpa using h)
  let := tensorLeft_preservesFiniteLimits V
  let := tensorLeft_preservesFiniteColimits V
  have hvw : Epi (V ◁ w) :=
    ((ShortComplex.kernelSequence_exact d).map (tensorLeft V)).epi_f hV
  have hvwm : Mono (V ◁ w) :=
    inferInstanceAs (Mono ((tensorLeft V).map (kernel.ι d)))
  have hvwi : IsIso (V ◁ w) := isIso_of_mono_of_epi _
  have hwi : IsIso (w ▷ V) := by
    have he : w ▷ V = (β_ W V).hom ≫ V ◁ w ≫ (β_ (𝟙_ C) V).inv := by
      rw [← braiding_naturality_left_assoc]
      simp
    rw [he]
    infer_instance
  let := tensorLeft_preservesFiniteLimits W
  let := tensorLeft_preservesFiniteColimits W
  have hwqm : Mono (W ◁ q) :=
    ((ShortComplex.cokernelSequence_exact i).map (tensorLeft W)).mono_g
      (hw.eq_of_src _ _)
  have hwqe : Epi (W ◁ q) :=
    inferInstanceAs (Epi ((tensorLeft W).map (cokernel.π i)))
  have hwqi : IsIso (W ◁ q) := isIso_of_mono_of_epi _
  have hcomp : w ≫ q = (ρ_ W).inv ≫ W ◁ q ≫ w ▷ V ≫ (λ_ V).hom := by
    rw [whisker_exchange_assoc]
    monoidal
  have : IsIso (w ≫ q) := by rw [hcomp]; infer_instance
  refine ⟨inv (w ≫ q) ≫ w, ?_⟩
  change (inv (w ≫ q) ≫ w) ≫ q = _
  simp
  rfl

 
lemma subunit_retraction {U : C} (i : U ⟶ 𝟙_ C) [Mono i] :
    ∃ r : 𝟙_ C ⟶ U, i ≫ r = 𝟙 U := by
  obtain ⟨s, hs⟩ := subunit_cokernel_section i
  let e := ShortComplex.Splitting.ofExactOfSection (ShortComplex.cokernelSequence i)
    (ShortComplex.cokernelSequence_exact i) s hs (show Mono i from inferInstance)
  exact ⟨e.r, e.f_r⟩
end
end FiberFunctorProof

end OAI
