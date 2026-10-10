import Mathlib
import OAI.RingTheory.Multiplicity.SourceGradedThickeningNat

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech.Koszul
universe u
variable {R : Type u} [CommRing R]
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  [CategoryTheory.Linear R C]

abbrev scalarCone (a : R) (F : CochainComplex C ℤ) := mappingCone (a • 𝟙 F)
noncomputable abbrev cInl (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    F.X (i+1) ⟶ (scalarCone a F).X i :=
  homotopyCofiber.inlX (a • 𝟙 F) (i+1) i rfl
noncomputable abbrev cInr (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    F.X i ⟶ (scalarCone a F).X i := homotopyCofiber.inrX (a • 𝟙 F) i
noncomputable abbrev cFst (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    (scalarCone a F).X i ⟶ F.X (i+1) :=
  homotopyCofiber.fstX (a • 𝟙 F) i (i+1) rfl
noncomputable abbrev cSnd (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    (scalarCone a F).X i ⟶ F.X i := homotopyCofiber.sndX (a • 𝟙 F) i

@[reassoc (attr := simp)] lemma cInl_fst (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInl a F i ≫ cFst a F i = 𝟙 _ := homotopyCofiber.inlX_fstX _ _ _ _
@[reassoc (attr := simp)] lemma cInl_snd (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInl a F i ≫ cSnd a F i = 0 := homotopyCofiber.inlX_sndX _ _ _ _
@[reassoc (attr := simp)] lemma cInr_fst (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInr a F i ≫ cFst a F i = 0 := homotopyCofiber.inrX_fstX _ _ _ _
@[reassoc (attr := simp)] lemma cInr_snd (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInr a F i ≫ cSnd a F i = 𝟙 _ := homotopyCofiber.inrX_sndX _ _

@[reassoc] lemma cInl_d (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInl a F i ≫ (scalarCone a F).d i (i+1) =
    -(F.d (i+1) (i+1+1) ≫ cInl a F (i+1)) + a • cInr a F (i+1) := by
  change homotopyCofiber.inlX (a • 𝟙 F) (i+1) i rfl ≫
    homotopyCofiber.d (a • 𝟙 F) i (i+1) = _
  rw [homotopyCofiber.inlX_d (a • 𝟙 F) i (i+1) (i+1+1) rfl rfl]
  change -F.d (i+1) (i+1+1) ≫ cInl a F (i+1) +
    (a • 𝟙 F).f (i+1) ≫ cInr a F (i+1) = _
  simp only [HomologicalComplex.smul_f_apply,HomologicalComplex.id_f,
    Linear.smul_comp,Category.id_comp]
@[reassoc] lemma cInr_d (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInr a F i ≫ (scalarCone a F).d i (i+1) =
      F.d i (i+1) ≫ cInr a F (i+1) :=
  homotopyCofiber.inrX_d _ _ _

noncomputable def coneSwapX (a b : R) (F : CochainComplex C ℤ) (i : ℤ) :
    (scalarCone a (scalarCone b F)).X i ⟶ (scalarCone b (scalarCone a F)).X i :=
  -(cFst a (scalarCone b F) i ≫ cFst b F (i+1) ≫
    cInl a F (i+1) ≫ cInl b (scalarCone a F) i) +
  cFst a (scalarCone b F) i ≫ cSnd b F (i+1) ≫
    cInl a F i ≫ cInr b (scalarCone a F) i +
  cSnd a (scalarCone b F) i ≫ cFst b F i ≫
    cInr a F (i+1) ≫ cInl b (scalarCone a F) i +
  cSnd a (scalarCone b F) i ≫ cSnd b F i ≫
    cInr a F i ≫ cInr b (scalarCone a F) i

@[reassoc (attr := simp)] lemma inll_coneSwapX (a b : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInl b F (i+1) ≫ cInl a (scalarCone b F) i ≫ coneSwapX a b F i =
      -(cInl a F (i+1) ≫ cInl b (scalarCone a F) i) := by
  simp [coneSwapX,Preadditive.comp_add,Preadditive.comp_neg]
@[reassoc (attr := simp)] lemma inrl_coneSwapX (a b : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInr b F (i+1) ≫ cInl a (scalarCone b F) i ≫ coneSwapX a b F i =
      cInl a F i ≫ cInr b (scalarCone a F) i := by
  simp [coneSwapX,Preadditive.comp_add,Preadditive.comp_neg]
@[reassoc (attr := simp)] lemma inlr_coneSwapX (a b : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInl b F i ≫ cInr a (scalarCone b F) i ≫ coneSwapX a b F i =
      cInr a F (i+1) ≫ cInl b (scalarCone a F) i := by
  simp [coneSwapX,Preadditive.comp_add,Preadditive.comp_neg]
@[reassoc (attr := simp)] lemma inrr_coneSwapX (a b : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInr b F i ≫ cInr a (scalarCone b F) i ≫ coneSwapX a b F i =
      cInr a F i ≫ cInr b (scalarCone a F) i := by
  simp [coneSwapX,Preadditive.comp_add,Preadditive.comp_neg]

noncomputable def coneSwap (a b : R) (F : CochainComplex C ℤ) :
    scalarCone a (scalarCone b F) ⟶ scalarCone b (scalarCone a F) where
  f := coneSwapX a b F
  comm' := by
    intro i j hij
    obtain rfl : i+1=j := hij
    apply homotopyCofiber.ext_from_X (a • 𝟙 (scalarCone b F)) (i+1) i rfl
    · apply homotopyCofiber.ext_from_X (b • 𝟙 F) (i+1+1) (i+1) rfl
      · change cInl b F (i+1) ≫ cInl a (scalarCone b F) i ≫ _ =
          cInl b F (i+1) ≫ cInl a (scalarCone b F) i ≫ _
        simp only [Category.assoc,cInl_d_assoc,cInl_d,
          Preadditive.comp_neg,Preadditive.comp_add,Preadditive.neg_comp,
          Preadditive.add_comp,Linear.comp_smul,Linear.smul_comp,
          inll_coneSwapX_assoc,inll_coneSwapX,inrl_coneSwapX,inlr_coneSwapX,
          neg_neg]
        abel
      · change cInr b F (i+1) ≫ cInl a (scalarCone b F) i ≫ _ =
          cInr b F (i+1) ≫ cInl a (scalarCone b F) i ≫ _
        simp only [Category.assoc,cInl_d_assoc,cInr_d_assoc,cInr_d,
          Preadditive.comp_neg,Preadditive.comp_add,Preadditive.neg_comp,
          Preadditive.add_comp,Linear.comp_smul,Linear.smul_comp,
          inrl_coneSwapX_assoc,inrl_coneSwapX,inrr_coneSwapX]
    · apply homotopyCofiber.ext_from_X (b • 𝟙 F) (i+1) i rfl
      · change cInl b F i ≫ cInr a (scalarCone b F) i ≫ _ =
          cInl b F i ≫ cInr a (scalarCone b F) i ≫ _
        simp only [Category.assoc,cInl_d_assoc,cInr_d_assoc,cInl_d,
          Preadditive.comp_neg,Preadditive.comp_add,Preadditive.neg_comp,
          Preadditive.add_comp,Linear.comp_smul,Linear.smul_comp,
          inlr_coneSwapX_assoc,inlr_coneSwapX,inrr_coneSwapX]
      · change cInr b F i ≫ cInr a (scalarCone b F) i ≫ _ =
          cInr b F i ≫ cInr a (scalarCone b F) i ≫ _
        simp only [cInr_d_assoc,cInr_d,inrr_coneSwapX_assoc,inrr_coneSwapX]

lemma coneSwapX_involutive (a b : R) (F : CochainComplex C ℤ) (i : ℤ) :
    coneSwapX a b F i ≫ coneSwapX b a F i = 𝟙 _ := by
  apply homotopyCofiber.ext_from_X (a • 𝟙 (scalarCone b F)) (i+1) i rfl
  · apply homotopyCofiber.ext_from_X (b • 𝟙 F) (i+1+1) (i+1) rfl
    · change cInl b F (i+1) ≫ cInl a (scalarCone b F) i ≫ _ =
        cInl b F (i+1) ≫ cInl a (scalarCone b F) i ≫ _
      simp only [inll_coneSwapX_assoc,Preadditive.neg_comp,Category.assoc,inll_coneSwapX,
        neg_neg,Category.comp_id]
    · change cInr b F (i+1) ≫ cInl a (scalarCone b F) i ≫ _ =
        cInr b F (i+1) ≫ cInl a (scalarCone b F) i ≫ _
      simp only [inrl_coneSwapX_assoc,inlr_coneSwapX,Category.comp_id]
  · apply homotopyCofiber.ext_from_X (b • 𝟙 F) (i+1) i rfl
    · change cInl b F i ≫ cInr a (scalarCone b F) i ≫ _ =
        cInl b F i ≫ cInr a (scalarCone b F) i ≫ _
      simp only [inlr_coneSwapX_assoc,inrl_coneSwapX,Category.comp_id]
    · change cInr b F i ≫ cInr a (scalarCone b F) i ≫ _ =
        cInr b F i ≫ cInr a (scalarCone b F) i ≫ _
      simp only [inrr_coneSwapX_assoc,inrr_coneSwapX,Category.comp_id]

noncomputable def coneSwapIso (a b : R) (F : CochainComplex C ℤ) :
    scalarCone a (scalarCone b F) ≅ scalarCone b (scalarCone a F) where
  hom := coneSwap a b F
  inv := coneSwap b a F
  hom_inv_id := by ext i; exact coneSwapX_involutive a b F i
  inv_hom_id := by ext i; exact coneSwapX_involutive b a F i

 

noncomputable def tensorConeIso (zs : List R) (a : R) (F : CochainComplex C ℤ) :
    scalarCone a (tensor zs F) ≅ tensor zs (scalarCone a F) := by
  induction zs with
  | nil => exact Iso.refl _
  | cons b zs ih => exact coneSwapIso a b (tensor zs F) ≪≫ (coneFunctor b).mapIso ih

end Lech.Koszul

end

end OAI
