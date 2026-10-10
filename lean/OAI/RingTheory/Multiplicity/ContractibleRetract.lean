import Mathlib
import OAI.RingTheory.Multiplicity.DuttaData

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R]

lemma split_contractible_retract (F K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a : K ⟶ F) (b : F ⟶ K) (hab : a ≫ b = 𝟙 K)
    (hK : Homotopy (𝟙 K) 0) :
    ∃ (G : CochainComplex (ModuleCat.{u} R) ℤ) (i : G ⟶ F) (r : F ⟶ G),
      i ≫ r = 𝟙 G ∧ r ≫ i + b ≫ a = 𝟙 F ∧ i ≫ b = 0 ∧ a ≫ r = 0 ∧
      Nonempty (HomotopyEquiv F G) := by
  have hq : (b ≫ a) ≫ (b ≫ a) = b ≫ a := by rw [Category.assoc,← Category.assoc a,hab,Category.id_comp]
  have hp : (𝟙 F - b ≫ a) ≫ (𝟙 F - b ≫ a) = 𝟙 F - b ≫ a :=
    CategoryTheory.Idempotents.idem_of_id_sub_idem _ hq
  obtain ⟨G,i,r,hir,hri⟩ := IsIdempotentComplete.idempotents_split F _ hp
  have hib : i ≫ b = 0 := by
    have he : i ≫ (r ≫ i) = i := by simp [← Category.assoc,hir]
    have hpb : (𝟙 F - b ≫ a) ≫ b = 0 := by simp [sub_comp,Category.assoc,hab]
    rw [← he,hri,Category.assoc,hpb,comp_zero]
  have har : a ≫ r = 0 := by
    have he : (r ≫ i) ≫ r = r := by simp [Category.assoc,hir]
    have hap : a ≫ (𝟙 F - b ≫ a) = 0 := by simp [comp_sub,← Category.assoc,hab]
    rw [← he,hri,← Category.assoc,hap,zero_comp]
  have hnull : Homotopy (b ≫ a) 0 := by simpa using (hK.compLeft b).compRight a
  have hh : Homotopy (r ≫ i) (𝟙 F) := by
    rw [hri]
    simpa [sub_eq_add_neg] using (Homotopy.refl (𝟙 F)).add (hnull.smul (-1:ℤ))
  exact ⟨G,i,r,hir,by rw [hri]; abel,hib,har,
    ⟨⟨r,i,hh,Homotopy.ofEq hir⟩⟩⟩

 
def complementaryRetractEquiv
    {F G K : ModuleCat.{u} R} (i : G ⟶ F) (r : F ⟶ G) (a : K ⟶ F) (b : F ⟶ K)
    (hir : i ≫ r = 𝟙 G) (hab : a ≫ b = 𝟙 K)
    (hs : r ≫ i + b ≫ a = 𝟙 F) (hib : i ≫ b = 0) (har : a ≫ r = 0) :
    F ≃ₗ[R] (G × K) :=
  LinearEquiv.ofLinearMap (r.hom.prod b.hom) (i.hom.coprod a.hom)
    (by
      apply LinearMap.ext
      intro x
      apply Prod.ext
      · have h1 := congrArg (fun f : G ⟶ G => f x.1) hir
        have h2 := congrArg (fun f : K ⟶ G => f x.2) har
        simpa using congrArg₂ (·+·) h1 h2
      · have h1 := congrArg (fun f : G ⟶ K => f x.1) hib
        have h2 := congrArg (fun f : K ⟶ K => f x.2) hab
        simpa using congrArg₂ (·+·) h1 h2)
    (by apply LinearMap.ext; intro x; exact congrArg (fun f : F ⟶ F => f x) hs)
end Lech

end

end OAI
