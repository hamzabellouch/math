import Mathlib
import OAI.RingTheory.Multiplicity.ContractibleRetract

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]

lemma finite_free_retract {M N : ModuleCat.{u} R} [Module.Free R M] [Module.Finite R M]
    (i : N ⟶ M) (r : M ⟶ N) (hir : i ≫ r = 𝟙 N) :
    Module.Free R N ∧ Module.Finite R N := by
  have hr : Function.Surjective r := by
    intro x
    exact ⟨i x,congrArg (fun f : N ⟶ N => f x) hir⟩
  let : Module.Finite R N := Module.Finite.of_surjective r.hom hr
  let : Module.Flat R N := Module.Flat.of_retract i.hom r.hom
    (show r.hom.comp i.hom = LinearMap.id from congrArg ModuleCat.Hom.hom hir)
  exact ⟨Module.free_of_flat_of_isLocalRing,inferInstance⟩

omit [IsLocalRing R] in
lemma isZero_of_retract {M N : ModuleCat.{u} R}
    (i : N ⟶ M) (r : M ⟶ N) (hir : i ≫ r = 𝟙 N) (hM : IsZero M) : IsZero N := by
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← hir,hM.eq_of_tgt i 0,zero_comp]

omit [IsLocalRing R] in
lemma null_projector_contractible_splitting
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (q : F ⟶ F)
    (hq : q ≫ q = q) (hn : Homotopy q 0) :
    ∃ (G K : CochainComplex (ModuleCat.{u} R) ℤ)
      (i : G ⟶ F) (r : F ⟶ G) (a : K ⟶ F) (b : F ⟶ K),
      i ≫ r = 𝟙 G ∧ a ≫ b = 𝟙 K ∧ b ≫ a = q ∧
      r ≫ i + b ≫ a = 𝟙 F ∧ i ≫ b = 0 ∧ a ≫ r = 0 ∧
      Nonempty (HomotopyEquiv F G) := by
  obtain ⟨K,a,b,hab,hba⟩ := IsIdempotentComplete.idempotents_split F q hq
  have hK : Homotopy (𝟙 K) 0 := by
    have he : a ≫ q ≫ b = 𝟙 K := by simp only [← hba,Category.assoc,hab,Category.comp_id]
    have hn' := (hn.compLeft a).compRight b
    simpa only [Category.assoc,he,comp_zero,zero_comp] using hn'
  obtain ⟨G,i,r,hir,hs,hib,har,he⟩ := split_contractible_retract F K a b hab hK
  exact ⟨G,K,i,r,a,b,hir,hab,hba,hs,hib,har,he⟩
end Lech

end

end OAI
