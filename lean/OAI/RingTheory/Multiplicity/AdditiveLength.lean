import Mathlib
import OAI.RingTheory.Multiplicity.HomologyLengthDevissage

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R]

lemma additive_length_pi (T : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [T.Additive]
    {ι : Type} [Fintype ι] (M : ι → ModuleCat.{u} R) :
    Module.length R (T.obj (ModuleCat.of R (∀ i,M i))) =
      ∑ i,Module.length R (T.obj (M i)) := by
  let e := T.mapIso (ModuleCat.biproductIsoPi M).symm ≪≫
    T.mapBiproduct M ≪≫ ModuleCat.biproductIsoPi (fun i : ι => T.obj (M i))
  exact e.toLinearEquiv.length_eq.trans (Module.length_pi_of_fintype _ _)

lemma additive_length_finite_free [Nontrivial R] (T : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [T.Additive]
    (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M] :
    Module.length R (T.obj M) = Module.finrank R M •
      Module.length R (T.obj (ModuleCat.of R R)) := by
  classical
  let b := Module.Free.chooseBasis R M
  let := Module.Free.ChooseBasisIndex.fintype R M
  let e := (b.reindex (Fintype.equivFin _)).equivFun.toModuleIso
  rw [(T.mapIso e).toLinearEquiv.length_eq]
  rw [additive_length_pi T (fun _ : Fin (Fintype.card (Module.Free.ChooseBasisIndex R M)) => ModuleCat.of R R)]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  congr 1
  exact (Module.finrank_eq_card_basis b).symm
end Lech

end

end OAI
