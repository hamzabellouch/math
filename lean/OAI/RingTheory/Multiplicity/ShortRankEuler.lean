import Mathlib
import OAI.RingTheory.Multiplicity.ComplexTheorem
import OAI.RingTheory.Multiplicity.FrobeniusHomologyGrowth

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]

omit [IsDomain R] in
lemma maximalIdeal_ne_bot_of_dimension_pos [IsDomain R] (hd : 0 < dimension R) :
    IsLocalRing.maximalIdeal R ≠ ⊥ := by
  intro he
  have hf : IsField R := Ring.isField_iff_maximal_bot.mpr (he ▸ IsLocalRing.maximalIdeal.isMaximal R)
  let := hf.toField
  have hh := dimension_cast R
  simp only [ringKrullDim_eq_zero_of_field] at hh
  have : dimension R = 0 := by exact_mod_cast hh
  omega

lemma short_rank_euler_zero (hd : 0 < dimension R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
    ∑ i∈Finset.range (dimension R+1),(-1:ℝ)^i*
      (Module.finrank R (F.X (-(i:ℤ))):ℝ) = 0 := by
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (maximalIdeal_ne_bot_of_dimension_pos hd)
  obtain ⟨a,ha⟩ := ProjectiveGhost.exists_nullhomotopy_power F
    (-(dimension R:ℤ)) (dimension R+1)
    (fun i => by have := hF.term_free i; infer_instance)
    (fun i hi => hF.bounded i (by omega)) hF.homology_finite_length x hx
  let K := FractionRing R
  let E := ModuleCat.extendScalars (algebraMap R K)
  let G := (E.mapHomologicalComplex (.up ℤ)).obj F
  have hz : algebraMap R K (x^a) ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr (pow_ne_zero _ hx0)
  have hc : Homotopy (𝟙 G) 0 := by
    have H := extendScalars_nullhomotopy (algebraMap R K) F (x^a) ha.some
    have H' := H.smul ((algebraMap R K (x^a))⁻¹)
    simpa only [smul_smul,inv_mul_cancel₀ hz,one_smul,smul_zero] using H'
  have hex := acyclic_of_contractible G hc
  let ell : TorsionLength (⊥ : Ideal K) := ordinaryLength ⊥
  have hval (j : ℤ) : ell.realValue (G.X j) = (Module.finrank R (F.X j):ℝ) := by
    have := hF.term_free j
    have := hF.term_finite j
    have : Module.Finite K (G.X j) := finite_extendScalars (algebraMap R K) (F.X j)
    dsimp [ell,TorsionLength.realValue,ordinaryLength]
    rw [Module.length_eq_finrank,ENat.toENNReal_coe,ENNReal.toReal_natCast]
    exact congrArg Nat.cast (finrank_extendScalars (algebraMap R K) (F.X j))
  have hfin (j : ℤ) : ell.finiteClass (G.X j) := by
    refine ⟨⟨1,by simp⟩,?_⟩
    have := hF.term_free j
    have := hF.term_finite j
    have : Module.Finite K (G.X j) := finite_extendScalars (algebraMap R K) (F.X j)
    change (Module.length K (G.X j)).toENNReal ≠ ⊤
    rw [Module.length_eq_finrank,ENat.toENNReal_coe]
    exact ENNReal.natCast_ne_top _
  have he := exact_euler_zero ell G (-(dimension R:ℤ)) (dimension R) hex hfin
    (E.map_isZero (hF.bounded _ (by left; omega)))
    (E.map_isZero (hF.bounded _ (by right; omega)))
  simp_rw [hval] at he
  exact ProductSourceCover.rank_reverse_zero (dimension R) (fun j => (Module.finrank R (F.X j):ℝ)) he
end Lech

end

end OAI
