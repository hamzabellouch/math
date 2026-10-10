import Mathlib
import OAI.RingTheory.Multiplicity.RootStageQuotient

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped TensorProduct ENNReal Topology
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
lemma frobenius_quotient_homology_finiteLength
    (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F)
    (I : Ideal R) (n : ℕ) (i : ℤ) :
    IsFiniteLength R (((complexQuotient I (.up ℤ)).obj (frobeniusComplex R p n F)).homology i) := by
  let G := frobeniusComplex R p n F
  let Q := (complexQuotient I (.up ℤ)).obj G
  have := hF.term_finite i
  have : Module.Finite R (G.X i) := finite_extendScalars (iterateFrobenius R p n) (F.X i)
  have : Module.Finite R (Q.X i) := Koszul.finite_moduleQuotient I (G.X i)
  have := finite_cochain_homology Q i
  apply finiteLength_of_maximal_le_radical_annihilator
  intro x hx
  obtain ⟨a,ha⟩ := ProjectiveGhost.exists_nullhomotopy_power F
    (-(dimension R : ℤ)) (dimension R+1)
    (fun j => by have := hF.term_free j; infer_instance)
    (fun j hj => hF.bounded j (by omega)) hF.homology_finite_length x hx
  refine ⟨a*(p^n),?_⟩
  exact Koszul.scalar_annihilates_homology Q (x^(a*(p^n)))
    (Koszul.quotient_nullhomotopy I G _ (frobenius_nullhomotopy p n a F x ha.some)) i
end Lech
namespace Lech.PerfectDomainStages
open Lech.RootTower Lech.Koszul
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [CharP K p] [CharP L p]
local instance robertsSeparablePowerSeriesIsDomain : IsDomain (MvPowerSeries (Fin h) k) :=
  NoZeroDivisors.to_isDomain _

include K L in
lemma frobenius_homology_conductor_bound
    (hdim : dimension D = h)
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D)))
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsFiniteHomologyComplex D F) :
    ∃ a : D, a ≠ 0 ∧ ∀ n i, i < 0 →
      Module.length D ((frobeniusComplex D p n F).homology i) ≤
        Module.length D (((complexQuotient (Ideal.span {a}) (.up ℤ)).obj
          (frobeniusComplex D p n F)).homology i) := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let C := PerfectClosure D p
  let T := regularTower (Fin h) k p
  have hflat := perfectClosure_flat (Fin h) k p
  let : IsIntegrallyClosed A := isIntegrallyClosed_of_flat_frobenius A p
    (fun n => iterateFrobenius_flat (σ := Fin h) (R := k) p n)
  have hAD : Function.Injective (algebraMap A D) := by
    apply Function.Injective.of_comp (f := algebraMap D L)
    rw [← RingHom.coe_comp,← IsScalarTower.algebraMap_eq A D L]
    rw [IsScalarTower.algebraMap_eq A K L,RingHom.coe_comp]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  obtain ⟨a,ha,hac⟩ := exists_conductor A D p L K
  have haD : algebraMap A D a ≠ 0 := (map_ne_zero_iff _ hAD).mpr ha
  refine ⟨algebraMap A D a,haD,fun n i hi => ?_⟩
  have hinj := tensorMap_injective A D p L K hflat n
  have hp0 : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  have hq0 : (p : ℝ≥0∞)^(n*h) ≠ 0 := pow_ne_zero _ hp0
  have hqfin : (p : ℝ≥0∞)^(n*h) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  let B := stage A D p n
  let g := rootMap A p n a
  let : Algebra D B := (originalToStage A D p n).toAlgebra
  let : Algebra D C := (PerfectClosure.of D p).toAlgebra
  let : IsScalarTower D B C := IsScalarTower.of_algebraMap_eq' rfl
  have hstage : T.length ((stageComplex h k D p n F).homology i) ≠ ⊤ := by
    rw [show T.length ((stageComplex h k D p n F).homology i) = _ from
      normalizedLength_stage_homology h k D p hres F hF.term_finite n hinj i]
    apply ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hq0)
    exact ENat.toENNReal_ne_top.mpr (Module.length_ne_top_iff.mpr
      (frobenius_shortComplex_homology_finiteLength p F hF n i))
  have hfree (j : ℤ) : Module.Free D ((frobeniusComplex D p n F).X j) := by
    have := hF.term_free j
    exact free_extendScalars (iterateFrobenius D p n) (F.X j)
  have hgi (j : ℤ) : Function.Injective (fun x : (stageComplex h k D p n F).X j => g • x) := by
    let e := ((HomologicalComplex.eval _ _ j).mapIso (stageRootIso h k D p n F)).toLinearEquiv
    intro x y hxy
    apply e.injective
    apply rootStage_scalar_injective h k D p n a haD (frobeniusComplex D p n F) hfree j
    simpa only [← e.map_smul] using congrArg e hxy
  have hb := Lech.TensorConductor.stage_homology_length_le B T F g (hac n) i hgi hstage
  have hz : T.length ((Lech.TensorConductor.ambientComplex (R:=P) (C:=C) F).homology i) = 0 := by
    apply (T.length_eq_of_equiv
      (restrictionHomologyIso (algebraMap P C)
        (((ModuleCat.extendScalars (PerfectClosure.of D p)).mapHomologicalComplex _).obj F) i).toLinearEquiv).trans
    exact Lech.SeparableOrder.normalizedLength_perfection_shortComplex_homology
      h k D p K L hdim F hF i hi
  rw [hz,zero_add] at hb
  change normalizedLength (Fin h) k p ((stageComplex h k D p n F).homology i) ≤
    normalizedLength (Fin h) k p (((complexQuotient (Ideal.span {g}) (.up ℤ)).obj
      (stageComplex h k D p n F)).homology i) at hb
  rw [normalizedLength_stage_homology h k D p hres F hF.term_finite n hinj i,
    normalizedLength_stage_scalar_quotient_homology h k D p hres F hF.term_free hF.term_finite n hinj a haD i] at hb
  have hc := (ENNReal.mul_le_mul_iff_right (ENNReal.inv_ne_zero.mpr hqfin)
    (ENNReal.inv_ne_top.mpr hq0)).mp hb
  exact ENat.toENNReal_le.mp hc

include K L in
 
theorem frobenius_shortComplex_homology_tendsto_zero
    (hdim : dimension D = h)
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D)))
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsFiniteHomologyComplex D F)
    (i : ℤ) (hi : i < 0) :
    Tendsto (fun n : ℕ => ((Module.length D ((frobeniusComplex D p n F).homology i)).toNat : ℝ) /
      ((p:ℝ)^n)^(dimension D)) atTop (𝓝 0) := by
  obtain ⟨a,ha,hbound⟩ := frobenius_homology_conductor_bound h k D p K L hdim hres F hF
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast (Nat.Prime.pos (Fact.out : p.Prime))
  by_cases hu : IsUnit a
  · have hz (n : ℕ) : Module.length D ((frobeniusComplex D p n F).homology i) = 0 := by
      apply le_zero_iff.mp
      apply (hbound n i hi).trans
      let Q := (complexQuotient (Ideal.span {a}) (.up ℤ)).obj (frobeniusComplex D p n F)
      have he : a • 𝟙 Q = 0 := complexQuotient_annihilated (Ideal.span {a}) a
        (Ideal.subset_span (Set.mem_singleton a)) (frobeniusComplex D p n F)
      have hQ : IsZero Q := (IsZero.iff_id_eq_zero Q).mpr (hu.smul_eq_zero.mp he)
      have : Subsingleton (Q.homology i) := ModuleCat.isZero_iff_subsingleton.mp
        ((homologyFunctor (ModuleCat D) (.up ℤ) i).map_isZero hQ)
      exact le_of_eq (Module.length_eq_zero (R:=D) (M:=Q.homology i))
    simpa only [hz,ENat.toNat_zero,Nat.cast_zero,zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  · obtain ⟨zs,hd,hzs,hprim⟩ := exists_small_quotient_parameters a
      (mem_nonZeroDivisors_of_ne_zero ha) hu
    apply squeeze_zero (g := fun n : ℕ =>
      ((Module.length D (((complexQuotient (Ideal.span {a}) (.up ℤ)).obj
        (frobeniusComplex D p n F)).homology i)).toNat : ℝ) / ((p:ℝ)^n)^(dimension D))
    · intro n; positivity
    · intro n
      apply (div_le_div_iff_of_pos_right (by positivity)).mpr
      exact_mod_cast ENat.toNat_le_toNat (hbound n i hi) (Module.length_ne_top_iff.mpr
        (frobenius_quotient_homology_finiteLength p F hF (Ideal.span {a}) n i))
    · exact frobenius_quotient_homology_tendsto_zero p F hF (Ideal.span {a}) zs hzs hprim hd i
end Lech.PerfectDomainStages

end

end OAI
