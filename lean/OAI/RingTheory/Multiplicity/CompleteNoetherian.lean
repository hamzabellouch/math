import Mathlib
import OAI.RingTheory.Multiplicity.PowerSeriesFinDimension

namespace OAI

noncomputable section
open IsLocalRing MvPowerSeries
namespace Lech.CompleteLocal
variable {k S : Type*} [Field k] [CommRing S] [IsLocalRing S]
  [IsAdicComplete (maximalIdeal S) S]

lemma noetherian_of_coefficient_and_fg (φ : k →+* S)
    (hφ : Function.Surjective ((residue S).comp φ)) (hfg : (maximalIdeal S).FG) :
    IsNoetherianRing S := by
  obtain ⟨n,z,hzspan⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  have hz : ∀ i,z i ∈ maximalIdeal S := fun i => hzspan ▸ Ideal.subset_span (Set.mem_range_self i)
  let A := MvPowerSeries (Fin n) k
  let I := Lech.PowerSeries.variablesIdeal (Fin n) k
  let ψ := Lech.PowerSeries.eval φ (maximalIdeal S) z hz
  let : Algebra k S := φ.toAlgebra
  let : Algebra A S := ψ.toAlgebra
  let : IsScalarTower k A S := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    exact (Lech.PowerSeries.eval_C φ (maximalIdeal S) z hz a).symm)
  have hmap : I.map (algebraMap A S)=maximalIdeal S := by
    change (Ideal.span (Set.range (X : Fin n → A))).map (algebraMap A S)=_
    rw [Ideal.map_span,← Set.range_comp]
    have he : (algebraMap A S) ∘ X=z := funext (fun i => Lech.PowerSeries.eval_X φ (maximalIdeal S) z hz i)
    rw [he]
    exact hzspan
  let : IsHausdorff I S := IsHausdorff.of_map (I:=I) (J:=maximalIdeal S) hmap.le
  let : IsPrecomplete I A := (Lech.PowerSeries.complete_variables (Fin n) k).toIsPrecomplete
  let : Module.Finite k (S ⧸ maximalIdeal S) :=
    Module.Finite.of_surjective (Algebra.linearMap k (S ⧸ maximalIdeal S)) hφ
  let : Module.Finite A (S ⧸ maximalIdeal S) := Module.Finite.of_restrictScalars_finite k A _
  have hsub : I • (⊤ : Submodule A S)=(maximalIdeal S).restrictScalars A := by
    rw [← hmap]
    symm
    simpa only [smul_eq_mul,Ideal.mul_top,Submodule.restrictScalars_top] using
      Submodule.restrictScalars_map_smul_eq I (⊤ : Submodule S S)
  let e := (Submodule.quotEquivOfEq _ _ hsub).trans
    (Submodule.Quotient.restrictScalarsEquiv A (maximalIdeal S))
  let : Module.Finite A (S ⧸ (I • (⊤ : Submodule A S))) := Module.Finite.equiv e.symm
  let : Module.Finite A S := Lech.AdicNakayama.finite_of_quotient I
  exact IsNoetherianRing.of_finite A S
end Lech.CompleteLocal

end

end OAI
