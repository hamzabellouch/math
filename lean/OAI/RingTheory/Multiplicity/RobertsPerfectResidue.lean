import Mathlib
import OAI.RingTheory.Multiplicity.RobertsNormalization

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace Lech.CharP
open Lech.RootTower Lech.PerfectDomainStages Lech.Koszul IsLocalRing Filter
open scoped ENNReal Topology nonZeroDivisors
universe u
variable (D : Type u) [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (ResidueField D) p]

theorem frobenius_homology_tendsto_zero
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : Lech.IsFiniteHomologyComplex D F)
    (i : ℤ) (hi : i < 0) :
    Tendsto (fun n : ℕ => ((Module.length D ((Lech.frobeniusComplex D p n F).homology i)).toNat : ℝ) /
      ((p:ℝ)^n)^(Lech.dimension D)) atTop (𝓝 0) := by
  obtain ⟨h,ψ,hψ,hfin,hloc,hres,hd⟩ :=
    Lech.Normalization.exists_finite_powerSeries_normalization D p
  have hdim : Lech.dimension D = h := by
    have hd' := Lech.dimension_cast D
    rw [hd] at hd'
    exact_mod_cast hd'
  let k := ResidueField D
  let : CharP k p := CharP.of_ringHom_of_ne_zero (residue D) p
    (Nat.Prime.ne_zero Fact.out)
  let A := MvPowerSeries (Fin h) k
  let C := PerfectClosure D p
  let P := PerfectClosure A p
  let : IsDomain A := NoZeroDivisors.to_isDomain _
  let : Algebra A D := ψ.toAlgebra
  let : Module.Finite A D := hfin
  let : IsLocalHom (algebraMap A D) := hloc
  have hf : Function.Injective (algebraMap A D) := hψ
  have hres' : Function.Surjective (algebraMap (ResidueField A) (ResidueField D)) := by
    intro b
    obtain ⟨a,ha⟩ := hres b
    refine ⟨residue A a,?_⟩
    rw [ResidueField.algebraMap_residue]
    exact ha
  let : FaithfulSMul A D := (faithfulSMul_iff_algebraMap_injective A D).mpr hf
  let K := FractionRing A
  let L := FractionRing D
  let : Algebra K L := FractionRing.liftAlgebra A L
  let : IsScalarTower A K L := FractionRing.isScalarTower_liftAlgebra A L
  let : FiniteDimensional K L := Module.Finite.of_isLocalization A D A⁰
  exact Lech.SeparableOrder.frobenius_homology_tendsto_zero h k D p K L hf hres' hdim F hF i hi
end Lech.CharP

end

end OAI
