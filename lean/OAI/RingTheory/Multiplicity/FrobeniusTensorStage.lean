import Mathlib
import OAI.RingTheory.Multiplicity.FrobeniusModule

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
open TensorProduct
namespace Lech.PerfectDomainStages
open Lech.RootTower CategoryTheory
universe u
variable (σ : Type) (k D : Type u) [Fintype σ] [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [Algebra (MvPowerSeries σ k) D] [IsLocalHom (algebraMap (MvPowerSeries σ k) D)]
  [Module.Finite (MvPowerSeries σ k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
local instance : IsDomain (MvPowerSeries σ k) := NoZeroDivisors.to_isDomain _

lemma normalizedLength_root_stage_tensor
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries σ k))
      (IsLocalRing.ResidueField D))) (N : ModuleCat.{u} D) [Module.Finite D N] (n : ℕ)
    (hi : Function.Injective (tensorMap (MvPowerSeries σ k) D p n)) :
    letI : Algebra D (stage (MvPowerSeries σ k) D p n) :=
      (rootToStage (MvPowerSeries σ k) D p n).toAlgebra
    normalizedLength σ k p ((stage (MvPowerSeries σ k) D p n) ⊗[D] N) =
      ((p : ℝ≥0∞)^(n * Fintype.card σ))⁻¹ * (Module.length D N).toENNReal := by
  let A := MvPowerSeries σ k
  let P := PerfectClosure A p
  let B := stage A D p n
  let : Algebra A P := (rootMap A p n).toAlgebra
  let : Algebra D B := (rootToStage A D p n).toAlgebra
  let : Algebra D (P ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  let : Module A N := Module.compHom N (algebraMap A D)
  let : IsScalarTower A D N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module.Finite A N := Module.Finite.trans D N
  let e := tensorEquiv A D p n hi
  let ed : (P ⊗[A] D) ≃ₐ[D] B :=
    { __ := e.toRingEquiv
      commutes' d := tensorEquiv_root A D p n hi d }
  let f : B ⊗[D] N ≃ₗ[P] P ⊗[A] N :=
    (Lech.TensorConductor.congrLeft ed.symm.toLinearEquiv
      (fun r x => e.symm.toLinearEquiv.map_smul r x)).trans (Lech.TensorPushout.equiv A P D N)
  change (regularTower σ k p).length _ = _
  rw [(regularTower σ k p).length_eq_of_equiv f]
  change normalizedLength σ k p (P ⊗[A] N) = _
  rw [normalizedLength_rootBaseChange]
  congr 1
  exact congrArg ENat.toENNReal (length_eq_of_residue_surjective hres N)

lemma normalizedLength_original_stage_tensor
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries σ k))
      (IsLocalRing.ResidueField D))) (M : ModuleCat.{u} D) [Module.Finite D M] (n : ℕ)
    (hi : Function.Injective (tensorMap (MvPowerSeries σ k) D p n)) :
    letI : Algebra D (stage (MvPowerSeries σ k) D p n) :=
      (originalToStage (MvPowerSeries σ k) D p n).toAlgebra
    normalizedLength σ k p ((stage (MvPowerSeries σ k) D p n) ⊗[D] M) =
      ((p : ℝ≥0∞)^(n * Fintype.card σ))⁻¹ *
        (Module.length D (Lech.FrobeniusModule D p n M)).toENNReal := by
  let A := MvPowerSeries σ k
  let P := PerfectClosure A p
  let B := stage A D p n
  let f := originalToStage A D p n
  let g := rootToStage A D p n
  let N := Lech.FrobeniusModule D p n M
  let X := (ModuleCat.extendScalars f).obj M
  let Y := (ModuleCat.extendScalars g).obj N
  let : Algebra D B := f.toAlgebra
  let : Module P X := by
    change Module P (B ⊗[D] M)
    infer_instance
  let : Module P Y := by
    letI : Algebra D B := g.toAlgebra
    change Module P (B ⊗[D] N)
    infer_instance
  let : IsScalarTower P B X := by
    change IsScalarTower P B (B ⊗[D] M)
    infer_instance
  let : IsScalarTower P B Y := by
    let : Algebra D B := g.toAlgebra
    change IsScalarTower P B (B ⊗[D] N)
    infer_instance
  have e : X ≅ Y := by
    dsimp only [X,Y,N,Lech.FrobeniusModule,f,g]
    rw [← rootToStage_original A D p n]
    exact (ModuleCat.extendScalarsComp (iterateFrobenius D p n)
      (rootToStage A D p n)).app M
  have he := (regularTower σ k p).length_eq_of_equiv
    (e.toLinearEquiv.restrictScalars P)
  change (regularTower σ k p).length X = _
  rw [he]
  exact normalizedLength_root_stage_tensor σ k D p hres N n hi
end Lech.PerfectDomainStages

end

end OAI
