import Mathlib
import OAI.RingTheory.Multiplicity.ScalarHomologyError

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ENNReal
namespace Lech.PerfectDomainStages
open Lech.RootTower
universe u
variable (A D : Type u) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Algebra A D] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP D p]

lemma rootToStage_flat (hflat : (PerfectClosure.of A p).Flat) (n : ℕ)
    (hi : Function.Injective (tensorMap A D p n)) : (rootToStage A D p n).Flat := by
  let P := PerfectClosure A p
  let B := stage A D p n
  let : Algebra A P := (rootMap A p n).toAlgebra
  let : Module.Flat A P := rootMap_flat A p hflat n
  let : Algebra D B := (rootToStage A D p n).toAlgebra
  let : Algebra D (P ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  let : Module.Flat D (P ⊗[A] D) := Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.commRight A D P).symm.toLinearEquiv
  let e := tensorEquiv A D p n hi
  let ed : (P ⊗[A] D) ≃ₐ[D] B :=
    { __ := e.toRingEquiv
      commutes' d := tensorEquiv_root A D p n hi d }
  exact Module.Flat.of_linearEquiv ed.symm.toLinearEquiv

def stageFrobeniusIso (n : ℕ) (F : CochainComplex (ModuleCat.{u} D) ℤ) :
    (((ModuleCat.extendScalars (originalToStage A D p n)).mapHomologicalComplex _).obj F) ≅
      (((ModuleCat.extendScalars (rootToStage A D p n)).mapHomologicalComplex _).obj
        (Lech.frobeniusComplex D p n F)) := by
  rw [← rootToStage_original A D p n]
  exact (NatIso.mapHomologicalComplex
    (ModuleCat.extendScalarsComp (iterateFrobenius D p n)
      (rootToStage A D p n)) (.up ℤ)).app F
end Lech.PerfectDomainStages

namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
def restrictionHomologyIso (f : R →+* S)
    (F : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) :
    (((ModuleCat.restrictScalars f).mapHomologicalComplex _).obj F).homology i ≅
      (ModuleCat.restrictScalars f).obj (F.homology i) :=
  (F.sc i).mapHomologyIso (ModuleCat.restrictScalars f)

def flatExtensionHomologyIso (f : R →+* S) (hf : f.Flat)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (((ModuleCat.extendScalars f).mapHomologicalComplex _).obj F).homology i ≅
      (ModuleCat.extendScalars f).obj (F.homology i) := by
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact (F.sc i).mapHomologyIso (ModuleCat.extendScalars f)
end Lech

namespace Lech.PerfectDomainStages
open Lech.RootTower
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
local instance frobeniusComplexStagePowerSeriesIsDomain : IsDomain (MvPowerSeries (Fin h) k) :=
  NoZeroDivisors.to_isDomain _

def stageComplex (n : ℕ) (F : CochainComplex (ModuleCat.{u} D) ℤ) :
    CochainComplex (ModuleCat.{u} (PerfectClosure (MvPowerSeries (Fin h) k) p)) ℤ :=
  ((ModuleCat.restrictScalars (algebraMap (PerfectClosure (MvPowerSeries (Fin h) k) p)
      (stage (MvPowerSeries (Fin h) k) D p n))).mapHomologicalComplex _).obj
    (((ModuleCat.extendScalars (originalToStage (MvPowerSeries (Fin h) k) D p n)).mapHomologicalComplex _).obj F)

lemma normalizedLength_stage_homology
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D)))
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hfin : ∀ j,Module.Finite D (F.X j))
    (n : ℕ) (hi : Function.Injective (tensorMap (MvPowerSeries (Fin h) k) D p n)) (i : ℤ) :
    normalizedLength (Fin h) k p ((stageComplex h k D p n F).homology i) =
      ((p : ℝ≥0∞)^(n*h))⁻¹ *
        (Module.length D ((Lech.frobeniusComplex D p n F).homology i)).toENNReal := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let B := stage A D p n
  let f := originalToStage A D p n
  let g := rootToStage A D p n
  let G := Lech.frobeniusComplex D p n F
  let U := ModuleCat.restrictScalars (algebraMap P B)
  have := hfin i
  have : Module.Finite D (G.X i) := Lech.finite_extendScalars (iterateFrobenius D p n) (F.X i)
  have := Lech.finite_cochain_homology G i
  let e := (Lech.restrictionHomologyIso (algebraMap P B)
      (((ModuleCat.extendScalars f).mapHomologicalComplex _).obj F) i) ≪≫
    U.mapIso (homologyMapIso (stageFrobeniusIso A D p n F) i) ≪≫
    U.mapIso (Lech.flatExtensionHomologyIso g
      (rootToStage_flat A D p (perfectClosure_flat (Fin h) k p) n hi) G i)
  have he := (regularTower (Fin h) k p).length_eq_of_equiv e.toLinearEquiv
  apply he.trans
  let : Algebra D B := g.toAlgebra
  let ee : U.obj ((ModuleCat.extendScalars g).obj (G.homology i)) ≃ₗ[P]
      B ⊗[D] (G.homology i) :=
    { __ := AddEquiv.refl _
      map_smul' r x := by
        change B ⊗[D] (G.homology i) at x
        change (algebraMap P B r) • (x : B ⊗[D] (G.homology i)) =
          r • (x : B ⊗[D] (G.homology i))
        exact IsScalarTower.algebraMap_smul B r (x : B ⊗[D] (G.homology i)) }
  apply ((regularTower (Fin h) k p).length_eq_of_equiv ee).trans
  simpa only [Fintype.card_fin,normalizedLength,A,B,G,g] using
    normalizedLength_root_stage_tensor (Fin h) k D p hres (G.homology i) n hi
end Lech.PerfectDomainStages

end

end OAI
