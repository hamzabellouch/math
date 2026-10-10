import Mathlib
import OAI.RingTheory.Multiplicity.PerfectionAcyclicity
import OAI.RingTheory.Multiplicity.ScalarQuotientTransport

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ENNReal
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
lemma restrictScalars_complex_smul (f : R →+* S)
    {F G : CochainComplex (ModuleCat.{u} S) ℤ} (a : R) (v : F ⟶ G) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex _).map (f a • v) =
      a • ((ModuleCat.restrictScalars f).mapHomologicalComplex _).map v := rfl
end Lech
namespace Lech.PerfectDomainStages
open Lech.RootTower
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
local instance rootStageQuotientPowerSeriesIsDomain : IsDomain (MvPowerSeries (Fin h) k) :=
  NoZeroDivisors.to_isDomain _

def rootStageFunctor (n : ℕ) :
    CochainComplex (ModuleCat.{u} D) ℤ ⥤
      CochainComplex (ModuleCat.{u} (PerfectClosure (MvPowerSeries (Fin h) k) p)) ℤ :=
  ((ModuleCat.extendScalars (rootToStage (MvPowerSeries (Fin h) k) D p n)).mapHomologicalComplex _) ⋙
    ((ModuleCat.restrictScalars (algebraMap (PerfectClosure (MvPowerSeries (Fin h) k) p)
      (stage (MvPowerSeries (Fin h) k) D p n))).mapHomologicalComplex _)

instance rootStageFunctor_preservesFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (rootStageFunctor h k D p n) := by
  unfold rootStageFunctor
  infer_instance
instance rootStageFunctor_preservesZero (n : ℕ) :
    (rootStageFunctor h k D p n).PreservesZeroMorphisms := by
  unfold rootStageFunctor
  infer_instance

def stageRootIso (n : ℕ) (F : CochainComplex (ModuleCat.{u} D) ℤ) :
    stageComplex h k D p n F ≅ (rootStageFunctor h k D p n).obj (frobeniusComplex D p n F) :=
  ((ModuleCat.restrictScalars (algebraMap (PerfectClosure (MvPowerSeries (Fin h) k) p)
    (stage (MvPowerSeries (Fin h) k) D p n))).mapHomologicalComplex _).mapIso
      (stageFrobeniusIso (MvPowerSeries (Fin h) k) D p n F)

omit [IsLocalRing D] [IsNoetherianRing D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D] [PerfectRing k p] in
lemma rootStage_scalar (n : ℕ) (a : MvPowerSeries (Fin h) k)
    (F : CochainComplex (ModuleCat.{u} D) ℤ) :
    (rootStageFunctor h k D p n).map (algebraMap (MvPowerSeries (Fin h) k) D a • 𝟙 F) =
      rootMap (MvPowerSeries (Fin h) k) p n a • 𝟙 ((rootStageFunctor h k D p n).obj F) := by
  dsimp only [rootStageFunctor,CategoryTheory.Functor.comp_map,CategoryTheory.Functor.comp_obj]
  rw [extendScalars_complex_smul,CategoryTheory.Functor.map_id,rootToStage_scalar,
    restrictScalars_complex_smul,CategoryTheory.Functor.map_id]
  rfl

omit [IsLocalRing D] [IsNoetherianRing D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D] [PerfectRing k p] in
lemma rootStage_scalar_injective (n : ℕ) (a : MvPowerSeries (Fin h) k)
    (ha : algebraMap (MvPowerSeries (Fin h) k) D a ≠ 0)
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hf : ∀ j,Module.Free D (F.X j)) :
    ∀ j,Function.Injective (fun x : ((rootStageFunctor h k D p n).obj F).X j =>
      rootMap (MvPowerSeries (Fin h) k) p n a • x) := by
  intro j
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let B := stage A D p n
  let f := rootToStage A D p n
  let M := (ModuleCat.extendScalars f).obj (F.X j)
  have := hf j
  have : Module.Free B M := free_extendScalars f (F.X j)
  have hn : f (algebraMap A D a) ≠ 0 := by
    intro hz
    apply ha
    apply rootMap_injective D p n
    have hh := congrArg (fun b : B => (b : PerfectClosure D p)) hz
    change rootMap D p n (algebraMap A D a) = 0 at hh
    simpa only [map_zero] using hh
  have hi := free_scalar_injective M (f (algebraMap A D a)) hn
  rw [rootToStage_scalar] at hi
  exact hi

lemma normalizedLength_root_homology
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D))) (F : CochainComplex (ModuleCat.{u} D) ℤ)
    (hfin : ∀ j,Module.Finite D (F.X j)) (n : ℕ)
    (hi : Function.Injective (tensorMap (MvPowerSeries (Fin h) k) D p n)) (i : ℤ) :
    normalizedLength (Fin h) k p (((rootStageFunctor h k D p n).obj F).homology i) =
      ((p : ℝ≥0∞)^(n*h))⁻¹ * (Module.length D (F.homology i)).toENNReal := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let B := stage A D p n
  let g := rootToStage A D p n
  let U := ModuleCat.restrictScalars (algebraMap P B)
  have := hfin i
  have := finite_cochain_homology F i
  let e := (restrictionHomologyIso (algebraMap P B)
      (((ModuleCat.extendScalars g).mapHomologicalComplex _).obj F) i) ≪≫
    U.mapIso (flatExtensionHomologyIso g
      (rootToStage_flat A D p (perfectClosure_flat (Fin h) k p) n hi) F i)
  apply ((regularTower (Fin h) k p).length_eq_of_equiv e.toLinearEquiv).trans
  let : Algebra D B := g.toAlgebra
  let ee : U.obj ((ModuleCat.extendScalars g).obj (F.homology i)) ≃ₗ[P]
      B ⊗[D] (F.homology i) :=
    { __ := AddEquiv.refl _
      map_smul' r x := by
        change B ⊗[D] (F.homology i) at x
        change (algebraMap P B r) • x = r • x
        exact IsScalarTower.algebraMap_smul B r x }
  apply ((regularTower (Fin h) k p).length_eq_of_equiv ee).trans
  simpa only [Fintype.card_fin,normalizedLength,A,B,g] using
    normalizedLength_root_stage_tensor (Fin h) k D p hres (F.homology i) n hi

lemma normalizedLength_stage_scalar_quotient_homology
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D))) (F : CochainComplex (ModuleCat.{u} D) ℤ)
    (hf : ∀ j,Module.Free D (F.X j)) (hfin : ∀ j,Module.Finite D (F.X j))
    (n : ℕ) (hi : Function.Injective (tensorMap (MvPowerSeries (Fin h) k) D p n))
    (a : MvPowerSeries (Fin h) k) (ha : algebraMap (MvPowerSeries (Fin h) k) D a ≠ 0) (i : ℤ) :
    normalizedLength (Fin h) k p
      (((complexQuotient (Ideal.span {rootMap (MvPowerSeries (Fin h) k) p n a}) (.up ℤ)).obj
        (stageComplex h k D p n F)).homology i) =
      ((p : ℝ≥0∞)^(n*h))⁻¹ * (Module.length D
        (((complexQuotient (Ideal.span {algebraMap (MvPowerSeries (Fin h) k) D a}) (.up ℤ)).obj
          (frobeniusComplex D p n F)).homology i)).toENNReal := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let G := frobeniusComplex D p n F
  let E := rootStageFunctor h k D p n
  have hf' (j : ℤ) : Module.Free D (G.X j) := by
    have := hf j
    exact free_extendScalars (iterateFrobenius D p n) (F.X j)
  have hfin' (j : ℤ) : Module.Finite D (G.X j) := by
    have := hfin j
    exact finite_extendScalars (iterateFrobenius D p n) (F.X j)
  let e := ((complexQuotient (Ideal.span {rootMap A p n a}) (.up ℤ)).mapIso
      (stageRootIso h k D p n F)) ≪≫
    (scalarQuotientTransport E G (algebraMap A D a) (rootMap A p n a)
      (rootStage_scalar h k D p n a G)
      (fun j => by have := hf' j; exact free_scalar_injective (G.X j) _ ha)
      (rootStage_scalar_injective h k D p n a ha G hf')).symm
  apply ((regularTower (Fin h) k p).length_eq_of_equiv (homologyMapIso e i).toLinearEquiv).trans
  apply normalizedLength_root_homology h k D p hres _ _ n hi i
  intro j
  have := hfin' j
  exact Koszul.finite_moduleQuotient (Ideal.span {algebraMap A D a}) (G.X j)
end Lech.PerfectDomainStages

end

end OAI
