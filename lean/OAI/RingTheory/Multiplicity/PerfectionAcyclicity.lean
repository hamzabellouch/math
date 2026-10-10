import Mathlib
import OAI.RingTheory.Multiplicity.FrobeniusComplexStage

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech.SeparableOrder
open Lech.RootTower Lech.PerfectDomainStages Lech.Koszul
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [CharP K p] [CharP L p]
local instance : IsDomain (MvPowerSeries (Fin h) k) := NoZeroDivisors.to_isDomain _

include K L in
lemma normalizedLength_perfection_shortComplex_homology
    (hdim : dimension D = h) (F : CochainComplex (ModuleCat.{u} D) ℤ)
    (hF : IsFiniteHomologyComplex D F) (i : ℤ) (hi : i < 0) :
    normalizedLength (Fin h) k p
      ((ModuleCat.restrictScalars (algebraMap (PerfectClosure (MvPowerSeries (Fin h) k) p)
        (PerfectClosure D p))).obj
        ((((ModuleCat.extendScalars (PerfectClosure.of D p)).mapHomologicalComplex _).obj F).homology i)) = 0 := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let C := PerfectClosure D p
  let E := (ModuleCat.extendScalars (PerfectClosure.of D p)).mapHomologicalComplex (.up ℤ)
  let G := E.obj F
  let T := regularTower (Fin h) k p
  let ell : Lech.TorsionLength (⊥ : Ideal C) := T.torsionLength (algebraMap P C) ⊥
  obtain ⟨a,ha,hn⟩ := shortComplex_uniform_nullhomotopy F hF
  let zsA : List A := List.ofFn fun j : Fin h => (MvPowerSeries.X j : A)^a
  let zsP : List P := (zsA.map (PerfectClosure.of A p)).reverse
  let zsC : List C := zsP.map (algebraMap P C)
  have hzlen : zsC.length = h := by simp [zsC,zsP,zsA]
  have hK (j : ℤ) (hj : j < 0) : ell.zeroClass ((unit zsC).homology j) := by
    refine ⟨⟨1,by simp⟩,?_⟩
    change T.length ((ModuleCat.restrictScalars (algebraMap P C)).obj
      ((tensor (zsP.map (algebraMap P C)) ((single (ModuleCat C) (.up ℤ) 0).obj
        (ModuleCat.of C C))).homology j)) = 0
    rw [T.length_eq_of_equiv
      (restrictScalarsSingleTensorHomologyIso (algebraMap P C) zsP (ModuleCat.of C C) j).toLinearEquiv]
    exact normalizedLength_coordinate_power_koszul h k D p K L a (Nat.ne_of_gt ha) j hj
  have hnull (b : C) (hb : b ∈ zsC) : Nonempty (Homotopy (b • 𝟙 G) 0) := by
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hb
    have hw' : w ∈ zsA.map (PerfectClosure.of A p) := by simpa only [zsP,List.mem_reverse] using hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw'
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hv
    have hm : algebraMap A D (MvPowerSeries.X j) ∈ IsLocalRing.maximalIdeal D :=
      IsLocalRing.map_maximalIdeal_le (algebraMap A D) (Ideal.mem_map_of_mem _ (by
        rw [Lech.PowerSeries.maximalIdeal_eq_variables]
        exact Ideal.subset_span ⟨j,rfl⟩))
    have hnx := hn (Ideal.pow_mem_pow hm a)
    have he : algebraMap P C (PerfectClosure.of A p ((MvPowerSeries.X j : A)^a)) =
        PerfectClosure.of D p ((algebraMap A D (MvPowerSeries.X j))^a) := by
      change perfectMap p (algebraMap A D) (PerfectClosure.of A p _) = _
      rw [perfectMap_of,map_pow]
    rw [he]
    exact ⟨extendScalars_nullhomotopy (PerfectClosure.of D p) F _ hnx.some⟩
  have hh := acyclicity_of_koszul ell.zeroClass zsC G
    (fun j => by have := hF.term_free j; exact free_extendScalars (PerfectClosure.of D p) (F.X j))
    (fun j => by have := hF.term_finite j; exact finite_extendScalars (PerfectClosure.of D p) (F.X j))
    (fun j hj => (ModuleCat.extendScalars (PerfectClosure.of D p)).map_isZero
      (hF.bounded j (by simpa only [hzlen,hdim] using hj))) hnull hK i hi
  exact hh.2
end Lech.SeparableOrder

end

end OAI
