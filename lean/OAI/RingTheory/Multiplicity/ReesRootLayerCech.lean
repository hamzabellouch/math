import Mathlib
import OAI.RingTheory.Multiplicity.CechExact
import OAI.RingTheory.Multiplicity.ReesRootIteration

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
private local instance concreteRing (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
private local instance baseAlgebra (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
private local instance baseModule (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
private local instance projectiveModule (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
private local instance scalarComm (s : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n s) R (Ring I z hz s) where
  smul_comm a r b := by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _
private local instance sectionGroup (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    AddCommGroup (Sections I z hz s hs m) := TensorProduct.addCommGroup
private local instance sectionChartModule (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module (Ring I z hz s) (Sections I z hz s hs m) := TensorProduct.leftModule
private local instance sectionBaseModule (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule

private local instance nonemptyFinite (s : Finset (Fin (n+1))) :
    Fintype (PLift s.Nonempty) := Fintype.ofFinite _
variable (m : Fin n → ℤ)

def layerProjection : FiniteModuleCech.Map (cechDiagram I z hz m)
    (FiniteModuleCech.reduction (cechDiagram I z hz m) I) where
  app s := (TensorIdeal.quotientNat I).app (cechObj I z hz m s)
  naturality hst := (TensorIdeal.quotientNat I).naturality (cechRes I z hz m hst)

variable (hgen : Ideal.span (Set.range z)=I)
include hgen in
lemma layerDiagram_zero (s : Finset (Fin (n+1))) :
    (cechInclusionDiagram I z hz m).app s ≫ (layerProjection I z hz m).app s=0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Submodule.Quotient.mk ((cechInclusionApp I z hz m s).hom x)=0
  rw [Submodule.Quotient.mk_eq_zero]
  apply (TensorIdeal.mem_smul_pi_iff I
    (fun hs : PLift s.Nonempty => Sections I z hz s hs.down m) _).mpr
  intro hs
  change inclusion I z hz s hs.down m (x hs) ∈ _
  rw [←inclusion_range I z hz s hs.down m hgen]
  exact LinearMap.mem_range_self _ _

include hgen in
lemma layerDiagram_shortExact (s : Finset (Fin (n+1))) :
    (FiniteModuleCech.diagramShortComplex (cechInclusionDiagram I z hz m)
      (layerProjection I z hz m) (layerDiagram_zero I z hz m hgen) s).ShortExact where
  mono_f := (ModuleCat.mono_iff_injective _).mpr (by
    intro x y hxy
    funext hs
    exact inclusion_injective I z hz s hs.down m (congrFun hxy hs))
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)
  exact := (ShortComplex.moduleCat_exact_iff _).mpr (by
    intro y hy
    change Submodule.Quotient.mk y=0 at hy
    have hys := (TensorIdeal.mem_smul_pi_iff I
      (fun hs : PLift s.Nonempty => Sections I z hz s hs.down m) y).mp
      ((Submodule.Quotient.mk_eq_zero _).mp hy)
    have hyr (hs : PLift s.Nonempty) : y hs ∈ (inclusion I z hz s hs.down m).range := by
      rw [inclusion_range I z hz s hs.down m hgen]
      exact hys hs
    choose x hx using fun hs : PLift s.Nonempty => hyr hs
    exact ⟨x,funext hx⟩)

def layerShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  FiniteModuleCech.positiveShortComplex (cechInclusionDiagram I z hz m)
    (layerProjection I z hz m) (layerDiagram_zero I z hz m hgen)

lemma layerShortComplex_exact : (layerShortComplex I z hz m hgen).ShortExact :=
  FiniteModuleCech.positive_shortExact _ _ _ (layerDiagram_shortExact I z hz m hgen)

end Lech.ReesRoot

end

end OAI
