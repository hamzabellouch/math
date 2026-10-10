import Mathlib
import OAI.RingTheory.Multiplicity.RootUlrichNaturality

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]
  {D E : Diagram R ι}

def positiveIso (e : ∀ s,D.obj s ≃ₗ[R] E.obj s)
    (he : ∀ {s t : Finset ι} (hst : s ⊆ t) (x : D.obj s),
      e t ((D.res hst).hom x)=(E.res hst).hom (e s x)) :
    positiveComplex D ≅ positiveComplex E :=
  HomologicalComplex.Hom.isoOfComponents (fun q =>
    (LinearEquiv.piCongrRight (fun s : Set.powersetCard ι (q+1) => e s.val)).toModuleIso) (by
      intro q r h
      obtain rfl : q+1=r := h
      rw [positiveComplex_d,positiveComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext s
      symm
      change e s.val (∑ i : Fin (q+2),(-1:ℤ)^i.val •
        (D.res (AlternatingCech.delete_subset s i)).hom (x (AlternatingCech.delete s i))) = _
      rw [map_sum]
      simp only [map_zsmul]
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun y => (-1:ℤ)^i.val • y) (he (AlternatingCech.delete_subset s i) _))
end Lech.FiniteModuleCech

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits UniversalSplitting
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
private local instance concreteRing (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
private local instance baseAlgebra (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) := inferInstance
private local instance baseModule (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) := inferInstance

abbrev ScalarCechSection (s : Finset (Fin (n+1))) := (hs : PLift s.Nonempty) → Ring I z hz s
abbrev scalarCechObj (s : Finset (Fin (n+1))) : ModuleCat.{u} R := ModuleCat.of R (ScalarCechSection I z hz s)

def scalarCechRes {s t : Finset (Fin (n+1))} (hst : s ⊆ t) :
    scalarCechObj I z hz s ⟶ scalarCechObj I z hz t :=
  ModuleCat.ofHom {
    toFun x ht := if hs : s.Nonempty then restrictionAlg I z hz hst (x ⟨hs⟩) else 0
    map_add' x y := by
      funext ht
      split_ifs with hs
      · exact (restrictionAlg I z hz hst).toRingHom.map_add (x ⟨hs⟩) (y ⟨hs⟩)
      · exact (add_zero 0).symm
    map_smul' r x := by
      funext ht
      split_ifs with hs
      · exact (restrictionAlg I z hz hst).toLinearMap.map_smul r (x ⟨hs⟩)
      · exact (smul_zero r).symm }

lemma scalarCechRes_apply {s t : Finset (Fin (n+1))} (hst : s ⊆ t)
    (hs : s.Nonempty) (ht : t.Nonempty) (x : ScalarCechSection I z hz s) :
    (scalarCechRes I z hz hst).hom x ⟨ht⟩=restriction I z hz hst (x ⟨hs⟩) := by
  change (if hs : s.Nonempty then _ else _)=_
  rw [dite_eq_left hs]
  rfl

def scalarCechDiagram : FiniteModuleCech.Diagram R (Fin (n+1)) where
  obj := scalarCechObj I z hz
  res := scalarCechRes I z hz
  res_self s := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext hs
    rw [scalarCechRes_apply I z hz _ hs.down hs.down,restriction_self]
    rfl
  res_comp {s t v} hst htv := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext hv
    obtain ⟨hv⟩ := hv
    by_cases hs : s.Nonempty
    · have ht := hs.mono hst
      change (scalarCechRes I z hz htv).hom ((scalarCechRes I z hz hst).hom x) ⟨hv⟩=_
      rw [scalarCechRes_apply I z hz htv ht hv,scalarCechRes_apply I z hz hst hs ht,
        scalarCechRes_apply I z hz (hst.trans htv) hs hv,restriction_comp]
    · change (if ht : t.Nonempty then restrictionAlg I z hz htv
          (if hs : s.Nonempty then _ else 0) else 0)=if hs : s.Nonempty then _ else 0
      rw [dite_eq_right hs]
      split_ifs
      · exact (restrictionAlg I z hz htv).toRingHom.map_zero
      · rfl

 
def powerScalarDiagram : FiniteModuleCech.Diagram R (Fin (n+1)) where
  obj s := ModuleCat.of R (PowerIndex n → ScalarCechSection I z hz s)
  res hst := ModuleCat.ofHom {
    toFun x e := (scalarCechRes I z hz hst).hom (x e)
    map_add' _ _ := by funext e; exact map_add _ _ _
    map_smul' r x := by
      funext e
      change (scalarCechRes I z hz hst).hom (r • x e)=r • (scalarCechRes I z hz hst).hom (x e)
      exact (scalarCechRes I z hz hst).hom.map_smul r (x e) }
  res_self s := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext e
    change (scalarCechRes I z hz (Finset.Subset.refl s)).hom (x e)=x e
    funext hs
    rw [scalarCechRes_apply I z hz _ hs.down hs.down,restriction_self]
  res_comp {s t v} hst htv := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext e
    have he : scalarCechRes I z hz hst ≫ scalarCechRes I z hz htv =
        scalarCechRes I z hz (hst.trans htv) := (scalarCechDiagram I z hz).res_comp hst htv
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom he) (x e)

 

def ulrichCechEquiv (s : Finset (Fin (n+1))) :
    cechObj I z hz (fun i => (powerWeight n i:ℤ)) s ≃ₗ[R] (powerScalarDiagram I z hz).obj s where
  toFun x e hs := (powerSectionBasis I z hz s hs.down).equivFun (x hs) e
  invFun x hs := (powerSectionBasis I z hz s hs.down).equivFun.symm (fun e => x e hs)
  left_inv x := by funext hs; exact LinearEquiv.symm_apply_apply _ _
  right_inv x := by funext e hs; exact congrFun (LinearEquiv.apply_symm_apply
      (powerSectionBasis I z hz s hs.down).equivFun (fun e => x e hs)) e
  map_add' x y := by funext e hs; exact congrFun (map_add (powerSectionBasis I z hz s hs.down).equivFun _ _) e
  map_smul' r x := by
    funext e hs
    exact congrFun (map_smul ((powerSectionBasis I z hz s hs.down).equivFun.restrictScalars R) r (x hs)) e

lemma ulrichCechEquiv_natural {s t : Finset (Fin (n+1))} (hst : s ⊆ t)
    (x : cechObj I z hz (fun i => (powerWeight n i:ℤ)) s) :
    ulrichCechEquiv I z hz t ((cechRes I z hz _ hst).hom x)=
      ((powerScalarDiagram I z hz).res hst).hom (ulrichCechEquiv I z hz s x) := by
  classical
  funext e ht
  by_cases hs : s.Nonempty
  · change (powerSectionBasis I z hz t ht.down).equivFun ((cechRes I z hz _ hst).hom x ht) e=
      (scalarCechRes I z hz hst).hom (fun hs => (powerSectionBasis I z hz s hs.down).equivFun (x hs) e) ht
    rw [scalarCechRes_apply I z hz hst hs ht.down,cechRes_apply I z hz _ hst hs ht.down,
      powerSectionCoordinates_natural]
  · change (powerSectionBasis I z hz t ht.down).equivFun
      (if hs : s.Nonempty then _ else 0) e=if hs : s.Nonempty then _ else 0
    rw [dite_eq_right hs]
    simp only [map_zero,Pi.zero_apply,dite_eq_right hs]

def ulrichCechIso :
    FiniteModuleCech.positiveComplex (cechDiagram I z hz (fun i => (powerWeight n i:ℤ))) ≅
      FiniteModuleCech.positiveComplex (powerScalarDiagram I z hz) :=
  FiniteModuleCech.positiveIso (ulrichCechEquiv I z hz) (fun _ => ulrichCechEquiv_natural I z hz _)
end Lech.ReesRoot

end

end OAI
