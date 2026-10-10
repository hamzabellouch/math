import Mathlib
import OAI.RingTheory.Multiplicity.ReesRootCech
import OAI.RingTheory.Multiplicity.RootProjectiveEuler

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
private local instance concreteRing (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
private local instance baseAlgebra (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
private local instance sectionChartModule (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module (Ring I z hz s) (Sections I z hz s hs m) := inferInstance

private local instance baseModule (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
private local instance projectiveModule (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
private local instance scalarComm (s : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n s) R (Ring I z hz s) where
  smul_comm a r b := by
    simp only [Algebra.smul_def]
    exact mul_left_comm _ _ _
private local instance sectionGroup (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    AddCommGroup (Sections I z hz s hs m) := TensorProduct.addCommGroup
private local instance sectionModule (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule

 

def coordinateMul (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) (b : Bool) :
    Sections I z hz s hs m →ₗ[Ring I z hz s] Sections I z hz s hs (Pi.single i 1+m) :=
  (ProjectiveRoot.coordinateMul R n s hs m i b).baseChange (Ring I z hz s)

def eulerLeft (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) :
    Sections I z hz s hs m →ₗ[Ring I z hz s]
      Sections I z hz s hs (Pi.single i 1+m) × Sections I z hz s hs (Pi.single i 1+m) :=
  (coordinateMul I z hz s hs m i false).prod (-coordinateMul I z hz s hs m i true)
def eulerRight (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) :
    Sections I z hz s hs (Pi.single i 1+m) × Sections I z hz s hs (Pi.single i 1+m) →ₗ[Ring I z hz s]
      Sections I z hz s hs (Pi.single i 1+(Pi.single i 1+m)) :=
  (coordinateMul I z hz s hs (Pi.single i 1+m) i true).coprod
    (coordinateMul I z hz s hs (Pi.single i 1+m) i false)

lemma eulerLeft_baseChange (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) :
    (TensorProduct.prodRight (ProjectiveRoot.Ring R n s) (Ring I z hz s) (Ring I z hz s)
      (ProjectiveRoot.Sections R n s hs (Pi.single i 1+m))
      (ProjectiveRoot.Sections R n s hs (Pi.single i 1+m))).toLinearMap.comp
        ((ProjectiveRoot.eulerLeft R n s hs m i).baseChange (Ring I z hz s))=
      (eulerLeft I z hz s hs m i).comp (LinearEquiv.refl (Ring I z hz s) _).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      apply Prod.ext
      · rfl
      · change a ⊗ₜ[ProjectiveRoot.Ring R n s] (-ProjectiveRoot.coordinateMul R n s hs m i true x)=
          -(a ⊗ₜ[ProjectiveRoot.Ring R n s] (ProjectiveRoot.coordinateMul R n s hs m i true x))
        exact TensorProduct.tmul_neg _ _
  | add x y hx hy => simp only [map_add,hx,hy]

lemma eulerRight_baseChange (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) :
    (LinearEquiv.refl (Ring I z hz s) _).toLinearMap.comp
      ((ProjectiveRoot.eulerRight R n s hs m i).baseChange (Ring I z hz s))=
        (eulerRight I z hz s hs m i).comp
          (TensorProduct.prodRight (ProjectiveRoot.Ring R n s) (Ring I z hz s) (Ring I z hz s)
            (ProjectiveRoot.Sections R n s hs (Pi.single i 1+m))
            (ProjectiveRoot.Sections R n s hs (Pi.single i 1+m))).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      change a ⊗ₜ[ProjectiveRoot.Ring R n s]
        (ProjectiveRoot.coordinateMul R n s hs _ i true x.1+ProjectiveRoot.coordinateMul R n s hs _ i false x.2)=_
      rw [TensorProduct.tmul_add]
      rfl
  | add x y hx hy => simp only [map_add,hx,hy]

private lemma euler_baseChange_shortExact (s : Finset (Fin (n+1))) (hs : s.Nonempty)
    (m : Fin n → ℤ) (i : Fin n) :
    Function.Injective ((ProjectiveRoot.eulerLeft R n s hs m i).baseChange (Ring I z hz s)) ∧
      Function.Exact ((ProjectiveRoot.eulerLeft R n s hs m i).baseChange (Ring I z hz s))
        ((ProjectiveRoot.eulerRight R n s hs m i).baseChange (Ring I z hz s)) ∧
      Function.Surjective ((ProjectiveRoot.eulerRight R n s hs m i).baseChange (Ring I z hz s)) := by
  let := (ProjectiveRoot.sections_properties R n hs (Pi.single i 1+(Pi.single i 1+m))).2.1
  obtain ⟨hi, he, hq⟩ := ProjectiveRoot.euler_shortExact R n s hs m i
  exact ModuleSequence.baseChange (Ring I z hz s)
    (ProjectiveRoot.eulerLeft R n s hs m i) (ProjectiveRoot.eulerRight R n s hs m i) hi he hq

lemma euler_shortExact (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) :
    Function.Injective (eulerLeft I z hz s hs m i) ∧
      Function.Exact (eulerLeft I z hz s hs m i) (eulerRight I z hz s hs m i) ∧
        Function.Surjective (eulerRight I z hz s hs m i) := by
  obtain ⟨hi, he, hq⟩ := euler_baseChange_shortExact I z hz s hs m i
  apply ModuleSequence.transport
    (A := Ring I z hz s)
    (M := Ring I z hz s ⊗[ProjectiveRoot.Ring R n s] ProjectiveRoot.Sections R n s hs m)
    (N := Ring I z hz s ⊗[ProjectiveRoot.Ring R n s]
      (ProjectiveRoot.Sections R n s hs (Pi.single i 1+m) × ProjectiveRoot.Sections R n s hs (Pi.single i 1+m)))
    (P := Ring I z hz s ⊗[ProjectiveRoot.Ring R n s]
      ProjectiveRoot.Sections R n s hs (Pi.single i 1+(Pi.single i 1+m)))
    ((ProjectiveRoot.eulerLeft R n s hs m i).baseChange (Ring I z hz s))
    ((ProjectiveRoot.eulerRight R n s hs m i).baseChange (Ring I z hz s))
    (eulerLeft I z hz s hs m i) (eulerRight I z hz s hs m i)
    (LinearEquiv.refl _ _) (TensorProduct.prodRight _ (Ring I z hz s) (Ring I z hz s) _ _)
    (LinearEquiv.refl _ _)
  · exact eulerLeft_baseChange I z hz s hs m i
  · exact eulerRight_baseChange I z hz s hs m i
  · exact hi
  · exact he
  · exact hq

lemma coordinateMul_natural {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ⊆ t) (m : Fin n → ℤ) (i : Fin n) (b : Bool) (x : Sections I z hz s hs m) :
    sectionsRestriction I z hz hs ht (Pi.single i 1+m) hst (coordinateMul I z hz s hs m i b x)=
      coordinateMul I z hz t ht m i b (sectionsRestriction I z hz hs ht m hst x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      change sectionsRestriction I z hz hs ht _ hst
        (a ⊗ₜ[ProjectiveRoot.Ring R n s] ProjectiveRoot.coordinateMul R n s hs m i b x)=_
      rw [sectionsRestriction_tmul,ProjectiveRoot.coordinateMul_natural,sectionsRestriction_tmul]
      rfl
  | add x y hx hy => simp only [map_add,hx,hy]

def coordinateCechHom (m : Fin n → ℤ) (i : Fin n) (b : Bool) (s : Finset (Fin (n+1))) :
    cechObj I z hz m s ⟶ cechObj I z hz (Pi.single i 1+m) s :=
  ModuleCat.ofHom {
    toFun x hs := coordinateMul I z hz s hs.down m i b (x hs)
    map_add' x y := by funext hs; exact map_add _ _ _
    map_smul' r x := by
      funext hs
      exact map_smul ((coordinateMul I z hz s hs.down m i b).restrictScalars R) r (x hs) }

lemma coordinateCechHom_natural (m : Fin n → ℤ) (i : Fin n) (b : Bool)
    {s t : Finset (Fin (n+1))} (hst : s ⊆ t) (x : cechObj I z hz m s) :
    (coordinateCechHom I z hz m i b t).hom ((cechRes I z hz m hst).hom x)=
      (cechRes I z hz (Pi.single i 1+m) hst).hom ((coordinateCechHom I z hz m i b s).hom x) := by
  classical
  funext ht
  by_cases hs : s.Nonempty
  · change coordinateMul I z hz t ht.down m i b ((cechRes I z hz m hst).hom x ht)=_
    rw [cechRes_apply I z hz m hst hs ht.down]
    change _=(cechRes I z hz (Pi.single i 1+m) hst).hom
      (fun hs => coordinateMul I z hz s hs.down m i b (x hs)) ht
    rw [cechRes_apply I z hz _ hst hs ht.down,coordinateMul_natural]
  · change coordinateMul I z hz t ht.down m i b (if hs : s.Nonempty then _ else 0)=
      if hs : s.Nonempty then _ else 0
    simp only [dite_eq_right hs,map_zero]

 
def coordinateCechMap (m : Fin n → ℤ) (i : Fin n) (b : Bool) :
    FiniteModuleCech.Map (cechDiagram I z hz m) (cechDiagram I z hz (Pi.single i 1+m)) where
  app s := coordinateCechHom I z hz m i b s
  naturality {s t} hst := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact coordinateCechHom_natural I z hz m i b hst
end Lech.ReesRoot

end

end OAI
