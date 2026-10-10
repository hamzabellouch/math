import Mathlib
import OAI.RingTheory.Multiplicity.FiniteModuleCech
import OAI.RingTheory.Multiplicity.ReesRootBundle

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]

 

def positiveComplex (D : Diagram R ι) : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (cochains D (n+1)))
    (fun n => ModuleCat.ofHom (d D (n+1))) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact d_square D (n+1))
lemma positiveComplex_d (D : Diagram R ι) (n : ℕ) :
    (positiveComplex D).d n (n+1) = ModuleCat.ofHom (d D (n+1)) := by
  unfold positiveComplex
  exact CochainComplex.of_d (fun j => ModuleCat.of R (cochains D (j+1)))
    (fun j => ModuleCat.ofHom (d D (j+1))) n
lemma positiveComplex_bounded (D : Diagram R ι) (n : ℕ) (hn : Fintype.card ι ≤ n) :
    IsZero ((positiveComplex D).X n) := bounded D (n+1) (by omega)

def Map.positiveComplex {D E : Diagram R ι} (φ : Map D E) :
    positiveComplex D ⟶ positiveComplex E :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (φ.cochains (n+1))) (fun n => by
    rw [positiveComplex_d,positiveComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (φ.cochains_d (n+1) f).symm)
end Lech.FiniteModuleCech

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I) (m : Fin n → ℤ)
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
  smul_comm a r b := by
    simp only [Algebra.smul_def]
    exact mul_left_comm _ _ _
private local instance sectionGroup (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    AddCommGroup (Sections I z hz s hs m) := TensorProduct.addCommGroup
private local instance sectionModule (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule

 

abbrev CechSection (s : Finset (Fin (n+1))) :=
  (hs : PLift s.Nonempty) → Sections I z hz s hs.down m

abbrev cechObj (s : Finset (Fin (n+1))) : ModuleCat.{u} R :=
  ModuleCat.of R (CechSection I z hz m s)

def cechRes {s t : Finset (Fin (n+1))} (hst : s ⊆ t) : cechObj I z hz m s ⟶ cechObj I z hz m t :=
  ModuleCat.ofHom {
    toFun x ht := if hs : s.Nonempty then sectionsRestriction I z hz hs ht.down m hst (x ⟨hs⟩) else 0
    map_add' x y := by
      funext ht
      split_ifs <;> simp only [Pi.add_apply,map_add,add_zero]
    map_smul' r x := by
      funext ht
      split_ifs <;> simp only [Pi.smul_apply,map_smul,RingHom.id_apply,smul_zero] }

lemma cechRes_apply {s t : Finset (Fin (n+1))} (hst : s ⊆ t)
    (hs : s.Nonempty) (ht : t.Nonempty) (x : CechSection I z hz m s) :
    (cechRes I z hz m hst).hom x ⟨ht⟩ = sectionsRestriction I z hz hs ht m hst (x ⟨hs⟩) := by
  change (if hs : s.Nonempty then _ else _) = _
  rw [dite_eq_left hs]

lemma cechRes_self (s : Finset (Fin (n+1))) :
    cechRes I z hz m (Finset.Subset.refl s) = 𝟙 (cechObj I z hz m s) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext hs
  exact (cechRes_apply I z hz m _ hs.down hs.down x).trans (sectionsRestriction_self I z hz hs.down m (x hs))

lemma cechRes_comp {s t v : Finset (Fin (n+1))} (hst : s ⊆ t) (htv : t ⊆ v) :
    cechRes I z hz m hst ≫ cechRes I z hz m htv = cechRes I z hz m (hst.trans htv) := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext hv
  obtain ⟨hv⟩ := hv
  by_cases hs : s.Nonempty
  · have ht : t.Nonempty := hs.mono hst
    change (cechRes I z hz m htv).hom ((cechRes I z hz m hst).hom x) ⟨hv⟩ = _
    rw [cechRes_apply I z hz m htv ht hv,cechRes_apply I z hz m hst hs ht,
      cechRes_apply I z hz m (hst.trans htv) hs hv]
    exact sectionsRestriction_comp I z hz hs ht hv m hst htv (x ⟨hs⟩)
  · change (if ht : t.Nonempty then
      sectionsRestriction I z hz ht hv m htv (if hs : s.Nonempty then _ else 0) else 0) =
        if hs : s.Nonempty then _ else 0
    rw [dite_eq_right hs]
    split_ifs <;> simp only [map_zero]

 
def cechDiagram : FiniteModuleCech.Diagram R (Fin (n+1)) where
  obj := cechObj I z hz m
  res := cechRes I z hz m
  res_self := cechRes_self I z hz m
  res_comp := cechRes_comp I z hz m

 
def cech : CochainComplex (ModuleCat.{u} R) ℕ :=
  FiniteModuleCech.positiveComplex (cechDiagram I z hz m)

lemma cech_bounded (q : ℕ) (hq : n < q) : IsZero ((cech I z hz m).X q) := by
  apply FiniteModuleCech.positiveComplex_bounded
  simp only [Fintype.card_fin]
  omega
end Lech.ReesRoot

end

end OAI
