import Mathlib
import OAI.RingTheory.Multiplicity.ScalarCechComparison
import OAI.RingTheory.Multiplicity.ScalarCechShift
import OAI.RingTheory.Multiplicity.TensorCechEuler
import OAI.RingTheory.Multiplicity.TensorCechHomotopy
import OAI.RingTheory.Multiplicity.TorsionAcyclicity
import OAI.RingTheory.Multiplicity.TorsionScalarComparison

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex FiniteModuleCech MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)

 
def scalarCechHomotopy : HomotopyEquiv (FilteredCech.shiftedPositive I z hz 0)
    (positiveZ (scalarCechDiagram I z hz)) :=
  (HomotopyEquiv.ofIso (FilteredCech.shiftOrdinaryIso I z hz 0)).trans
    ((CechNormalization.extendEquivalence (CechNormalization.homotopyEquiv
      (FilteredCech.diagram I z hz 0))).trans
      (HomotopyEquiv.ofIso ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso
        (scalarCechIso I z hz).symm)))

variable (F : CochainComplex (ModuleCat.{u} R) ℤ)
 
def scalarHomologyIso (i : ℤ) :
    (tensorCech F (scalarCechDiagram I z hz)).homology i ≅
      (((TensorTotal.Right.functor F).obj (FilteredCech.positive I z hz 0)).homology (i+1)) :=
  ((CechNormalization.tensorEquivalence F (scalarCechHomotopy I z hz)).toHomologyIso i).symm ≪≫
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
      (CochainComplex.mapBifunctorShift₂Iso F (FilteredCech.positive I z hz 0)
        (curriedTensor (ModuleCat.{u} R)) 1) ≪≫
    (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} R) 1 i (i+1) (by omega)).app _

variable [Nontrivial R] (hgen : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun j => z j^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (hK : ∀ a : ℕ,1≤a → ∀ i : ℤ,i<0 →
    ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
  (hf : ∀ p,Module.Free R (F.X p)) (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(n+1:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)

include hgen hds hmu ha hK hf hfin hb hac in
theorem scalarHomology_value (i : ℤ) :
    ell.value ((tensorCech F (scalarCechDiagram I z hz)).homology i)=ell.value (F.homology i) := by
  have hp : ∀ p,Module.Projective R (F.X p) := fun p => by have := hf p; infer_instance
  have ht : powerTorsion I (((TensorTotal.Right.functor F).obj
      (FilteredCech.positive I z hz 0)).homology (i+1)) :=
    FilteredCech.positive_homology_powerTorsion I z hz F (-(n+1:ℤ)) 0 hp hfin hb hac 0 (i+1)
  have he := ell.eq_of_iso (scalarHomologyIso I z hz F i)
    ((powerTorsion I).prop_of_iso (scalarHomologyIso I z hz F i).symm ht) ht
  refine he.trans ?_
  symm
  exact SourceGraded.cech_homology_value_torsion I z hgen ell F hds (by omega) hmu ha hK hf hfin
    (-(n+1:ℤ)) (n+2) (by intro p hp; apply hb; omega) hac i

include hgen hds hmu ha hK hf hfin hb hac in
 
theorem scalarEuler_value :
    tensorEuler ell F (n+1) (scalarCechDiagram I z hz)=ell.realValue (F.homology 0) := by
  have H := SourceGraded.acyclicity_finite_torsion I z hgen ell F hmu ha hK hf hfin
    (by simpa only [Nat.cast_add,Nat.cast_one] using hb) hac
  have hp : ∀ p,Module.Projective R (F.X p) := fun p => by have := hf p; infer_instance
  have ht (i : ℤ) : powerTorsion I ((tensorCech F (scalarCechDiagram I z hz)).homology i) :=
    (powerTorsion I).prop_of_iso (scalarHomologyIso I z hz F i).symm
      (FilteredCech.positive_homology_powerTorsion I z hz F (-(n+1:ℤ)) 0 hp hfin hb hac 0 (i+1))
  have he := finiteHomologyEuler_pure_zero ell (tensorCech F (scalarCechDiagram I z hz))
    (fun i hi => ⟨ht i, by rw [scalarHomology_value I z hz F hgen ell hds hmu ha hK hf hfin hb hac]; exact H.2 i hi⟩)
    (n+1) (n+1+Fintype.card (Fin (n+1))) (by omega)
  change tensorEuler ell F (n+1) (scalarCechDiagram I z hz)=_ at he
  rw [he]
  exact congrArg ENNReal.toReal (scalarHomology_value I z hz F hgen ell hds hmu ha hK hf hfin hb hac 0)
end Lech.ReesRoot

end

end OAI
