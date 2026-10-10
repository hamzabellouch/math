import Mathlib
import OAI.RingTheory.Multiplicity.CechCarrierOperators
import OAI.RingTheory.Multiplicity.ReesRootCech

namespace OAI

noncomputable section
namespace Lech.CechNormalization
open CategoryTheory CategoryTheory.Limits HomologicalComplex Set CarrierOperators
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]
  (D : FiniteModuleCech.Diagram R ι)

abbrev fullCochains (p : ℕ) := Sections D (fullCarrier p)
abbrev fullD (p : ℕ) := lift D (deltaOp p)
abbrev fullSort (p : ℕ) := lift D (sortOp p)
abbrev fullExpand (p : ℕ) := lift D (expandOp p)
abbrev fullH (p : ℕ) := lift D (contractionOp p)
abbrev fullN (p : ℕ) := lift D (normalizeOp p)

omit [Fintype ι] in
lemma fullD_square (p : ℕ) (f : fullCochains D p) : fullD D (p+1) (fullD D p f)=0 := by
  change ((lift D (deltaOp (p+1))).comp (lift D (deltaOp p))) f=0
  rw [←lift_comp]
  funext a
  exact congrFun (FiniteCoverCech.delta_square R (D.obj (FiniteCoverCech.intersection a)) p
    (toFixed D (fullCarrier p) (FiniteCoverCech.intersection a) f)) a

omit [Fintype ι] in
lemma sortedD_eq (p : ℕ) : lift D (sortedDeltaOp p)=FiniteModuleCech.d D p := by
  apply LinearMap.ext
  intro f
  funext s
  change (∑ i : Fin (p+1),(-1:ℤ)^i.val •
      toFixed D (sortedCarrier p) s.val f (AlternatingCech.delete s i))=_
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  change (if h : (AlternatingCech.delete s i).val⊆s.val then _ else _)=_
  rw [dite_eq_left (AlternatingCech.delete_subset s i)]

omit [Fintype ι] in
lemma fullSort_d (p : ℕ) :
    (fullSort D (p+1)).comp (fullD D p)=(FiniteModuleCech.d D p).comp (fullSort D p) := by
  rw [←sortedD_eq]
  exact (by
    rw [←lift_comp,←lift_comp]
    exact lift_congr D (fun M => sort_delta M p))

lemma fullExpand_d (p : ℕ) :
    (fullExpand D (p+1)).comp (FiniteModuleCech.d D p)=(fullD D p).comp (fullExpand D p) := by
  rw [←sortedD_eq]
  rw [←lift_comp,←lift_comp]
  exact lift_congr D (fun M => expand_delta M p)

lemma fullSort_expand (p : ℕ) : (fullSort D p).comp (fullExpand D p)=LinearMap.id := by
  rw [←lift_id D (sortedCarrier p)]
  rw [←lift_comp]
  exact lift_congr D (fun M => sort_expand M p)

lemma fullExpand_sort (p : ℕ) : (fullExpand D p).comp (fullSort D p)=fullN D p := by
  rw [←lift_comp]
  exact lift_congr D (fun M => expand_sort M p)

lemma fullH_zero : fullH D 0=0 := by
  apply LinearMap.ext
  intro f
  funext a
  rfl

lemma fullH_identity (p : ℕ) :
    (fullH D (p+1)).comp (fullD D (p+1))+(fullD D p).comp (fullH D p)=
      LinearMap.id-fullN D (p+1) := by
  change (lift D (contractionOp (p+1))).comp (lift D (deltaOp (p+1)))+
    (lift D (deltaOp p)).comp (lift D (contractionOp p))=LinearMap.id-lift D (normalizeOp (p+1))
  rw [←lift_comp,←lift_comp,←lift_add,←lift_id D (fullCarrier (p+1)),←lift_sub]
  apply lift_congr D
  intro M
  apply LinearMap.ext
  exact contraction_identity R M p

 
def fullPositive : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of R (fullCochains D (p+1)))
    (fun p => ModuleCat.ofHom (fullD D (p+1))) (fun p => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact fullD_square D (p+1))

omit [Fintype ι] in
lemma fullPositive_d (p : ℕ) : (fullPositive D).d p (p+1)=ModuleCat.ofHom (fullD D (p+1)) := by
  unfold fullPositive
  exact CochainComplex.of_d (fun q => ModuleCat.of R (fullCochains D (q+1)))
    (fun q => ModuleCat.ofHom (fullD D (q+1))) p

def sortMap : fullPositive D ⟶ FiniteModuleCech.positiveComplex D :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom (fullSort D (p+1))) (fun p => by
    rw [fullPositive_d,FiniteModuleCech.positiveComplex_d]
    apply ModuleCat.hom_ext
    exact (fullSort_d D (p+1)).symm)

def expandMap : FiniteModuleCech.positiveComplex D ⟶ fullPositive D :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom (fullExpand D (p+1))) (fun p => by
    rw [fullPositive_d,FiniteModuleCech.positiveComplex_d]
    apply ModuleCat.hom_ext
    exact (fullExpand_d D (p+1)).symm)

lemma expand_sortMap : expandMap D ≫ sortMap D=𝟙 _ := by
  apply Hom.ext
  funext p
  apply ModuleCat.hom_ext
  exact fullSort_expand D (p+1)

lemma sort_expandMap (p : ℕ) :
    ((sortMap D ≫ expandMap D).f p).hom=fullN D (p+1) := fullExpand_sort D (p+1)

def homotopyComponent (i j : ℕ) : (fullPositive D).X i ⟶ (fullPositive D).X j :=
  if h : j+1=i then by subst i; exact ModuleCat.ofHom (fullH D (j+1)) else 0

lemma homotopyComponent_succ (j : ℕ) :
    homotopyComponent D (j+1) j=ModuleCat.ofHom (fullH D (j+1)) := by
  rw [homotopyComponent,dite_eq_left rfl]

def normalizationHomotopy : Homotopy (𝟙 (fullPositive D)) (sortMap D ≫ expandMap D) where
  hom := homotopyComponent D
  zero i j h := by
    change ¬j+1=i at h
    rw [homotopyComponent,dite_eq_right h]
  comm i := by
    rw [Homotopy.dNext_cochainComplex,homotopyComponent_succ,fullPositive_d]
    cases i with
    | zero =>
        rw [Homotopy.prevD_zero_cochainComplex,add_zero]
        apply ModuleCat.hom_ext
        have hh := fullH_identity D 0
        rw [fullH_zero,LinearMap.comp_zero,add_zero] at hh
        change LinearMap.id=(fullH D 1).comp (fullD D 1)+_
        rw [sort_expandMap]
        exact (eq_sub_iff_add_eq.mp hh).symm
    | succ i =>
        rw [Homotopy.prevD_succ_cochainComplex,homotopyComponent_succ,fullPositive_d]
        apply ModuleCat.hom_ext
        change LinearMap.id=(fullH D (i+2)).comp (fullD D (i+2))+
          (fullD D (i+1)).comp (fullH D (i+1))+_
        rw [sort_expandMap]
        exact (eq_sub_iff_add_eq.mp (fullH_identity D (i+1))).symm

 
def homotopyEquiv : HomotopyEquiv (fullPositive D) (FiniteModuleCech.positiveComplex D) where
  hom := sortMap D
  inv := expandMap D
  homotopyHomInvId := (normalizationHomotopy D).symm
  homotopyInvHomId := Homotopy.ofEq (expand_sortMap D)
end Lech.CechNormalization

end

end OAI
