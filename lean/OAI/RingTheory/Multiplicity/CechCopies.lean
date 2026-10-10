import Mathlib
import OAI.RingTheory.Multiplicity.ReesUlrichCech
import OAI.RingTheory.Multiplicity.TensorCechEuler

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]
  (D : Diagram R ι)

def copiesDiagram (κ : Type) : Diagram R ι where
  obj s := ModuleCat.of R (κ → D.obj s)
  res hst := ModuleCat.ofHom (LinearMap.pi fun k => (D.res hst).hom.comp (LinearMap.proj k))
  res_self s := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext k
    change (D.res (Finset.Subset.refl s)).hom (x k)=x k
    rw [D.res_self]
    rfl
  res_comp hst htv := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext k
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (D.res_comp hst htv)) (x k)

def copiesDiagonal (κ : Type) : Map D (copiesDiagram D κ) where
  app s := ModuleCat.ofHom (LinearMap.pi fun _ => LinearMap.id)
  naturality _ := by rfl

def copiesProjection {κ : Type} (k : κ) : Map (copiesDiagram D κ) D where
  app s := ModuleCat.ofHom (LinearMap.proj k)
  naturality _ := by rfl

lemma copies_positive_retract {κ : Type} (k : κ) :
    (copiesDiagonal D κ).positiveComplex ≫ (copiesProjection D k).positiveComplex=𝟙 _ := by
  apply Hom.ext
  funext q
  rfl

def tensorCechMap (F : CochainComplex (ModuleCat.{u} R) ℤ)
    {D E : Diagram R ι} (φ : Map D E) : tensorCech F D ⟶ tensorCech F E :=
  (TensorTotal.Right.functor F).map (extendMap φ.positiveComplex ComplexShape.embeddingUpNat)

lemma copies_tensor_retract (F : CochainComplex (ModuleCat.{u} R) ℤ) {κ : Type} (k : κ) :
    tensorCechMap F (copiesDiagonal D κ) ≫ tensorCechMap F (copiesProjection D k)=𝟙 _ := by
  let T := (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)) ⋙
    TensorTotal.Right.functor F
  change T.map (copiesDiagonal D κ).positiveComplex ≫
    T.map (copiesProjection D k).positiveComplex=𝟙 _
  rw [←T.map_comp,copies_positive_retract,T.map_id]

variable {I : Ideal R} (ell : TorsionLength I)
lemma finite_of_copies (F : CochainComplex (ModuleCat.{u} R) ℤ) {κ : Type} (k : κ)
    (hK : ∀ q,ell.finiteClass ((tensorCech F (copiesDiagram D κ)).homology q)) (q : ℤ) :
    ell.finiteClass ((tensorCech F D).homology q) := by
  have hs : homologyMap (tensorCechMap F (copiesDiagonal D κ)) q ≫
      homologyMap (tensorCechMap F (copiesProjection D k)) q=𝟙 _ := by
    rw [←homologyMap_comp,copies_tensor_retract,homologyMap_id]
  let : Epi (homologyMap (tensorCechMap F (copiesProjection D k)) q) :=
    epi_of_epi_fac (h:=𝟙 ((tensorCech F D).homology q)) hs
  exact ell.finiteClass.prop_of_epi (homologyMap (tensorCechMap F (copiesProjection D k)) q) (hK q)

def copiesReindex {κ η : Type} (e : κ ≃ η) (s : Finset ι) :
    (copiesDiagram D κ).obj s ≃ₗ[R] (copiesDiagram D η).obj s where
  toFun x k := x (e.symm k)
  invFun x k := x (e k)
  left_inv x := by funext k; simp only [Equiv.symm_apply_apply]
  right_inv x := by funext k; simp only [Equiv.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def copiesCongr {κ η : Type} (e : κ ≃ η) :
    positiveComplex (copiesDiagram D κ) ≅ positiveComplex (copiesDiagram D η) :=
  positiveIso (copiesReindex D e) (fun _ _ => rfl)

def copiesSuccEquiv (a : ℕ) (s : Finset ι) :
    (copiesDiagram D (Fin (a+1))).obj s ≃ₗ[R] (prodDiagram D (copiesDiagram D (Fin a))).obj s where
  toFun x := (x 0,fun k => x k.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := by funext k; exact Fin.cases rfl (fun _ => rfl) k
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def copiesSuccIso (a : ℕ) : positiveComplex (copiesDiagram D (Fin (a+1))) ≅
    positiveComplex (prodDiagram D (copiesDiagram D (Fin a))) :=
  positiveIso (copiesSuccEquiv D a) (fun _ _ => rfl)

lemma copies_zero (F : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ) :
    IsZero ((tensorCech F (copiesDiagram D (Fin 0))).homology q) := by
  have hZ : IsZero (positiveZ (copiesDiagram D (Fin 0))) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Hom.ext
    funext p
    have hX : IsZero ((positiveZ (copiesDiagram D (Fin 0))).X p) := by
      by_cases hp : 0 ≤ p
      · have he : ComplexShape.embeddingUpNat.f p.toNat=p := Int.toNat_of_nonneg hp
        apply IsZero.of_iso _ ((positiveComplex (copiesDiagram D (Fin 0))).extendXIso _ he)
        let : Subsingleton ((positiveComplex (copiesDiagram D (Fin 0))).X p.toNat) :=
          ⟨fun x y => by funext s k; exact Fin.elim0 k⟩
        exact ModuleCat.isZero_of_subsingleton _
      · exact positiveZ_bounded _ p (Or.inl (by omega))
    exact hX.eq_of_src _ _
  exact (homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).map_isZero
    ((TensorTotal.Right.functor F).map_isZero hZ)

lemma tensorEuler_copies_fin (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)
    (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
    (hflat : ∀ p,Module.Flat R (F.X p))
    (hD : ∀ q,ell.finiteClass ((tensorCech F D).homology q)) (a : ℕ) :
    (∀ q,ell.finiteClass ((tensorCech F (copiesDiagram D (Fin a))).homology q)) ∧
      tensorEuler ell F h (copiesDiagram D (Fin a))=(a:ℝ)*tensorEuler ell F h D := by
  induction a with
  | zero =>
      refine ⟨fun q => ell.finiteClass.prop_of_isZero (copies_zero D F q),?_⟩
      unfold tensorEuler
      rw [finiteHomologyEuler_zero ell _ (copies_zero D F)]
      simp
  | succ a ih =>
      have hP (q : ℤ) : ell.finiteClass ((tensorCech F (prodDiagram D (copiesDiagram D (Fin a)))).homology q) :=
        ell.finiteClass.prop_X₂_of_exact
          ((tensorShortComplex_shortExact (prodInl D _) (prodSnd D _) (prod_comp_zero D _)
            F hflat (prod_shortExact D _)).homology_exact₂ q) (hD q) (ih.1 q)
      have hC (q : ℤ) : ell.finiteClass ((tensorCech F (copiesDiagram D (Fin (a+1)))).homology q) :=
        ell.finiteClass.prop_of_iso
          ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).mapIso
            ((TensorTotal.Right.functor F).mapIso
              ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso (copiesSuccIso D a)))).symm
          (hP q)
      refine ⟨hC,?_⟩
      rw [tensorEuler_iso ell F h (copiesSuccIso D a) hC,
        tensorEuler_prod ell F h hb hflat _ _ hD ih.1,ih.2]
      push_cast
      ring

lemma tensorEuler_copies (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)
    (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
    (hflat : ∀ p,Module.Flat R (F.X p))
    {κ : Type} [Fintype κ] (k : κ)
    (hC : ∀ q,ell.finiteClass ((tensorCech F (copiesDiagram D κ)).homology q)) :
    tensorEuler ell F h (copiesDiagram D κ)=(Fintype.card κ:ℝ)*tensorEuler ell F h D := by
  classical
  rw [tensorEuler_iso ell F h (copiesCongr D (Fintype.equivFin κ)) hC]
  exact (tensorEuler_copies_fin D ell F h hb hflat (finite_of_copies D ell F k hC)
    (Fintype.card κ)).2
end Lech.FiniteModuleCech

end

end OAI
