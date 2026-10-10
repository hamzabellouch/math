import Mathlib
import OAI.RingTheory.Multiplicity.FiniteModuleCech

namespace OAI

noncomputable section
namespace Lech.CechNormalization
open Set FiniteCoverCech
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
  {ι : Type} [Fintype ι] [LinearOrder ι]

def sortedRestriction (p : ℕ) : Row M (ι:=ι) p →ₗ[R] (powersetCard ι p → M) where
  toFun f s := f (s.val.orderEmbOfFin s.property)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def altify (p : ℕ) : Row M (ι:=ι) p →ₗ[R] AlternatingCech.Alt R M (ι:=ι) p :=
  (AlternatingCech.sortedCoordinates R M p).symm.toLinearMap.comp (sortedRestriction R M p)

def normalize (p : ℕ) : Row M (ι:=ι) p →ₗ[R] Row M (ι:=ι) p :=
  (AlternatingCech.evaluation R M p).comp (altify R M p)

lemma normalize_sorted (p : ℕ) (f : Row M (ι:=ι) p) (s : powersetCard ι p) :
    normalize R M p f (s.val.orderEmbOfFin s.property)=f (s.val.orderEmbOfFin s.property) := by
  change AlternatingCech.evaluation R M p (altify R M p f) (s.val.orderEmbOfFin s.property)=_
  rw [←AlternatingCech.sortedCoordinates_eq_evaluation]
  change AlternatingCech.sortedCoordinates R M p
    ((AlternatingCech.sortedCoordinates R M p).symm (sortedRestriction R M p f)) s=_
  rw [LinearEquiv.apply_symm_apply]
  rfl

lemma altify_delta (p : ℕ) (f : Row M (ι:=ι) p) :
    altify R M (p+1) (delta R M p f)=AlternatingCech.delta R M p (altify R M p f) := by
  apply (AlternatingCech.sortedCoordinates R M (p+1)).injective
  ext s
  change AlternatingCech.sortedCoordinates R M (p+1)
    ((AlternatingCech.sortedCoordinates R M (p+1)).symm _) s=_
  rw [LinearEquiv.apply_symm_apply,AlternatingCech.sortedCoordinates_delta]
  change (∑ i : Fin (p+1),(-1:R)^i.val • f (s.val.orderEmbOfFin s.property ∘ i.succAbove)) = _
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Int.cast_smul_eq_zsmul R]
  simp only [Int.cast_pow,Int.cast_neg,Int.cast_one]
  congr 1
  change f (powersetCard.ofFinEmbEquiv.symm s ∘ i.succAbove)=
    AlternatingCech.sortedCoordinates R M p
      ((AlternatingCech.sortedCoordinates R M p).symm (sortedRestriction R M p f)) (AlternatingCech.delete s i)
  rw [LinearEquiv.apply_symm_apply]
  change f (powersetCard.ofFinEmbEquiv.symm s ∘ i.succAbove)=
    f (powersetCard.ofFinEmbEquiv.symm (AlternatingCech.delete s i))
  rw [AlternatingCech.delete_sorted]
  rfl

lemma normalize_delta (p : ℕ) (f : Row M (ι:=ι) p) :
    normalize R M (p+1) (delta R M p f)=delta R M p (normalize R M p f) := by
  change AlternatingCech.evaluation R M (p+1) (altify R M (p+1) (delta R M p f))=_
  rw [altify_delta,AlternatingCech.evaluation_delta]
  rfl

lemma normalize_zero (f : Row M (ι:=ι) 0) : normalize R M 0 f=f := by
  ext a
  let s : powersetCard ι 0 := ⟨∅,rfl⟩
  have ha : a=s.val.orderEmbOfFin s.property := Subsingleton.elim _ _
  rw [ha,normalize_sorted]

lemma normalize_perm (p : ℕ) (f : Row M (ι:=ι) p) (a : Fin p → ι) (σ : Equiv.Perm (Fin p)) :
    normalize R M p f (a ∘ σ)=(Equiv.Perm.sign σ:ℤ) • normalize R M p f a := by
  change altify R M p f ((fun i => AlternatingCech.basis R (a i)) ∘ σ)=_
  exact (altify R M p f).map_perm _ σ

lemma normalize_degenerate (p : ℕ) (f : Row M (ι:=ι) p) (a : Fin p → ι)
    (ha : ¬Function.Injective a) : normalize R M p f a=0 := by
  apply (altify R M p f).map_eq_zero_of_not_injective
  intro h
  apply ha
  intro i j hij
  exact h (congrArg (AlternatingCech.basis R) hij)

def AgreeOn (S : Finset ι) (p : ℕ) (f g : Row M (ι:=ι) p) : Prop :=
  ∀ a,intersection a ⊆ S → f a=g a

lemma normalize_agree (S : Finset ι) (p : ℕ) (f g : Row M (ι:=ι) p)
    (hf : AgreeOn M S p f g) : AgreeOn M S p (normalize R M p f) (normalize R M p g) := by
  intro a ha
  by_cases h : Function.Injective a
  · obtain ⟨s,σ,_,hσ⟩ := AlternatingCech.tuple_sort a h
    rw [hσ,normalize_perm,normalize_perm,normalize_sorted,normalize_sorted]
    congr 1
    apply hf
    intro index hindex
    obtain ⟨position,_,hposition⟩ := Finset.mem_image.mp hindex
    apply ha
    refine Finset.mem_image.mpr ⟨σ.symm position,Finset.mem_univ _,?_⟩
    simpa only [hσ,Function.comp_apply,Equiv.apply_symm_apply] using hposition
  · rw [normalize_degenerate R M p f a h,normalize_degenerate R M p g a h]

variable {N : Type u} [AddCommGroup N] [Module R N]
lemma normalize_natural (l : M →ₗ[R] N) (p : ℕ) (f : Row M (ι:=ι) p) :
    normalize R N p (l ∘ f)=l ∘ normalize R M p f := by
  ext a
  by_cases h : Function.Injective a
  · obtain ⟨s,σ,hs,hσ⟩ := AlternatingCech.tuple_sort a h
    rw [hσ,normalize_perm,normalize_sorted]
    change _=l (normalize R M p f (s.val.orderEmbOfFin s.property ∘ σ))
    rw [normalize_perm,normalize_sorted,map_zsmul]
    rfl
  · rw [normalize_degenerate R N p _ a h]
    change _=l (normalize R M p f a)
    rw [normalize_degenerate R M p f a h,map_zero]

omit [Fintype ι] [LinearOrder ι] in
lemma delta_natural (l : M →ₗ[R] N) (p : ℕ) (f : Row M (ι:=ι) p) :
    delta R N p (l ∘ f)=l ∘ delta R M p f := by
  ext a
  simp only [delta,LinearMap.coe_mk,AddHom.coe_mk,Function.comp_apply,map_sum,map_smul]

omit [Fintype ι] in
lemma delta_agree (S : Finset ι) (p : ℕ) (f g : Row M (ι:=ι) p)
    (hf : AgreeOn M S p f g) : AgreeOn M S (p+1) (delta R M p f) (delta R M p g) := by
  intro a ha
  change (∑ i : Fin (p+1),(-1:R)^i.val • f (a ∘ i.succAbove)) =
    ∑ i : Fin (p+1),(-1:R)^i.val • g (a ∘ i.succAbove)
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact hf _ ((intersection_delete a i).trans ha)

omit [Fintype ι] in
lemma extra_agree (S : Finset ι) (c : ι) (hc : c∈S) (p : ℕ) (f g : Row M (ι:=ι) (p+1))
    (hf : AgreeOn M S (p+1) f g) : AgreeOn M S p (extra R M c p f) (extra R M c p g) := by
  intro a ha
  apply hf
  rw [intersection_cons]
  exact Finset.insert_subset hc ha

 

def contraction : (p : ℕ) → Row M (ι:=ι) (p+1) →ₗ[R] Row M (ι:=ι) p
  | 0 => 0
  | p+1 => LinearMap.pi (fun a : Fin (p+1) → ι =>
      (LinearMap.proj a).comp
        (extra R M (a 0) (p+1) -
          (normalize R M (p+1)).comp (extra R M (a 0) (p+1)) -
          (delta R M p).comp ((contraction p).comp (extra R M (a 0) (p+1)))))

lemma contraction_succ (p : ℕ) (f : Row M (ι:=ι) (p+2)) (a : Fin (p+1) → ι) :
    contraction R M (p+1) f a =
      (extra R M (a 0) (p+1) f - normalize R M (p+1) (extra R M (a 0) (p+1) f) -
        delta R M p (contraction R M p (extra R M (a 0) (p+1) f))) a := rfl

lemma contraction_identity_step (p : ℕ)
    (h : ∀ g : Row M (ι:=ι) p,
      delta R M p (contraction R M p (delta R M p g))=
        delta R M p g-normalize R M (p+1) (delta R M p g))
    (f : Row M (ι:=ι) (p+1)) :
    contraction R M (p+1) (delta R M (p+1) f)+delta R M p (contraction R M p f)=
      f-normalize R M (p+1) f := by
  ext a
  rw [Pi.add_apply,contraction_succ]
  let c := a 0
  let g := extra R M c p f
  have he : extra R M c (p+1) (delta R M (p+1) f)=f-delta R M p g :=
    eq_sub_iff_add_eq.mpr (extra_delta R M c p f)
  have hh : extra R M c (p+1) (delta R M (p+1) f)-
      normalize R M (p+1) (extra R M c (p+1) (delta R M (p+1) f))-
      delta R M p (contraction R M p (extra R M c (p+1) (delta R M (p+1) f)))+
      delta R M p (contraction R M p f)=f-normalize R M (p+1) f := by
    rw [he,map_sub,map_sub,map_sub,h g]
    abel
  exact congrFun hh a

lemma contraction_identity (p : ℕ) (f : Row M (ι:=ι) (p+1)) :
    contraction R M (p+1) (delta R M (p+1) f)+delta R M p (contraction R M p f)=
      f-normalize R M (p+1) f := by
  induction p with
  | zero =>
    apply contraction_identity_step
    intro g
    rw [contraction,LinearMap.zero_apply,map_zero,normalize_delta,normalize_zero,sub_self]
  | succ p ih =>
    apply contraction_identity_step
    intro g
    have hi := congrArg (delta R M (p+1)) (ih g)
    rw [map_add,delta_square,add_zero,map_sub,←normalize_delta] at hi
    exact hi

lemma contraction_natural (l : M →ₗ[R] N) (p : ℕ) (f : Row M (ι:=ι) (p+1)) :
    contraction R N p (l ∘ f)=l ∘ contraction R M p f := by
  induction p with
  | zero => ext a; simp [contraction]
  | succ p ih =>
    ext a
    rw [contraction_succ]
    change _=l (contraction R M (p+1) f a)
    rw [contraction_succ]
    have he : extra R N (a 0) (p+1) (l ∘ f)=l ∘ extra R M (a 0) (p+1) f := rfl
    rw [he,normalize_natural,ih,delta_natural]
    simp only [Pi.sub_apply,Function.comp_apply,map_sub]

lemma contraction_agree (S : Finset ι) (p : ℕ) (f g : Row M (ι:=ι) (p+1))
    (hf : AgreeOn M S (p+1) f g) : AgreeOn M S p (contraction R M p f) (contraction R M p g) := by
  induction p with
  | zero => intro a ha; rfl
  | succ p ih =>
    intro a ha
    rw [contraction_succ,contraction_succ]
    have hc : a 0∈S := ha (Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩)
    have he := extra_agree R M S (a 0) hc (p+1) f g hf
    simp only [Pi.sub_apply]
    rw [he a ha,normalize_agree R M S (p+1) _ _ he a ha,
      delta_agree R M S p _ _ (ih _ _ he) a ha]
end Lech.CechNormalization

end

end OAI
