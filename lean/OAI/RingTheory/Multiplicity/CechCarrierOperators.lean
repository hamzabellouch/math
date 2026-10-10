import Mathlib
import OAI.RingTheory.Multiplicity.CarrierOperators
import OAI.RingTheory.Multiplicity.CechNormalizationRows

namespace OAI

noncomputable section
namespace Lech.CechNormalization
open Set FiniteCoverCech CarrierOperators
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]

abbrev fullCarrier (p : ℕ) : Carrier ι := ⟨Fin p → ι,intersection⟩
abbrev sortedCarrier (p : ℕ) : Carrier ι := ⟨powersetCard ι p,Subtype.val⟩

def deltaOp (p : ℕ) : Op (R:=R) (fullCarrier (ι:=ι) p) (fullCarrier (p+1)) where
  app M := delta R M p
  natural l f := delta_natural R _ l p f
  locality M S f g h := delta_agree R M S p f g h

def normalizeOp (p : ℕ) : Op (R:=R) (fullCarrier (ι:=ι) p) (fullCarrier p) where
  app M := normalize R M p
  natural l f := normalize_natural R _ l p f
  locality M S f g h := normalize_agree R M S p f g h

def contractionOp (p : ℕ) : Op (R:=R) (fullCarrier (ι:=ι) (p+1)) (fullCarrier p) where
  app M := contraction R M p
  natural l f := contraction_natural R _ l p f
  locality M S f g h := contraction_agree R M S p f g h

def sortOp (p : ℕ) : Op (R:=R) (fullCarrier (ι:=ι) p) (sortedCarrier p) where
  app M := sortedRestriction R M p
  natural _ _ := rfl
  locality M S f g h s hs := by
    apply h
    change intersection (s.val.orderEmbOfFin s.property)⊆S
    intro index hindex
    obtain ⟨position,_,rfl⟩ := Finset.mem_image.mp hindex
    exact hs (s.val.orderEmbOfFin_mem s.property position)

variable (R) (M : Type u) [AddCommGroup M] [Module R M]

def expansion (p : ℕ) : (powersetCard ι p → M) →ₗ[R] Row M (ι:=ι) p :=
  (AlternatingCech.evaluation R M p).comp (AlternatingCech.sortedCoordinates R M p).symm.toLinearMap

lemma expansion_sorted (p : ℕ) (f : powersetCard ι p → M) (s : powersetCard ι p) :
    expansion R M p f (s.val.orderEmbOfFin s.property)=f s := by
  change AlternatingCech.evaluation R M p ((AlternatingCech.sortedCoordinates R M p).symm f)
    (s.val.orderEmbOfFin s.property)=_
  rw [←AlternatingCech.sortedCoordinates_eq_evaluation,LinearEquiv.apply_symm_apply]

lemma expansion_perm (p : ℕ) (f : powersetCard ι p → M) (a : Fin p → ι) (σ : Equiv.Perm (Fin p)) :
    expansion R M p f (a ∘ σ)=(Equiv.Perm.sign σ:ℤ) • expansion R M p f a := by
  change ((AlternatingCech.sortedCoordinates R M p).symm f)
    ((fun i => AlternatingCech.basis R (a i)) ∘ σ)=_
  exact ((AlternatingCech.sortedCoordinates R M p).symm f).map_perm _ σ

lemma expansion_degenerate (p : ℕ) (f : powersetCard ι p → M) (a : Fin p → ι)
    (ha : ¬Function.Injective a) : expansion R M p f a=0 := by
  apply ((AlternatingCech.sortedCoordinates R M p).symm f).map_eq_zero_of_not_injective
  intro h
  apply ha
  intro i j hij
  exact h (congrArg (AlternatingCech.basis R) hij)

lemma expansion_natural {N : Type u} [AddCommGroup N] [Module R N]
    (l : M →ₗ[R] N) (p : ℕ) (f : powersetCard ι p → M) :
    expansion R N p (l ∘ f)=l ∘ expansion R M p f := by
  ext a
  by_cases h : Function.Injective a
  · obtain ⟨s,σ,hs,hσ⟩ := AlternatingCech.tuple_sort a h
    rw [hσ,expansion_perm,expansion_sorted]
    change _=l (expansion R M p f (s.val.orderEmbOfFin s.property ∘ σ))
    rw [expansion_perm,expansion_sorted,map_zsmul]
    rfl
  · rw [expansion_degenerate R N p _ a h]
    change _=l (expansion R M p f a)
    rw [expansion_degenerate R M p f a h,map_zero]

lemma expansion_agree (S : Finset ι) (p : ℕ) (f g : powersetCard ι p → M)
    (hf : Agree (sortedCarrier p) M S f g) :
    Agree (fullCarrier p) M S (expansion R M p f) (expansion R M p g) := by
  intro a ha
  by_cases h : Function.Injective a
  · obtain ⟨s,σ,hs,hσ⟩ := AlternatingCech.tuple_sort a h
    rw [hσ,expansion_perm,expansion_perm,expansion_sorted,expansion_sorted]
    congr 1
    apply hf
    change s.val⊆S
    rw [←hs]
    intro index hindex
    obtain ⟨position,_,hposition⟩ :=
      (@Finset.mem_image (Fin p) ι
        (fun left right => Classical.propDecidable (left=right)) a Finset.univ index).mp hindex
    exact ha (Finset.mem_image.mpr ⟨position,Finset.mem_univ _,hposition⟩)
  · rw [expansion_degenerate R M p f a h,expansion_degenerate R M p g a h]

variable {R M}
def expandOp (p : ℕ) : Op (R:=R) (sortedCarrier (ι:=ι) p) (fullCarrier p) where
  app M := expansion R M p
  natural l f := expansion_natural R _ l p f
  locality M S f g h := expansion_agree R M S p f g h

def sortedDeltaOp (p : ℕ) : Op (R:=R) (sortedCarrier (ι:=ι) p) (sortedCarrier (p+1)) where
  app M := AlternatingCech.rawDelta R M p
  natural l f := by
    ext s
    change (∑ i : Fin (p+1),(-1:ℤ)^i.val • l (f (AlternatingCech.delete s i))) =
      l (∑ i : Fin (p+1),(-1:ℤ)^i.val • f (AlternatingCech.delete s i))
    rw [map_sum]
    simp only [map_zsmul]
  locality M S f g h s hs := by
    change (∑ i : Fin (p+1),(-1:ℤ)^i.val • f (AlternatingCech.delete s i)) =
      ∑ i : Fin (p+1),(-1:ℤ)^i.val • g (AlternatingCech.delete s i)
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    exact h _ ((AlternatingCech.delete_subset s i).trans hs)

omit [Fintype ι] in
lemma sort_delta (M : ModuleCat.{u} R) (p : ℕ) :
    ((sortOp (R:=R) (ι:=ι) (p+1)).app M).comp ((deltaOp p).app M) =
      ((sortedDeltaOp p).app M).comp ((sortOp p).app M) := by
  apply LinearMap.ext
  intro f
  funext s
  change (∑ i : Fin (p+1),(-1:R)^i.val • f (s.val.orderEmbOfFin s.property ∘ i.succAbove)) =
    ∑ i : Fin (p+1),(-1:ℤ)^i.val • f ((AlternatingCech.delete s i).val.orderEmbOfFin (AlternatingCech.delete s i).property)
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Int.cast_smul_eq_zsmul R]
  simp only [Int.cast_pow,Int.cast_neg,Int.cast_one]
  congr 1
  change f (powersetCard.ofFinEmbEquiv.symm s ∘ i.succAbove)=
    f (powersetCard.ofFinEmbEquiv.symm (AlternatingCech.delete s i))
  rw [AlternatingCech.delete_sorted]
  rfl

lemma sort_expand (M : ModuleCat.{u} R) (p : ℕ) :
    ((sortOp (R:=R) (ι:=ι) p).app M).comp ((expandOp p).app M)=LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext s
  exact expansion_sorted R M p f s

lemma expand_sort (M : ModuleCat.{u} R) (p : ℕ) :
    ((expandOp (R:=R) (ι:=ι) p).app M).comp ((sortOp p).app M)=(normalizeOp p).app M := rfl

lemma expand_delta (M : ModuleCat.{u} R) (p : ℕ) :
    ((expandOp (R:=R) (ι:=ι) (p+1)).app M).comp ((sortedDeltaOp p).app M) =
      ((deltaOp p).app M).comp ((expandOp p).app M) := by
  apply LinearMap.ext
  intro f
  have hr : sortedRestriction R M p (expansion R M p f)=f := by
    ext s
    exact expansion_sorted R M p f s
  have hs := DFunLike.congr_fun (sort_delta (R:=R) (ι:=ι) M p) (expansion R M p f)
  change sortedRestriction R M (p+1) (delta R M p (expansion R M p f))=
    AlternatingCech.rawDelta R M p (sortedRestriction R M p (expansion R M p f)) at hs
  rw [hr] at hs
  change expansion R M (p+1) (AlternatingCech.rawDelta R M p f)=delta R M p (expansion R M p f)
  rw [←hs]
  change normalize R M (p+1) (delta R M p (expansion R M p f))=_
  rw [normalize_delta]
  change delta R M p (expansion R M p (sortedRestriction R M p (expansion R M p f)))=_
  rw [hr]
end Lech.CechNormalization

end

end OAI
