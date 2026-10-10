import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.DimensionNonneg

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "C" => fusionFoldedCartan m d

include hm in

lemma fusion_subobject_cartan_inequality
    {T R U:FusionLabel m → Type} [∀ L,Fintype (T L)] [∀ L,Fintype (R L)] [∀ L,Fintype (U L)]
    (M:∀ L,BasedComplex Q (K:=ℂ) (T L)) (S:∀ L,BasedComplex Q (K:=ℂ) (R L))
    (F:∀ L,BasedComplex Q (K:=ℂ) (U L)) (q k:ℤ)
    (hM:∀ L i,((M L).placement i).level=q) (hS:∀ L i,((S L).placement i).level=q)
    (hF:∀ L i,((F L).placement i).level=k)
    (incl:∀ L,TermwiseSplitInjection Q (S L) (M L)) (J:Set V)
    (hsupp:∀ L i,((S L).placement i).color.1∈J)
    (hsoc:∀ H α,α.1∈J → ∀ r,coefficientSocle Q (F H) α r=⊥)
    (hmid:∀ L H,totalHomDimension Q (M L) (F H) (k-q+1)=0) :
    fusionWeightedHom m d hd M F (k-q) ≤
      ((∑ L,fusionWeight m L • generatorVector Q (M L))-
       (∑ L,fusionWeight m L • generatorVector Q (S L))) ⬝ᵥ
        (unfoldedCartan Q *ᵥ (∑ H,fusionWeight m H • generatorVector Q (F H))) := by
  have he : ((∑ L,fusionWeight m L • generatorVector Q (M L))-
       (∑ L,fusionWeight m L • generatorVector Q (S L))) =
      ∑ L,fusionWeight m L • (generatorVector Q (M L)-generatorVector Q (S L)) := by
    simp only [smul_sub,Finset.sum_sub_distrib]
  rw [he,finite_weighted_cartan]
  unfold fusionWeightedHom
  apply Finset.sum_le_sum
  intro L _
  apply Finset.sum_le_sum
  intro H _
  apply mul_le_mul_of_nonneg_left _ (mul_pos (fusionWeight_pos m hm L) (fusionWeight_pos m hm H)).le
  exact subobject_cartan_inequality Q (M L) (S L) (F H) (hM L) (hS L) (hF H)
    (incl L) {α|α.1∈J} (hsupp L) (hsoc H) (hmid L H)

lemma fusion_weighted_euler_of_middle_zero
    {T R:FusionLabel m → Type} [∀ L,Fintype (T L)] [∀ L,Fintype (R L)]
    (M:∀ L,BasedComplex Q (K:=ℂ) (T L)) (F:∀ L,BasedComplex Q (K:=ℂ) (R L)) (q k:ℤ)
    (hM:∀ L i,((M L).placement i).level=q) (hF:∀ L i,((F L).placement i).level=k)
    (hmid:∀ L H,totalHomDimension Q (M L) (F H) (k-q+1)=0) :
    (∑ L,fusionWeight m L • generatorVector Q (M L)) ⬝ᵥ
      (unfoldedCartan Q *ᵥ (∑ H,fusionWeight m H • generatorVector Q (F H))) =
      fusionWeightedHom m d hd M F (k-q)+fusionWeightedHom m d hd F M (q-k) := by
  rw [finite_weighted_cartan]
  have he (L H:FusionLabel m) := pure_cartan_euler Q (M L) (F H) (hM L) (hF H)
  simp only [hmid,Nat.cast_zero,sub_zero] at he
  simp_rw [he]
  simp only [_root_.mul_add,Finset.sum_add_distrib,fusionWeightedHom]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro L _
  apply Finset.sum_congr rfl
  intro H _
  rw [mul_comm (fusionWeight m H) (fusionWeight m L)]

theorem fusionOrbit_subobject_null_separation
    (w:List (V × Bool)) (s:V) {T:FusionLabel m → Type} [∀ L,Fintype (T L)]
    (M:∀ L,BasedComplex Q (K:=ℂ) (T L)) (q k:ℤ)
    (hM:∀ L i,((M L).placement i).level=q)
    (ι:∀ L,Map Q (M L) (Y w s L q)) (π:∀ L,Map Q (Y w s L q) (M L))
    (hret:∀ L,(ι L).matrix*(π L).matrix=projectiveIdentity Q (M L).placement)
    {B:Type} {R:B → FusionLabel m → Type} [∀ b L,Fintype (R b L)]
    (S:∀ b L,BasedComplex Q (K:=ℂ) (R b L))
    (hS:∀ b L i,((S b L).placement i).level=q)
    (incl:∀ b L,TermwiseSplitInjection Q (S b L) (M L))
    (I J:Set V) (c a:V → ℝ) (σ:B → V → ℝ)
    (hmvec:(∑ L,fusionWeight m L • generatorVector Q (M L))=fusionFold m a)
    (hsvec:∀ b,(∑ L,fusionWeight m L • generatorVector Q (S b L))=fusionFold m (σ b))
    (hsupp:∀ b L i,((S b L).placement i).color.1∈J)
    (hσ:∀ b v,v∉J → σ b v=0)
    (hc:∀ v,0 ≤ c v) (hcSupp:∀ v,v∉I → c v=0) (hcPos:∀ v,v∈I → 0<c v)
    (hcNull:∀ v,v∈I → (C *ᵥ c) v=0) (hext:∀ v,v∉J → a v=c v)
    (hint:(fun j:J=>a j-c j)∈interior (convexHull ℝ (Set.range fun b:B=>(fun j:J=>σ b j))))
    (hsoc:∀ H α,α.1∈J → ∀ r,coefficientSocle Q (Y w s H k) α r=⊥) :
    (∀ v∉I,(∃ u∈I,C v u<0) → fusionOrbitMultiplicity m d hd hdiag hm w s k v=0) ∧
    (∀ j∈J,(C *ᵥ fusionOrbitMultiplicity m d hd hdiag hm w s k) j=0) ∧
    fusionWeightedHom m d hd M (fun H=>Y w s H k) (k-q)=0 ∧
    fusionWeightedHom m d hd (fun H=>Y w s H k) M (q-k)=0 := by
  let y := fusionOrbitMultiplicity m d hd hdiag hm w s k
  let F := fun H=>Y w s H k
  let H₀ := fusionWeightedHom m d hd M F (k-q)
  have hF : ∀ H i,((F H).placement i).level=k := by
    intro H i
    exact i.property
  have hmid : ∀ L H,totalHomDimension Q (M L) (F H) (k-q+1)=0 := by
    intro L H
    exact fusionOrbit_summand_middle m d hd hdiag w s L H (M L) q k (ι L) (π L) (hret L)
  have hyvec : (∑ H,fusionWeight m H • generatorVector Q (F H))=fusionFold m y :=
    fusionOrbitWeightedVector_eq m d hd hdiag hm w s k
  have hD := fusionD0_pos m hm
  have hbound : ∀ b,H₀ ≤ fusionD0 m*((a-σ b) ⬝ᵥ (C *ᵥ y)) := by
    intro b
    have h := fusion_subobject_cartan_inequality m d hd hm M (S b) F q k hM (hS b) hF
      (incl b) J (hsupp b) hsoc hmid
    rw [hmvec,hsvec b,hyvec] at h
    have he : fusionFold m a-fusionFold m (σ b)=fusionFold m (a-σ b) := by
      ext α
      simp only [fusionFold,Pi.sub_apply,mul_sub]
    rw [he,fusionQuiver_cartan,fusion_pairing m hm] at h
    exact h
  have hb : ∀ z∈(Set.range fun b:B=>(fun j:J=>σ b j)),
      H₀/fusionD0 m ≤ (a-NullBoundary.extend J z) ⬝ᵥ (C *ᵥ y) := by
    rintro _ ⟨b,rfl⟩
    rw [NullBoundary.extend_restrict J (σ b) (hσ b)]
    exact (div_le_iff₀ hD).mpr (by simpa only [mul_comm] using hbound b)
  have hsep := NullBoundary.convex_null_boundary_separation C I J c a y
    (Set.range fun b:B=>(fun j:J=>σ b j)) (H₀/fusionD0 m)
    (fusionFoldedCartan_symm m d hd) (fusionFoldedCartan_off_nonpos m d hm)
    hc hcSupp hcPos hcNull (fusionOrbitMultiplicity_nonneg m d hd hdiag hm w s k)
    hext hint (div_nonneg (fusionWeightedHom_nonneg m d hd hm M F (k-q)) hD.le) hb
  have hzero : H₀=0 := (div_eq_zero_iff.mp hsep.2.2.1).resolve_right (ne_of_gt hD)
  refine ⟨hsep.1,hsep.2.1,hzero,?_⟩
  have he := fusion_weighted_euler_of_middle_zero m d hd M F q k hM hF hmid
  rw [hmvec,hyvec,fusionQuiver_cartan,fusion_pairing m hm,hsep.2.2.2,MulZeroClass.mul_zero] at he
  change 0=H₀+_ at he
  simpa only [hzero,zero_add] using he.symm

end HarmonicArtin

end OAI
