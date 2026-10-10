import Mathlib
import OAI.Topology.ArtinGroups.Realizations.OrderWeights

namespace OAI

namespace HarmonicArtin
open Convexity
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def simplexSupport {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) : Finset (Fin (n+1)) :=
  Finset.univ.filter (fun index=>z.weights index≠0)

lemma mem_simplexSupport {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) (i:Fin (n+1)) :
    i∈simplexSupport z ↔ z.weights i≠0 := by simp [simplexSupport]

lemma simplexSupport_nonempty {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) :
    (simplexSupport z).Nonempty := by
  by_contra hn
  have hz:∀index,z.weights index=0:=by
    intro i
    by_contra h
    exact hn ⟨i,(mem_simplexSupport z i).mpr h⟩
  have ht:=z.total_of_fintype
  simp only [hz,Finset.sum_const_zero] at ht
  norm_num at ht

noncomputable def simplexSupportDim {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) : ℕ :=
  (simplexSupport z).card-1

lemma simplexSupportDim_succ {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) :
    simplexSupportDim z+1=(simplexSupport z).card := by
  have :=(simplexSupport_nonempty z).card_pos
  unfold simplexSupportDim
  omega

noncomputable def simplexSupportEnum {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) :
    Fin (simplexSupportDim z+1) ≃o {i // i∈simplexSupport z} :=
  (simplexSupport z).orderIsoOfFin (simplexSupportDim_succ z).symm

noncomputable def simplexSupportInclusion {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) :
    Fin (simplexSupportDim z+1) →o Fin (n+1) :=
  ⟨fun i=>(simplexSupportEnum z i).val,fun _ _ h=>(simplexSupportEnum z).monotone h⟩

noncomputable def simplexSupported {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) :
    StdSimplex ℝ (Fin (simplexSupportDim z+1)) :=
  ⟨Finsupp.equivFunOnFinite.symm (fun index=>z.weights (simplexSupportInclusion z index)),
    fun index=>z.nonneg _,by
    rw [Finsupp.sum_fintype _ _ (by intros; rfl)]
    have he:=Equiv.sum_comp (simplexSupportEnum z).toEquiv (fun index=>z.weights index.val)
    change (∑index,z.weights (simplexSupportInclusion z index))=1
    rw [show (∑index,z.weights (simplexSupportInclusion z index))=
      ∑index:simplexSupport z,z.weights index.val from he]
    rw [Finset.sum_coe_sort]
    calc
      _ = ∑index,z.weights index := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        exact not_not.mp (fun h=>hi ((mem_simplexSupport z i).mpr h))
      _=1:=z.total_of_fintype⟩

lemma simplexSupported_map {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) :
    StdSimplex.map (simplexSupportInclusion z) (simplexSupported z)=z := by
  apply StdSimplex.ext
  apply Finsupp.ext
  intro index
  change Finsupp.mapDomain (simplexSupportInclusion z) (simplexSupported z).weights index =
    z.weights index
  by_cases supported:index∈simplexSupport z
  · let supportedIndex:Fin (simplexSupportDim z+1):=
      (simplexSupportEnum z).symm ⟨index,supported⟩
    have imageEq:simplexSupportInclusion z supportedIndex=index:=
      congrArg Subtype.val ((simplexSupportEnum z).apply_symm_apply ⟨index,supported⟩)
    have inclusionInjective:Function.Injective (simplexSupportInclusion z):=
      Subtype.val_injective.comp (simplexSupportEnum z).injective
    rw [← imageEq, Finsupp.mapDomain_apply_of_injective inclusionInjective]
    rfl
  · have weightZero:z.weights index=0:=
      not_not.mp (fun nonzero=>supported ((mem_simplexSupport z index).mpr nonzero))
    rw [Finsupp.mapDomain_of_notMem_range, weightZero]
    rintro ⟨supportedIndex, imageEq⟩
    exact supported (imageEq ▸ (simplexSupportEnum z supportedIndex).property)

lemma chainWeights_support_positive {n:ℕ} (x:Fin (n+1)→o P)
    (z:StdSimplex ℝ (Fin (n+1))) {i:Fin (n+1)} (hi:i∈simplexSupport z) :
    x i∈(chainWeights x z).support := by
  rw [Finsupp.mem_support_iff]
  have hz:0<z.weights i:=lt_of_le_of_ne (z.nonneg i) (Ne.symm ((mem_simplexSupport z i).mp hi))
  have hs:z.weights i≤chainWeights x z (x i):=by
    rw [chainWeights_apply]
    calc
      _=(if x i=x i then z.weights i else 0):=by simp
      _≤_:=Finset.single_le_sum (f:=fun index:Fin (n+1)=>if x index=x i then z.weights index else 0)
        (fun index _=>by split_ifs;exacts [z.nonneg index,le_rfl]) (Finset.mem_univ i)
  exact ne_of_gt (lt_of_lt_of_le hz hs)

end HarmonicArtin

end OAI
