import OAI.RingTheory.BassTrace.FreeParameters

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace

section

open scoped Classical BigOperators

variable {G : Type*} [Group G]

omit [Group G] in
lemma trace_coeff {ι : Type*} [Fintype ι] (e : Paths.GroupMatrix (G := G) (ι := ι)) (s : G) :
    (Matrix.trace e).coeff s=Matrix.trace (Paths.coefficient e s) := by
  simp only [Matrix.trace,Matrix.diag,MonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,Paths.coefficient]

lemma classCoefficient_eq_finsum (g : G) (a : MonoidAlgebra ℂ G) :
    classCoefficient g a=∑ᶠ s∈{s : G|IsConj s g},a.coeff s := by
  unfold classCoefficient
  simp only [Set.mem_ofPred_eq,finsum_eq_if]
  symm
  apply finsum_eq_sum_of_support_subset
  intro s hs
  by_contra h
  have hz := Finsupp.notMem_support_iff.mp h
  simp [hz] at hs

lemma totalWeight_eq_classCoefficient {ι : Type*} [Fintype ι]
    (e : Paths.GroupMatrix (G := G) (ι := ι)) (he : e*e=e) (g : G) :
    Paths.totalWeight e g 0=classCoefficient g (Matrix.trace e) := by
  rw [Paths.totalWeight_conjugacy e he g 0,classCoefficient_eq_finsum]
  simp only [trace_coeff]

lemma sum_conjugacy_invariant_zero (a : MonoidAlgebra ℂ G) (P : G→Prop)
    (hinv : ∀h k,IsConj h k→(P h↔P k))
    (hz : ∀h,P h→classCoefficient h a=0) :
    a.coeff.sum (fun h z=>if P h then z else 0)=0 := by
  rw [Finsupp.sum]
  rw [←Finset.sum_fiberwise_of_maps_to (s := a.coeff.support)
      (t := a.coeff.support.image ConjClasses.mk)
      (fun i hi=>Finset.mem_image_of_mem _ hi)]
  apply Finset.sum_eq_zero
  intro q hq
  obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hq
  by_cases hp : P h
  · have he : (∑i∈a.coeff.support with ConjClasses.mk i=ConjClasses.mk h,
        if P i then a.coeff i else 0)=classCoefficient h a := by
      rw [classCoefficient,Finsupp.sum,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      simp only [ConjClasses.mk_eq_mk_iff_isConj]
      by_cases hc : IsConj i h
      · simp only [hc,ite_eq_left,(hinv i h hc).mpr hp]
      · simp only [hc,ite_false]
    rw [he,hz h hp]
  · apply Finset.sum_eq_zero
    intro i hi
    have hc := ConjClasses.mk_eq_mk_iff_isConj.mp (Finset.mem_filter.mp hi).2
    simp only [(hinv i h hc).not.mpr hp,ite_false]

end

open scoped Classical BigOperators

variable {G : Type*} [Group G] {ι : Type*} [Fintype ι]

lemma exists_symmetric_generators [Group.FG G] (e : Paths.GroupMatrix (G := G) (ι := ι)) :
    ∃S : Finset G,(∀s∈S,s⁻¹∈S) ∧ Subgroup.closure (S : Set G)=⊤ ∧ Paths.support e⊆S := by
  obtain ⟨T,hT,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let U := hfin.toFinset ∪ Paths.support e
  let S := U ∪ U.image Inv.inv
  refine ⟨S,?_,?_,?_⟩
  · intro s hs
    rcases Finset.mem_union.mp hs with hs|hs
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs)
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_union_left _ (by simpa only [inv_inv] using hu)
  · apply top_unique
    rw [←hT]
    apply Subgroup.closure_mono
    intro s hs
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (hfin.mem_toFinset.mpr hs))
  · intro s hs
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hs)

def restrictMatrix (K : Subgroup G) (e : Paths.GroupMatrix (G := G) (ι := ι)) :
    Paths.GroupMatrix (G := K) (ι := ι) :=
  fun i j=>MonoidAlgebra.comapDomain Subtype.val Subtype.val_injective (e i j)

lemma restrictMatrix_map (K : Subgroup G) (e : Paths.GroupMatrix (G := G) (ι := ι))
    (hs : ∀s∈Paths.support e,s∈K) :
    (restrictMatrix K e).map (MonoidAlgebra.mapDomainRingHom ℂ K.subtype)=e := by
  apply Matrix.ext
  intro i j
  apply MonoidAlgebra.mapDomain_comapDomain
  intro s hs'
  exact ⟨⟨s,hs s (Paths.entry_support_subset e i j hs')⟩,rfl⟩

lemma restrictMatrix_idempotent (K : Subgroup G) (e : Paths.GroupMatrix (G := G) (ι := ι))
    (he : e*e=e) (hs : ∀s∈Paths.support e,s∈K) :
    restrictMatrix K e * restrictMatrix K e=restrictMatrix K e := by
  have hi := MonoidAlgebra.mapDomain_injective (R := ℂ) (f := (K.subtype : K→G)) Subtype.val_injective
  have hh : (restrictMatrix K e * restrictMatrix K e).map (MonoidAlgebra.mapDomainRingHom ℂ K.subtype)=
      (restrictMatrix K e).map (MonoidAlgebra.mapDomainRingHom ℂ K.subtype) := by
    rw [Matrix.map_mul,restrictMatrix_map K e hs,he]
  apply Matrix.ext
  intro i j
  apply hi
  exact congrFun (congrFun hh i) j

lemma map_trace_restrict (K : Subgroup G) (e : Paths.GroupMatrix (G := G) (ι := ι))
    (hs : ∀s∈Paths.support e,s∈K) :
    MonoidAlgebra.mapDomainRingHom ℂ K.subtype (Matrix.trace (restrictMatrix K e))=Matrix.trace e := by
  simp only [Matrix.trace,Matrix.diag,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (congrFun (restrictMatrix_map K e hs) i) i

lemma classCoefficient_map_subgroup (K : Subgroup G) (a : MonoidAlgebra ℂ K) (g : G) :
    classCoefficient g (MonoidAlgebra.mapDomainRingHom ℂ K.subtype a)=
      a.coeff.sum (fun h z=>if IsConj (h : G) g then z else 0) := by
  unfold classCoefficient
  rw [MonoidAlgebra.mapDomainRingHom_apply,MonoidAlgebra.coeff_mapDomain]
  apply Finsupp.sum_mapDomain_index
  · intro h; simp
  · intro h z w; split_ifs <;> simp

end BassTrace

end

end OAI
