import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ClosedNeighborhood

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open Matrix
open scoped BigOperators

variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I : Type u} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem highest_local_generator_test_not_exact
    (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (U:Set V) (i:I)
    (hiU:(E.placement i).color∈U)
    (hcap:∀ j,(E.placement j).color∈Q.closedNeighborhood U → (E.placement j).level≤(E.placement i).level)
    (hfirst:∀ j,(E.placement j).color∈Q.closedNeighborhood U → (E.placement j).level=(E.placement i).level→
      (E.placement i).cochain≤(E.placement j).cochain) :
    ¬ ScalarExactAt Q (E.testComplex Q (E.placement i).color) (E.placement i).color
      ((E.placement i).level+2) (E.placement i).cochain := by
  classical
  let α:=(E.placement i).color
  let T:=E.testComplex Q α
  let t:TestIndex Q E.placement α:=generatorTokenTest Q E i
  let D:=testMatrix Q E.placement E.placement α E.differential
  have ht:Path.length t.2.val=2:=rfl
  have hcol:∀ u,D u t=0 := by
    intro u
    by_contra hm
    have hm':(T.differential u t).vertex α≠0 := by
      change ((D u t) • vertexId Q (K:=K) α).vertex α≠0
      simpa [vertexId_eval] using hm
    obtain ⟨_,_,hc,hu⟩:=degree_vertex_support Q T.entries T.degree u t α hm'
    change (E.placement i).cochain=(E.placement u.1).cochain+1 at hc
    change (E.placement i).internal+2=
      (E.placement u.1).internal+Path.length u.2.val+0 at hu
    have hmem := Q.corner_target_mem_neighborhood hiU u.2
    have hh:=hcap u.1 hmem
    rcases hp:u.2.val with v|a|v
    · have hl:Path.length u.2.val=0:=by rw [hp]; rfl
      dsimp only [GeneratorPlacement.level] at hh
      omega
    · have hl:Path.length u.2.val=1:=by rw [hp]; rfl
      have he:(E.placement u.1).level=(E.placement i).level := by
        dsimp only [GeneratorPlacement.level]; omega
      have hm:=hfirst u.1 hmem he
      omega
    · exact hm (test_token_row_zero Q E hE α u t (by rw [hp]; rfl))
  intro he
  change ScalarExactAt Q T α ((E.placement i).level+2) (E.placement i).cochain at he
  let x:TestIndex Q E.placement α→K:=Pi.single t 1
  have hxs:ScalarSupported Q T ((E.placement i).level+2) (E.placement i).cochain x := by
    intro u hu
    have hut:u≠t := by
      intro hh
      subst u
      apply hu
      constructor
      · change (E.placement i).cochain+((E.placement i).internal+2)=
          (E.placement i).cochain+(E.placement i).internal+2
        omega
      · rfl
    exact Pi.single_eq_of_ne hut _
  have hxd:Matrix.vecMul x (T.differential.map (vertexHom Q α))=0 := by
    rw [testComplex_vertex_differential Q E α]
    funext u
    change (∑ v,x v * D v u)=0
    rw [Finset.sum_eq_single t]
    · exact mul_eq_zero.mpr (Or.inr (test_token_row_zero Q E hE α t u ht))
    · intro v hv hvt
      rw [show x v=0 from Pi.single_eq_of_ne hvt _,MulZeroClass.zero_mul]
    · simp
  obtain ⟨z,hzs,hzd⟩:=he x hxs hxd
  have hh:=congrFun hzd t
  rw [testComplex_vertex_differential Q E α] at hh
  have hz:Matrix.vecMul z D t=0 := by
    apply Finset.sum_eq_zero
    intro u hu
    exact mul_eq_zero.mpr (Or.inr (hcol u))
  change Matrix.vecMul z D t=x t at hh
  rw [hz] at hh
  have hx:x t=1:=Pi.single_eq_same _ _
  rw [hx] at hh
  exact zero_ne_one hh

omit [DecidableEq I] in
theorem local_generatorBound_of_test_and_boundary
    (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (U:Set V) (d:ℤ)
    (h:TestUpperBound Q E U (d+2))
    (hout:∀ i,(E.placement i).color∈Q.closedNeighborhood U →
      (E.placement i).color∉U → (E.placement i).level≤d) :
    ∀ i,(E.placement i).color∈U → (E.placement i).level≤d := by
  classical
  intro i hiU
  by_contra hi
  let G:Finset I:=Finset.univ.filter (fun k=>(E.placement k).color∈U)
  have hiG:i∈G := by simp [G,hiU]
  obtain ⟨j,hj,hmax⟩:=Finset.exists_max_image G
    (fun j:I=>(E.placement j).level) ⟨i,hiG⟩
  have hm:∀ k,(E.placement k).color∈U → (E.placement k).level≤(E.placement j).level:=
    fun k hk=>hmax k (by simp [G,hk])
  let F:=G.filter (fun k:I=>(E.placement k).level=(E.placement j).level)
  have hjF:j∈F:=by simp [F,hj]
  obtain ⟨k,hk,hmin⟩:=Finset.exists_min_image F (fun k:I=>(E.placement k).cochain) ⟨j,hjF⟩
  have hlev:(E.placement k).level=(E.placement j).level:= (Finset.mem_filter.mp hk).2
  have hkd:d<(E.placement k).level := by have hh:=hm i hiU; omega
  have hku:(E.placement k).color∈U :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
  apply highest_local_generator_test_not_exact Q E hE U k hku
  · intro z hz
    by_cases hzU:(E.placement z).color∈U
    · rw [hlev]; exact hm z hzU
    · have hh:=hout z hz hzU; omega
  · intro z hz hzlev
    have hzU:(E.placement z).color∈U := by
      by_contra hzU
      have hh:=hout z hz hzU
      omega
    exact hmin z (by simp [F,G,hzU,hzlev,hlev])
  · exact h (E.placement k).color hku ((E.placement k).level+2) (by omega)
      (E.placement k).cochain

lemma classCapOn_of_test_and_boundary (x : FiniteHomotopyClass Q (K:=K))
    (U:Set V) (d:ℤ) (h:ClassTestUpper Q x U (d+2))
    (hb:ClassCapOn Q x (Q.closedNeighborhood U \ U) d) : ClassCapOn Q x U d := by
  let E:=minimalClassModel Q x
  have hx : (⟦E⟧:FiniteHomotopyClass Q (K:=K))=x := minimalClassModel_class Q x
  have ht : TestUpperBound Q E.complex U (d+2) := by
    rw [← classTestUpper_model,hx]; exact h
  exact local_generatorBound_of_test_and_boundary Q E.complex
    (minimalClassModel_minimal Q x) U d ht (fun i hi hni=>hb i ⟨hi,hni⟩)

lemma classPositiveNegative_cancel (hn:∀ a,Q.source a≠Q.target a)
    (x:FiniteHomotopyClass Q (K:=K)) (α:V) :
    classPositiveTwist Q α (classNegativeTwist Q α x)=x :=
  (classTwistPerm Q hn α).apply_symm_apply x

lemma classTestExact_negative_self (hn:∀ a,Q.source a≠Q.target a)
    (x:FiniteHomotopyClass Q (K:=K)) (α:V) (l c:ℤ) :
    ClassTestExact Q α l c (classNegativeTwist Q α x) ↔
      ClassTestExact Q α (l+1) (c-1) x := by
  have h:=classTestExact_positive_self Q hn (classNegativeTwist Q α x) α (l+1) (c-1)
  rw [classPositiveNegative_cancel Q hn] at h
  simpa only [add_sub_cancel_right,sub_add_cancel] using h.symm

lemma classNegativeTwist_testUpper (hn:∀ a,Q.source a≠Q.target a)
    (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (α:V) (hα:α∈U) {t:ℤ}
    (h:ClassTestUpper Q x U t) : ClassTestUpper Q (classNegativeTwist Q α x) U t := by
  apply classPositiveTwist_testUpper_reflect Q hn _ U α hα
  simpa only [classPositiveNegative_cancel Q hn] using h

lemma inverseWord_testUpper (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) {t:ℤ}
    (h:ClassTestUpper Q x U t) (hw:∀ α∈w,α∈U) :
    ClassTestUpper Q (inverseWordAction Q w x) U t := by
  induction w generalizing x with
  | nil => exact h
  | cons α w ih =>
    exact ih _ (classNegativeTwist_testUpper Q hn x U α (hw α (by simp)) h)
      (fun β hβ=>hw β (by simp [hβ]))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
