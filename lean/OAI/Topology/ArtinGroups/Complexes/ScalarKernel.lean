import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PlacedProjective
import OAI.Topology.ArtinGroups.Complexes.Shift

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def ScalarKernel {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (f:Map Q E F) (x:I→K) : Prop := ∀ j β,∑ i,x i*(f.matrix i j).vertex β=0

def PlacementSupported (E:BasedComplex Q (K:=K) I) (α:V) (c:ℤ) (x:I→K) : Prop :=
  ∀ i,(E.placement i).color≠α ∨ (E.placement i).cochain≠c→x i=0

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma differential_arrow_right_support (E:BasedComplex Q (K:=K) I) (i j:I) (a:A)
    (h:(E.placement j).color≠Q.target a) : (E.differential i j).arrow a=0 := by
  have hh:=congrArg (fun z:Q.Zigzag K=>z.arrow a) (E.entries.2 i j)
  simpa only [arrow_mul,Pi.add_apply,leftScale,rightScale,arrow_vertexId,Pi.zero_apply,
    MulZeroClass.mul_zero,zero_add,vertexId_eval,ite_eq_right h.symm,MulZeroClass.mul_zero] using hh.symm

noncomputable def coefficientOutgoing (E:BasedComplex Q (K:=K) I) (x:I→K) (a:A) : I→K :=
  fun j=>∑ i,x i*(E.differential i j).arrow a

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma coefficientOutgoing_support (E:BasedComplex Q (K:=K) I) (α:V) (c:ℤ)
    {x:I→K} (hx:PlacementSupported Q E α c x) (a:A) :
    PlacementSupported Q E (Q.target a) (c+1) (coefficientOutgoing Q E x a) := by
  intro j hj
  apply Finset.sum_eq_zero
  intro i _
  rcases hj with hj|hj
  · rw [differential_arrow_right_support Q E i j a hj,MulZeroClass.mul_zero]
  · by_cases hi:(E.placement i).cochain=c
    · rw [(E.degree i j).1 (by omega)]
      exact MulZeroClass.mul_zero _
    · rw [hx i (Or.inr hi),MulZeroClass.zero_mul]

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma ScalarKernel.outgoing {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    {f:Map Q E F} (hf:CoefficientMatrix Q f.matrix) {x:I→K} (hx:ScalarKernel Q f x)
    (a:A) : ScalarKernel Q f (coefficientOutgoing Q E x a) := by
  intro j β
  by_cases hb:β=(F.placement j).color
  · subst β
    by_cases hja:(F.placement j).color=Q.target a
    · rw [hja]
      have hh (i:I) := congrArg (fun M:Matrix I J (Q.Zigzag K)=>(M i j).arrow a) f.commute
      simp only [Matrix.mul_apply,arrow_sum,Finset.sum_apply,arrow_mul,Pi.add_apply,
        leftScale,rightScale,(hf _ _).1,Pi.zero_apply,MulZeroClass.mul_zero,
        MulZeroClass.zero_mul,zero_add,add_zero] at hh
      change ∑ k,(∑ i,x i*(E.differential i k).arrow a)*(f.matrix k j).vertex (Q.target a)=0
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [_root_.mul_assoc,← Finset.mul_sum,hh,Finset.mul_sum,← _root_.mul_assoc]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro k _
      rw [hx k (Q.source a),MulZeroClass.zero_mul]
    · apply Finset.sum_eq_zero
      intro i _
      by_cases hc:(E.placement i).color=Q.target a
      · have he:(f.matrix i j).vertex (F.placement j).color=0 := by
          by_contra he
          have hs:=reduction_support Q f.entries f.degree i j _ he
          exact hja (hs.1 ▸ hc)
        rw [he,MulZeroClass.mul_zero]
      · have hz:coefficientOutgoing Q E x a i=0 := by
          apply Finset.sum_eq_zero
          intro k _
          rw [differential_arrow_right_support Q E k i a hc,MulZeroClass.mul_zero]
        rw [hz,MulZeroClass.zero_mul]
  · apply Finset.sum_eq_zero
    intro i _
    rw [entry_vertex_right_support Q f.entries i j β hb,MulZeroClass.mul_zero]

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma ScalarKernel.project {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    {f:Map Q E F} {x:I→K} (hx:ScalarKernel Q f x) (p:GeneratorPlacement V) :
    ScalarKernel Q f (fun i=>if E.placement i=p then x i else 0) := by
  intro j β
  by_cases hj:F.placement j=p
  · convert hx j β using 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp only
    by_cases hi:E.placement i=p
    · rw [ite_eq_left hi]
    · rw [ite_eq_right hi,MulZeroClass.zero_mul]
      have hz:(f.matrix i j).vertex β=0 := by
        by_contra hz
        exact hi ((reduction_support Q f.entries f.degree i j β hz).1.trans hj)
      rw [hz,MulZeroClass.mul_zero]
  · apply Finset.sum_eq_zero
    intro i _
    dsimp only
    by_cases hi:E.placement i=p
    · rw [ite_eq_left hi]
      have hz:(f.matrix i j).vertex β=0 := by
        by_contra hz
        exact hj ((reduction_support Q f.entries f.degree i j β hz).1.symm.trans hi)
      rw [hz,MulZeroClass.mul_zero]
    · rw [ite_eq_right hi,MulZeroClass.zero_mul]

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma scalarKernel_has_socle {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    {f:Map Q E F} (hf:CoefficientMatrix Q f.matrix) {x:I→K}
    (hx:ScalarKernel Q f x) (hx0:x≠0) :
    ∃ α c y,y∈coefficientSocle Q E α c ∧ y≠0 ∧ ScalarKernel Q f y := by
  let S:Finset I:=Finset.univ.filter fun i=>∃ y:I→K,
    PlacementSupported Q E (E.placement i).color (E.placement i).cochain y ∧
      y≠0 ∧ ScalarKernel Q f y
  have hs:S.Nonempty := by
    obtain ⟨i,hi⟩:∃ i,x i≠0 := by
      by_contra h
      push Not at h
      exact hx0 (funext h)
    let y:I→K:=fun j=>if E.placement j=E.placement i then x j else 0
    refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,y,?_,?_,hx.project Q _⟩⟩
    · intro j hj
      have he:E.placement j≠E.placement i := by intro he; simp only [he,ne_self_iff_false,or_self] at hj
      exact ite_eq_right he
    · intro hz
      have hh:=congrFun hz i
      apply hi
      simpa only [y,ite_eq_left rfl,Pi.zero_apply] using hh
  obtain ⟨i,hi,hmax⟩:=Finset.exists_max_image S (fun i=>(E.placement i).cochain) hs
  obtain ⟨y,hy,hy0,hyker⟩:=(Finset.mem_filter.mp hi).2
  refine ⟨(E.placement i).color,(E.placement i).cochain,y,⟨hy,?_⟩,hy0,hyker⟩
  intro j a _
  have hz:coefficientOutgoing Q E y a=0 := by
    by_contra hz
    obtain ⟨t,ht⟩:∃ t,coefficientOutgoing Q E y a t≠0 := by
      by_contra h
      push Not at h
      exact hz (funext h)
    have hsupp:=coefficientOutgoing_support Q E _ _ hy a
    have hc:(E.placement t).color=Q.target a :=
      Classical.not_not.mp (fun hn=>ht (hsupp t (Or.inl hn)))
    have hd:(E.placement t).cochain=(E.placement i).cochain+1 :=
      Classical.not_not.mp (fun hn=>ht (hsupp t (Or.inr hn)))
    have htS:t∈S := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,coefficientOutgoing Q E y a,?_,hz,hyker.outgoing Q hf a⟩
      simpa only [hc,hd] using hsupp
    have hh:=hmax t htS
    omega
  exact congrFun hz j

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
theorem pureMap_scalarKernel_zero (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    {q:ℤ} (hE:∀ i,(E.placement i).level=q) (hF:∀ j,(F.placement j).level=q)
    (f:Map Q E F)
    (hm:∀ T:FiniteModel.{u} Q (K:=K),ClassUpperBound Q q (classOfComplex Q T.complex)→
      HomMonoFrom Q T.complex f)
    {x:I→K} (hx:ScalarKernel Q f x) : x=0 := by
  by_contra hx0
  obtain ⟨α,c,y,hy,hy0,hyk⟩:=scalarKernel_has_socle Q (pureMap_coefficient Q f q hE hF) hx hx0
  let p:GeneratorPlacement V:=⟨α,c,q-c⟩
  let P:=placedProjective Q (K:=K) p
  have hP:∀ i,(P.placement i).level=q := by intro i; change c+(q-c)=q; omega
  let z:PUnit.{u+1}→K:=fun _=>1
  have hz:z∈coefficientTopDual Q P α c := by
    constructor
    · intro i hi
      exact (hi.elim (fun h=>h rfl) (fun h=>h rfl)).elim
    · intro i a
      change ∑ j:PUnit.{u+1},(0:K)*z j=0
      simp only [MulZeroClass.zero_mul,Finset.sum_const_zero]
  let g:=topSocleMatrix Q α z y
  have hg:g∈homCycles Q P E 0 0 := by
    simpa only [sub_self] using topSocleMatrix_mem_homCycles Q P E hP hE α c c hz hy
  have hg':g*f.matrix∈homCycles Q P F 0 0 := by
    simpa only [zero_add] using homCycles_mul Q hg (map_mem_homCycles Q f)
  have hco:CoefficientMatrix Q (g*f.matrix):=
    pure_homSpace_coefficient Q P F hP hF (by omega) hg'.1
  have hzero:g*f.matrix=0 := by
    apply Matrix.ext
    intro i j
    apply coefficient_row_zero Q hg'.1.1 hco i _ j
    intro j
    change (∑ k,g i k*f.matrix k j).vertex α=0
    simp only [vertex_sum,Finset.sum_apply,g,topSocleMatrix,vertex_mul,vertex_smul,
      Pi.mul_apply,Pi.smul_apply,smul_eq_mul,vertexId_eval,_root_.mul_one,z,_root_.one_mul,ite_true,eq_self]
    exact hyk j α
  have hmono:=derivedMono_postcompose_injective Q P E F hP hE (n:=0) (v:=0) (by omega) f hm
  have hgzero:(⟨g,hg⟩:homCycles Q P E 0 0)=0 := by
    apply hmono
    apply Subtype.ext
    change g*f.matrix=(0:Matrix PUnit.{u+1} I (Q.Zigzag K))*f.matrix
    rw [Matrix.zero_mul]
    exact hzero
  exact topSocleMatrix_ne_zero Q α (by intro h; have hh:=congrFun h PUnit.unit; exact one_ne_zero hh) hy0
    (congrArg Subtype.val hgzero)

noncomputable def Map.scalarMatrix {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (f:Map Q E F) : Matrix I J K := fun i j=>(f.matrix i j).vertex (F.placement j).color

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma map_vertex_source_eq_target {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (f:Map Q E F) (i:I) (j:J) :
    (f.matrix i j).vertex (E.placement i).color=f.scalarMatrix Q i j := by
  by_cases h:(E.placement i).color=(F.placement j).color
  · exact congrArg _ h
  · rw [entry_vertex_right_support Q f.entries i j _ h]
    exact (entry_vertex_left_support Q f.entries i j _ (Ne.symm h)).symm

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma map_coefficient_entry {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (f:Map Q E F) (hf:CoefficientMatrix Q f.matrix) (i:I) (j:J) :
    f.matrix i j=f.scalarMatrix Q i j •vertexId Q (E.placement i).color := by
  apply ext
  · funext β
    simp only [vertex_smul,Pi.smul_apply,smul_eq_mul,vertexId_eval]
    by_cases hb:β=(E.placement i).color
    · subst β
      rw [ite_eq_left rfl,_root_.mul_one]
      exact map_vertex_source_eq_target Q f i j
    · rw [ite_eq_right hb,MulZeroClass.mul_zero]
      exact entry_vertex_left_support Q f.entries i j _ hb
  · simpa only [arrow_smul,arrow_vertexId,smul_zero] using (hf i j).1
  · simpa only [token_smul,token_vertexId,smul_zero] using (hf i j).2

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma scalarKernel_of_vecMul_zero {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (f:Map Q E F) {x:I→K} (hx:Matrix.vecMul x (f.scalarMatrix Q)=0) : ScalarKernel Q f x := by
  intro j β
  by_cases hb:β=(F.placement j).color
  · subst β
    exact congrFun hx j
  · apply Finset.sum_eq_zero
    intro i _
    rw [entry_vertex_right_support Q f.entries i j _ hb,MulZeroClass.mul_zero]

omit [Fintype V] [DecidableEq A] in
theorem pureMap_termwiseSplit (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    {q:ℤ} (hE:∀ i,(E.placement i).level=q) (hF:∀ j,(F.placement j).level=q)
    (f:Map Q E F)
    (hm:∀ T:FiniteModel.{u} Q (K:=K),ClassUpperBound Q q (classOfComplex Q T.complex)→
      HomMonoFrom Q T.complex f) :
    ∃ g:TermwiseSplitInjection Q E F,g.inclusion=f := by
  let R:=f.scalarMatrix Q
  have hk:LinearMap.ker R.toLinearMapRight'=⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    exact pureMap_scalarKernel_zero Q E F hE hF f hm (scalarKernel_of_vecMul_zero Q f hx)
  obtain ⟨s,hs⟩:=LinearMap.exists_leftInverse_of_injective R.toLinearMapRight' hk
  let S:=s.toMatrixRight'
  have hRS:R*S=1 := by
    have hh:=congrArg LinearMap.toMatrixRight' hs
    simpa only [LinearMap.toMatrixRight'_comp,LinearMap.toMatrixRight'_id,
      LinearEquiv.apply_symm_apply] using hh
  let g:Matrix J I (Q.Zigzag K):=fun j i=>S j i •(1:Q.Zigzag K)
  refine ⟨⟨f,g,?_⟩,rfl⟩
  apply Matrix.ext
  intro i j
  change ∑ k,f.matrix i k*g k j=projectiveIdentity Q E.placement i j
  simp_rw [map_coefficient_entry Q f (pureMap_coefficient Q f q hE hF)]
  simp only [g,smul_mul_smul_comm,_root_.mul_one,← Finset.sum_smul]
  have hij:=congrArg (fun N:Matrix I I K=>N i j) hRS
  change (∑ k,f.scalarMatrix Q i k*S k j)=(1:Matrix I I K) i j at hij
  rw [hij]
  by_cases he:i=j
  · subst j
    simp only [Matrix.one_apply_eq,one_smul,projectiveIdentity,Matrix.diagonal_apply_eq]
  · simp only [Matrix.one_apply_ne he,zero_smul,projectiveIdentity,Matrix.diagonal_apply_ne _ he]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
