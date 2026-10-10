import Mathlib
import OAI.Topology.ArtinGroups.Quivers.CornerScalar
import OAI.Topology.ArtinGroups.Quivers.LengthCases
import OAI.Topology.ArtinGroups.Quivers.TokenTestVector

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype V] [DecidableEq A] in
lemma high_dual_cycle_zero (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (e:HomotopyEquivalence Q E F) (α:V) (l:ℤ)
    (hE:∀ i,(E.placement i).level≤l) (hF:∀ j,(F.placement j).level<l)
    (x:I→K) (hx:∀ i,(E.placement i).level≠l ∨ (E.placement i).color≠α → x i=0)
    (hd:(E.differential.map (vertexHom Q α)).mulVec x=0) : x=0 := by
  let f:=e.forward.matrix.map (vertexHom Q α)
  let b:=e.backward.matrix.map (vertexHom Q α)
  let h:=e.sourceHomotopy.map (vertexHom Q α)
  let dE:=E.differential.map (vertexHom Q α)
  have hb:b.mulVec x=0 := by
    funext j
    apply Finset.sum_eq_zero
    intro i _
    change (e.backward.matrix j i).vertex α*x i=0
    by_cases hm:(e.backward.matrix j i).vertex α=0
    · rw [hm,MulZeroClass.zero_mul]
    obtain ⟨_,_,hc,hu⟩:=degree_vertex_support Q e.backward.entries e.backward.degree j i α hm
    have hi:(E.placement i).level≠l := by
      have hj:=hF j
      dsimp only [GeneratorPlacement.level] at *
      omega
    rw [hx i (Or.inl hi),MulZeroClass.mul_zero]
  have hh:h.mulVec x=0 := by
    funext j
    apply Finset.sum_eq_zero
    intro i _
    change (e.sourceHomotopy j i).vertex α*x i=0
    by_cases hm:(e.sourceHomotopy j i).vertex α=0
    · rw [hm,MulZeroClass.zero_mul]
    obtain ⟨_,_,hc,hu⟩:=degree_vertex_support Q e.sourceEntries e.sourceDegree j i α hm
    have hi:(E.placement i).level≠l := by
      have hj:=hE j
      dsimp only [GeneratorPlacement.level] at *
      omega
    rw [hx i (Or.inl hi),MulZeroClass.mul_zero]
  have hid:((projectiveIdentity Q E.placement).map (vertexHom Q α)).mulVec x=x := by
    funext i
    simp only [Matrix.mulVec,Matrix.map_apply,dotProduct,projectiveIdentity,Matrix.diagonal_apply]
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left rfl]
      change (vertexId Q (E.placement i).color).vertex α*x i=x i
      by_cases hi:(E.placement i).color=α
      · simp [hi,vertexId_eval]
      · rw [hx i (Or.inr hi),MulZeroClass.mul_zero]
    · intro j _ hj
      simp [Ne.symm hj,vertexHom]
    · simp
  have he:f*b=(projectiveIdentity Q E.placement).map (vertexHom Q α)+dE*h+h*dE := by
    simpa only [Matrix.map_mul,Matrix.map_add _ (map_add _),← add_assoc] using congrArg
      (fun M:Matrix I I (Q.Zigzag K)=>M.map (vertexHom Q α)) e.sourceEquation
  have hz:=congrArg (fun M:Matrix I I K=>M.mulVec x) he
  rw [← Matrix.mulVec_mulVec, hb,Matrix.mulVec_zero,Matrix.add_mulVec,Matrix.add_mulVec,
    hid,← Matrix.mulVec_mulVec,hh,Matrix.mulVec_zero,← Matrix.mulVec_mulVec,hd,
    Matrix.mulVec_zero,_root_.add_zero,_root_.add_zero] at hz
  exact hz.symm

theorem positiveTwist_top_zero_of_cap
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (q:ℤ) (hE:∀ i,(E.placement i).level=q) (α:V)
    (e:HomotopyEquivalence Q (E.positiveTwist Q α) F)
    (hF:∀ j,(F.placement j).level≤q) :
    ∀ c,coefficientTopDual Q E α c=⊥ := by
  intro c
  apply eq_bot_iff.mpr
  intro x hx
  change x=0
  let t:=tokenTestVector Q E.placement α x
  have ht:t∈topTestCycles Q E α c:=tokenTestVector_top Q E hE α c hx
  let y:TestIndex Q E.placement α⊕I→K:=Sum.elim t (fun _=>0)
  have hy:y=0 := by
    apply high_dual_cycle_zero Q (E.positiveTwist Q α) F e α (q+1)
    · intro i
      rcases i with i|i
      · change (E.placement i.1).cochain-1+((E.placement i.1).internal+Path.length i.2.val)≤q+1
        have hi:=hE i.1
        have hl:Path.length i.2.val≤2:=by rcases Path.length_cases i.2.val with h|h|h <;> omega
        dsimp only [GeneratorPlacement.level] at hi
        omega
      · change (E.placement i).level≤q+1
        rw [hE]; omega
    · intro j
      have hj:=hF j
      omega
    · intro i hi
      rcases i with i|i
      · change t i=0
        apply ht.1
        intro hh
        apply hi.elim
        · intro h
          apply h
          change (E.placement i.1).cochain-1+((E.placement i.1).internal+Path.length i.2.val)=q+1
          have hq:=hE i.1
          dsimp only [GeneratorPlacement.level] at hq
          omega
        · intro h
          exact h rfl
      · rfl
    · funext i
      rcases i with i|i
      · change (∑ j:TestIndex Q E.placement α⊕I,
          ((E.positiveTwist Q α).differential (.inl i) j).vertex α*y j)=0
        rw [Fintype.sum_sum_type]
        have hh:=congrFun ht.2 i
        change (∑ j,t j * testMatrix Q E.placement E.placement α E.differential i j)=0 at hh
        simp only [y,Sum.elim_inl,Sum.elim_inr,MulZeroClass.mul_zero,Finset.sum_const_zero,_root_.add_zero]
        have hm j:((E.positiveTwist Q α).differential (.inl i) (.inl j)).vertex α =
            -testMatrix Q E.placement E.placement α E.differential i j := by
          change (-((testMatrix Q E.placement E.placement α E.differential i j) • vertexId Q α)).vertex α=_
          change -(testMatrix Q E.placement E.placement α E.differential i j *
            (vertexId Q (K:=K) α).vertex α) = _
          rw [vertexId_eval,ite_eq_left rfl,_root_.mul_one]
        simp only [hm,_root_.neg_mul,Finset.sum_neg_distrib]
        rw [show (∑ j,testMatrix Q E.placement E.placement α E.differential i j*t j)=0 from by
          simpa only [_root_.mul_comm] using hh,_root_.neg_zero]
      · change (∑ j:TestIndex Q E.placement α⊕I,
          ((E.positiveTwist Q α).differential (.inr i) j).vertex α*y j)=0
        rw [Fintype.sum_sum_type]
        simp [y,BasedComplex.positiveTwist,Map.cone,Map.coneDifferential,Matrix.fromBlocks]
  have ht0:t=0:=funext fun i=>congrFun hy (.inl i)
  have hr:=sumTokenTest_unit Q E.placement α x (fun i hi=>hx.1 i (Or.inl hi))
  change sumTokenTest Q E.placement α t=x at hr
  rw [ht0,map_zero] at hr
  exact hr.symm

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
