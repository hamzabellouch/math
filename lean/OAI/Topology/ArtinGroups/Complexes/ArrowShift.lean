import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.BraidCoreFirstTarget
import OAI.Topology.ArtinGroups.Complexes.TokenShift

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def arrowShift (E:BasedComplex Q (K:=K) I) : BasedComplex Q (K:=K) I where
  placement i := ⟨(E.placement i).color,(E.placement i).cochain-1,(E.placement i).internal+1⟩
  differential := -E.differential
  entries := projectiveEntries_neg Q E.entries
  degree i j := by
    constructor
    · intro h
      change -E.differential i j=0
      rw [(E.degree i j).1 (by dsimp only at h; omega),neg_zero]
    · change Homogeneous Q (0+((E.placement i).internal+1)-((E.placement j).internal+1)) (-E.differential i j)
      convert homogeneous_neg Q (E.degree i j).2 using 1; omega
  square_zero := by rw [Matrix.neg_mul,Matrix.mul_neg,neg_neg,E.square_zero]

abbrev AdjacentTestIndex (E:BasedComplex Q (K:=K) I) (α β:V) :=
  TestIndex Q E.placement β ⊕ TestIndex Q E.placement β ⊕
    TestIndex Q E.placement β ⊕ TestIndex Q E.placement β ⊕ TestIndex Q E.placement α

noncomputable def adjacentTestIndexEquiv (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β) :
    AdjacentTestIndex Q E α β ≃
      TestIndex Q ((E.positiveTwist Q β).positiveTwist Q α).placement β where
  toFun
    | .inl u => ⟨.inr (.inl u),selfCornerEquiv Q hn β false⟩
    | .inr (.inl u) => ⟨.inr (.inr u.1),u.2⟩
    | .inr (.inr (.inl u)) => ⟨.inl ⟨.inl u,e.corner Q⟩,(e.reverse Q).corner Q⟩
    | .inr (.inr (.inr (.inl u))) => ⟨.inr (.inl u),selfCornerEquiv Q hn β true⟩
    | .inr (.inr (.inr (.inr u))) => ⟨.inl ⟨.inr u.1,u.2⟩,(e.reverse Q).corner Q⟩
  invFun
    | ⟨.inl ⟨.inl u,_⟩,_⟩ => .inr (.inr (.inl u))
    | ⟨.inl ⟨.inr i,p⟩,_⟩ => .inr (.inr (.inr (.inr ⟨i,p⟩)))
    | ⟨.inr (.inl u),p⟩ => if (selfCornerEquiv Q hn β).symm p then
        .inr (.inr (.inr (.inl u))) else .inl u
    | ⟨.inr (.inr i),p⟩ => .inr (.inl ⟨i,p⟩)
  left_inv u := by rcases u with u|u|u|u|u <;> rfl
  right_inv u := by
    rcases u with ⟨⟨u|i,p⟩|(u|i),q⟩
    · have hp:p=e.corner Q:=e.corner_unique Q p
      have hq:q=(e.reverse Q).corner Q := (e.reverse Q).corner_unique Q q
      cases hp; cases hq; rfl
    · have hq:q=(e.reverse Q).corner Q := (e.reverse Q).corner_unique Q q
      cases hq; rfl
    · have he:=(selfCornerEquiv Q hn β).apply_symm_apply q
      cases h:(selfCornerEquiv Q hn β).symm q
      · simp only [h,Bool.false_eq_true,↓reduceIte]
        congr 1
        change (selfCornerEquiv Q hn β false : Zigzag.CornerPath Q β β)=q
        simpa only [h] using he
      · simp only [h,↓reduceIte]
        congr 1
        change (selfCornerEquiv Q hn β true : Zigzag.CornerPath Q β β)=q
        simpa only [h] using he
    · rfl

noncomputable def normalizedAdjacentTest (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β) :=
  (((E.positiveTwist Q β).positiveTwist Q α).testComplex Q β).reindex Q
    (adjacentTestIndexEquiv Q hn E e)

lemma adjacentTest_first_pivot_entry (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β)
    (u v:TestIndex Q E.placement β) :
    (normalizedAdjacentTest Q hn E e).differential (.inl u) (.inr (.inl v))=
      projectiveIdentity Q (testPlacement Q E.placement β) u v := by
  exact normalizedTestTwist_pivot_entry Q hn E β u v

noncomputable def adjacentTestFirstPivot (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β) :
    BlockPivot Q (normalizedAdjacentTest Q hn E e) where
  coefficient := 1
  nonzero := one_ne_zero
  color _ := rfl
  cochain i := by change (E.placement i.1).cochain=(E.placement i.1).cochain-1+1; omega
  internal i := by
    change (E.placement i.1).internal+Path.length i.2.val=
      (E.placement i.1).internal+Path.length i.2.val+0
    omega
  entry i j := by rw [adjacentTest_first_pivot_entry]; simp only [one_smul]; rfl

omit [DecidableEq I] in
lemma adjacentTest_first_source_retained (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β)
    (u:TestIndex Q E.placement β)
    (v:TestIndex Q E.placement β ⊕ TestIndex Q E.placement β ⊕ TestIndex Q E.placement α) :
    (normalizedAdjacentTest Q hn E e).differential (.inl u) (.inr (.inr v))=0 := by
  rcases v with v|v|v
  · change (pathCoordinates Q (K:=K) (_ * 0) _) • vertexId Q β=0
    rw [MulZeroClass.mul_zero,coordinates_zero,zero_smul]
  · exact normalizedTestTwist_unit_token Q hn E β u v
  · change (pathCoordinates Q (K:=K) (_ * 0) _) • vertexId Q β=0
    rw [MulZeroClass.mul_zero,coordinates_zero,zero_smul]

lemma adjacentTest_first_reduced_entry (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β)
    (u v:TestIndex Q E.placement β ⊕ TestIndex Q E.placement β ⊕ TestIndex Q E.placement α) :
    ((adjacentTestFirstPivot Q hn E e).reduced Q).differential u v=
      (normalizedAdjacentTest Q hn E e).differential (.inr (.inr u)) (.inr (.inr v)) := by
  rw [BlockPivot.reduced_differential]
  simp only [adjacentTest_first_source_retained,MulZeroClass.mul_zero,Finset.sum_const_zero,sub_zero]

omit [DecidableEq I] in
lemma adjacentTest_second_pivot_entry (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β)
    (u v:TestIndex Q E.placement β) :
    (normalizedAdjacentTest Q hn E e).differential
      (.inr (.inr (.inl u))) (.inr (.inr (.inr (.inl v))))=
      projectiveIdentity Q (testPlacement Q E.placement β) u v := by
  change (pathCoordinates Q (K:=K) (pathBasis Q (e.reverse Q).corner.val *
    evaluationMatrix Q (E.positiveTwist Q β).placement α ⟨.inl u,e.corner Q⟩ (.inl v))
      (Sum.inr (Sum.inr β))) • vertexId Q β=_
  simp only [evaluationMatrix,SimpleEdge.corner_val,pathBasis_arrow,
    Sum.inl.injEq,projectiveIdentity,Matrix.diagonal_apply,testPlacement,
    SimpleEdge.reverse_arrow]
  by_cases h:u=v
  · simp only [ite_eq_left h]
    have harr : arrowBasis Q (K:=K) (Q.reverse e.arrow) * arrowBasis Q e.arrow=tokenBasis Q β := by
      simpa only [Q.reverse_reverse,Q.source_reverse,e.target] using
        (arrowBasis_reverse Q (K:=K) (Q.reverse e.arrow))
    rw [harr]
    rw [← pathBasis_token,pathBasis_coordinates,ite_eq_left rfl,one_smul]
  · simp only [ite_eq_right h,MulZeroClass.mul_zero,coordinates_zero,zero_smul]

noncomputable def adjacentTestSecondPivot (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β) :
    BlockPivot Q ((adjacentTestFirstPivot Q hn E e).reduced Q) where
  coefficient := 1
  nonzero := one_ne_zero
  color _ := rfl
  cochain u := by
    change (E.placement u.1).cochain-1=(E.placement u.1).cochain-1-1+1
    omega
  internal u := by
    change (E.placement u.1).internal+Path.length u.2.val+2=
      (E.placement u.1).internal+Path.length u.2.val+1+1
    omega
  entry u v := by
    rw [adjacentTest_first_reduced_entry,adjacentTest_second_pivot_entry]
    simp only [one_smul]
    rfl

omit [DecidableEq I] in
lemma adjacentTest_retained_to_second_target (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β)
    (u:TestIndex Q E.placement α) (v:TestIndex Q E.placement β) :
    (normalizedAdjacentTest Q hn E e).differential
      (.inr (.inr (.inr (.inr u)))) (.inr (.inr (.inr (.inl v))))=0 := by
  change (pathCoordinates Q (K:=K) (_ * evaluationMatrix Q (E.positiveTwist Q β).placement α
    ⟨.inr u.1,u.2⟩ (.inl v)) _) • vertexId Q β=0
  simp only [evaluationMatrix,Sum.inr_ne_inl,↓reduceIte,MulZeroClass.mul_zero,coordinates_zero,zero_smul]

omit [DecidableEq I] in
lemma adjacentTest_retained_entry (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β)
    (u v:TestIndex Q E.placement α) :
    (normalizedAdjacentTest Q hn E e).differential
      (.inr (.inr (.inr (.inr u)))) (.inr (.inr (.inr (.inr v))))=
      -(testMatrix Q E.placement E.placement α E.differential u v • vertexId Q (K:=K) β) := by
  change (pathCoordinates Q (K:=K) (pathBasis Q (e.reverse Q).corner.val *
    (-(testMatrix Q E.placement E.placement α E.differential u v • vertexId Q (K:=K) α)))
      (e.reverse Q).corner.val) • vertexId Q β=_
  rw [_root_.mul_neg,mul_smul,cornerPath_right]
  simp only [map_neg,Pi.neg_apply,coordinates_smul,pathBasis_coordinates,ite_true,
    _root_.mul_one,neg_smul]

lemma adjacentTest_second_reduced_differential (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β)
    (u v:TestIndex Q E.placement α) :
    ((adjacentTestSecondPivot Q hn E e).reduced Q).differential u v=
      -(testMatrix Q E.placement E.placement α E.differential u v • vertexId Q (K:=K) β) := by
  rw [BlockPivot.reduced_differential]
  simp only [adjacentTest_first_reduced_entry,adjacentTest_retained_to_second_target,
    smul_zero,MulZeroClass.zero_mul,Finset.sum_const_zero,sub_zero,adjacentTest_retained_entry]

noncomputable def adjacentTestReduction (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β) :
    HomotopyEquivalence Q (((E.positiveTwist Q β).positiveTwist Q α).testComplex Q β)
      ((adjacentTestSecondPivot Q hn E e).reduced Q) :=
  ((((E.positiveTwist Q β).positiveTwist Q α).testComplex Q β).reindexHomotopyEquivalence Q
    (adjacentTestIndexEquiv Q hn E e)).trans Q
      (((adjacentTestFirstPivot Q hn E e).reductionEquivalence Q).trans Q
        ((adjacentTestSecondPivot Q hn E e).reductionEquivalence Q))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
