import Mathlib
import OAI.Topology.ArtinGroups.Complexes.MinimalModelEquivalence

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open Matrix

attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L:Type u} [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]
  {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma cone_homotopy_degree11 (f:Map Q E F)
    (H:Matrix (I⊕J) (I⊕J) (Q.Zigzag K))
    (hH:MapDegree Q (f.cone Q).placement (f.cone Q).placement (-1) 0 H) :
    MapDegree Q E.placement E.placement (-1) 0 H.toBlocks₁₁ := by
  intro i j
  refine ⟨?_,(hH (.inl i) (.inl j)).2⟩
  intro h
  apply (hH (.inl i) (.inl j)).1
  change (E.placement j).cochain-1≠(E.placement i).cochain-1+(-1)
  omega

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma cone_homotopy_degree22 (f:Map Q E F)
    (H:Matrix (I⊕J) (I⊕J) (Q.Zigzag K))
    (hH:MapDegree Q (f.cone Q).placement (f.cone Q).placement (-1) 0 H) :
    MapDegree Q F.placement F.placement (-1) 0 H.toBlocks₂₂ :=
  fun i j=>hH (.inr i) (.inr j)

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma cone_homotopy_degree21 (f:Map Q E F)
    (H:Matrix (I⊕J) (I⊕J) (Q.Zigzag K))
    (hH:MapDegree Q (f.cone Q).placement (f.cone Q).placement (-1) 0 H) :
    MapDegree Q F.placement E.placement 0 0 H.toBlocks₂₁ := by
  intro i j
  refine ⟨?_,(hH (.inr i) (.inl j)).2⟩
  intro h
  apply (hH (.inr i) (.inl j)).1
  change (E.placement j).cochain-1≠(F.placement i).cochain+(-1)
  omega

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma through_absent_level_zero {C:BasedComplex Q (K:=K) I}
    (D:BasedComplex Q (K:=K) J) (f:Map Q C D) (g:Map Q D C)
    (q:ℤ) (hD:∀ j,(D.placement j).level≠q)
    (i k:I) (hi:(C.placement i).level=q) (hk:(C.placement k).level=q) :
    (f.matrix*g.matrix) i k=0 := by
  apply Finset.sum_eq_zero
  intro j _
  change f.matrix i j*g.matrix j k=0
  by_cases hf:f.matrix i j=0
  · rw [hf,zero_mul]
  by_cases hg:g.matrix j k=0
  · rw [hg,mul_zero]
  have hl:=map_level_bound Q f i j hf
  have hu:=map_level_bound Q g j k hg
  exact (hD j (by omega)).elim

omit [Fintype V] [DecidableEq A] in
lemma cone_identity_blocks (f:Map Q E F) :
    projectiveIdentity Q (K:=K) (f.cone Q).placement=
      Matrix.fromBlocks (projectiveIdentity Q E.placement) 0 0
        (projectiveIdentity Q F.placement) := by
  apply Matrix.ext
  intro i j
  rcases i with i|i <;> rcases j with j|j <;> simp [projectiveIdentity,Matrix.diagonal,Map.cone,Map.conePlacement]

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma cone_homotopy_source_block (f:Map Q E F)
    (H:Matrix (I⊕J) (I⊕J) (Q.Zigzag K)) :
    ((f.cone Q).differential*H+H*(f.cone Q).differential).toBlocks₁₁=
      -(E.differential*H.toBlocks₁₁+H.toBlocks₁₁*E.differential)+f.matrix*H.toBlocks₂₁ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks H]
  change ((Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential)*
      Matrix.fromBlocks H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂+
    Matrix.fromBlocks H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂*
      Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential).toBlocks₁₁=_
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
  change (-E.differential*H.toBlocks₁₁+f.matrix*H.toBlocks₂₁)+
    (H.toBlocks₁₁*(-E.differential)+H.toBlocks₁₂*(0 : Matrix J I (Q.Zigzag K)))=_
  simp only [Matrix.mul_zero,add_zero,Matrix.neg_mul,Matrix.mul_neg]
  abel

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma cone_homotopy_target_block (f:Map Q E F)
    (H:Matrix (I⊕J) (I⊕J) (Q.Zigzag K)) :
    ((f.cone Q).differential*H+H*(f.cone Q).differential).toBlocks₂₂=
      (F.differential*H.toBlocks₂₂+H.toBlocks₂₂*F.differential)+H.toBlocks₂₁*f.matrix := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks H]
  change ((Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential)*
      Matrix.fromBlocks H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂+
    Matrix.fromBlocks H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂*
      Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential).toBlocks₂₂=_
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
  change ((0 : Matrix J I (Q.Zigzag K))*H.toBlocks₁₂+F.differential*H.toBlocks₂₂)+
    (H.toBlocks₂₁*f.matrix+H.toBlocks₂₂*F.differential)=_
  simp only [Matrix.zero_mul,zero_add]
  abel

omit [Fintype V] [DecidableEq A] in
lemma cone_layer_inverse_equations (f:Map Q E F) (hE:E.IsMinimal Q) (hF:F.IsMinimal Q)
    (D:BasedComplex Q (K:=K) L) (e:HomotopyEquivalence Q (f.cone Q) D)
    (q:ℤ) (hD:∀ j,(D.placement j).level≠q-1 ∧ (D.placement j).level≠q) :
    atLevel Q E.placement F.placement f.matrix q *
      atLevel Q F.placement E.placement (-e.sourceHomotopy.toBlocks₂₁) q=
        projectiveIdentity Q (E.pureLayer Q hE q).placement ∧
    atLevel Q F.placement E.placement (-e.sourceHomotopy.toBlocks₂₁) q *
      atLevel Q E.placement F.placement f.matrix q=
        projectiveIdentity Q (F.pureLayer Q hF q).placement := by
  have hdeg:=cone_homotopy_degree21 Q f e.sourceHomotopy e.sourceDegree
  have hb:∀ i j,e.sourceHomotopy.toBlocks₂₁ i j≠0→
      (E.placement j).level≤(F.placement i).level := by
    intro i j hij
    simpa using mapDegree_level_bound Q hdeg hij
  have hs:=congrArg (fun m=>atLevel Q E.placement E.placement m.toBlocks₁₁ q) e.sourceEquation
  have ht:=congrArg (fun m=>atLevel Q F.placement F.placement m.toBlocks₂₂ q) e.sourceEquation
  have hz₁:atLevel Q E.placement E.placement
      (e.forward.matrix*e.backward.matrix).toBlocks₁₁ q=0 := by
    apply Matrix.ext
    intro i j
    apply through_absent_level_zero Q D e.forward e.backward (q-1) (fun k=>(hD k).1) (.inl i.val) (.inl j.val)
    · change (E.placement i.val).cochain-1+(E.placement i.val).internal=q-1
      have hh:=i.property; dsimp [GeneratorPlacement.level] at hh; omega
    · change (E.placement j.val).cochain-1+(E.placement j.val).internal=q-1
      have hh:=j.property; dsimp [GeneratorPlacement.level] at hh; omega
  have hz₂:atLevel Q F.placement F.placement
      (e.forward.matrix*e.backward.matrix).toBlocks₂₂ q=0 := by
    apply Matrix.ext
    intro i j
    exact through_absent_level_zero Q D e.forward e.backward q (fun k=>(hD k).2)
      (.inr i.val) (.inr j.val) i.property j.property
  rw [hz₁] at hs
  rw [hz₂] at ht
  change 0=atLevel Q E.placement E.placement
    ((projectiveIdentity Q (f.cone Q).placement).toBlocks₁₁+
      ((f.cone Q).differential*e.sourceHomotopy+
        e.sourceHomotopy*(f.cone Q).differential).toBlocks₁₁) q at hs
  change 0=atLevel Q F.placement F.placement
    ((projectiveIdentity Q (f.cone Q).placement).toBlocks₂₂+
      ((f.cone Q).differential*e.sourceHomotopy+
        e.sourceHomotopy*(f.cone Q).differential).toBlocks₂₂) q at ht
  rw [cone_identity_blocks,Matrix.toBlocks_fromBlocks₁₁,cone_homotopy_source_block,
    atLevel_add,atLevel_add,atLevel_identity] at hs
  rw [cone_identity_blocks,Matrix.toBlocks_fromBlocks₂₂,cone_homotopy_target_block,
    atLevel_add,atLevel_add,atLevel_identity] at ht
  have he₁:=atLevel_homotopy_boundary Q E hE e.sourceHomotopy.toBlocks₁₁
    (cone_homotopy_degree11 Q f _ e.sourceDegree) q
  have he₂:=atLevel_homotopy_boundary Q F hF e.sourceHomotopy.toBlocks₂₂
    (cone_homotopy_degree22 Q f _ e.sourceDegree) q
  change 0=projectiveIdentity Q _+(-atLevel Q E.placement E.placement
    (E.differential*e.sourceHomotopy.toBlocks₁₁+e.sourceHomotopy.toBlocks₁₁*E.differential) q+
      atLevel Q E.placement E.placement (f.matrix*e.sourceHomotopy.toBlocks₂₁) q) at hs
  rw [he₁,neg_zero,zero_add,atLevel_mul Q _ _ _ _ _ q (map_level_bound Q f) hb] at hs
  rw [he₂,zero_add,atLevel_mul Q _ _ _ _ _ q hb (map_level_bound Q f)] at ht
  have hn : atLevel Q F.placement E.placement (-e.sourceHomotopy.toBlocks₂₁) q =
      -atLevel Q F.placement E.placement e.sourceHomotopy.toBlocks₂₁ q := by
    apply Matrix.ext
    intro i j
    rfl
  rw [hn]
  constructor
  ·
    rw [Matrix.mul_neg]
    exact (neg_eq_iff_eq_neg).mpr (eq_neg_of_add_eq_zero_right hs.symm)
  ·
    rw [Matrix.neg_mul]
    exact (neg_eq_iff_eq_neg).mpr (eq_neg_of_add_eq_zero_right ht.symm)

noncomputable def Map.inverseMatrix (f:Map Q E F) (g:Matrix J I (Q.Zigzag K))
    (hg:ProjectiveEntries Q F.placement E.placement g)
    (hd:MapDegree Q F.placement E.placement 0 0 g)
    (hfg:f.matrix*g=projectiveIdentity Q E.placement)
    (hgf:g*f.matrix=projectiveIdentity Q F.placement) : Map Q F E where
  matrix:=g
  entries:=hg
  degree:=hd
  commute:=by
    calc
      F.differential*g=(projectiveIdentity Q F.placement*F.differential)*g := by
        exact congrArg (fun m=>m*g) (projectiveIdentity_mul Q F.entries).symm
      _=((g*f.matrix)*F.differential)*g := by rw [hgf]
      _=(g*(f.matrix*F.differential))*g := by simp only [Matrix.mul_assoc]
      _=(g*(E.differential*f.matrix))*g := by rw [f.commute]
      _=(g*E.differential)*(f.matrix*g) := by simp only [Matrix.mul_assoc]
      _=(g*E.differential)*projectiveIdentity Q E.placement :=
        congrArg (fun m=>(g*E.differential)*m) hfg
      _=g*E.differential := mul_projectiveIdentity Q (projectiveEntries_mul Q hg E.entries)

noncomputable def coneLayerIsomorphism (f:Map Q E F) (hE:E.IsMinimal Q) (hF:F.IsMinimal Q)
    (D:BasedComplex Q (K:=K) L) (e:HomotopyEquivalence Q (f.cone Q) D)
    (q:ℤ) (hD:∀ j,(D.placement j).level≠q-1 ∧ (D.placement j).level≠q) :
    ChainIsomorphism Q (E.pureLayer Q hE q) (F.pureLayer Q hF q) := by
  let a:=f.pureLayer Q hE hF q
  let b:=atLevel Q F.placement E.placement (-e.sourceHomotopy.toBlocks₂₁) q
  have he:ProjectiveEntries Q F.placement E.placement e.sourceHomotopy.toBlocks₂₁ :=
    ⟨fun i j=>e.sourceEntries.1 (.inr i) (.inl j),
      fun i j=>e.sourceEntries.2 (.inr i) (.inl j)⟩
  have heb:=projectiveEntries_neg Q he
  have hb:ProjectiveEntries Q (F.pureLayer Q hF q).placement
      (E.pureLayer Q hE q).placement b :=
    ⟨fun i j=>heb.1 i.val j.val,fun i j=>heb.2 i.val j.val⟩
  have hdeg:=mapDegree_neg Q (cone_homotopy_degree21 Q f _ e.sourceDegree)
  have hd:MapDegree Q (F.pureLayer Q hF q).placement
      (E.pureLayer Q hE q).placement 0 0 b :=fun i j=>hdeg i.val j.val
  have hh:=cone_layer_inverse_equations Q f hE hF D e q hD
  exact ⟨a,a.inverseMatrix Q b hb hd hh.1 hh.2,hh.1,hh.2⟩

omit [Fintype V] [DecidableEq A] in
theorem classLayer_eq_of_cone_gap (f:Map Q E F) (hE:E.IsMinimal Q) (hF:F.IsMinimal Q)
    (D:BasedComplex Q (K:=K) L) (e:HomotopyEquivalence Q (f.cone Q) D)
    (q:ℤ) (hD:∀ j,(D.placement j).level≠q-1 ∧ (D.placement j).level≠q) :
    classLayer Q q (classOfComplex Q E)=classLayer Q q (classOfComplex Q F) := by
  rw [classLayer_minimal Q E hE,classLayer_minimal Q F hF]
  exact Quotient.sound ⟨(coneLayerIsomorphism Q f hE hF D e q hD).toHomotopyEquivalence Q⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
