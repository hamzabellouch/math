import Mathlib
import OAI.Topology.ArtinGroups.Complexes.CoconePlacement
import OAI.Topology.ArtinGroups.Quivers.TestIndex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I]

def twistNewTestIndex (E:BasedComplex Q (K:=K) I) (α β:V)
    (p:Zigzag.CornerPath Q β α) (u:TestIndex Q E.placement α) :
    TestIndex Q (E.positiveTwist Q α).placement β := ⟨Sum.inl u,p⟩

def twistOldTestIndex (E:BasedComplex Q (K:=K) I) (α β:V)
    (u:TestIndex Q E.placement β) :
    TestIndex Q (E.positiveTwist Q α).placement β := ⟨Sum.inr u.1,u.2⟩

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma corner_other_length {α β:V} (hne:β≠α) (p:Zigzag.CornerPath Q β α) :
    Path.length p.val=1 := by
  obtain ⟨p,hp,hq⟩:=p
  rcases p with v|a|v
  · exact (hne (hp.symm.trans hq)).elim
  · rfl
  · exact (hne (hp.symm.trans hq)).elim

lemma twistTest_new_differential
    (E:BasedComplex Q (K:=K) I) (α β:V)
    (y:TestIndex Q (E.positiveTwist Q α).placement β→K)
    (p:Zigzag.CornerPath Q β α) (v:TestIndex Q E.placement α) :
    Matrix.vecMul y (testMatrix Q (E.positiveTwist Q α).placement
      (E.positiveTwist Q α).placement β (E.positiveTwist Q α).differential)
      (twistNewTestIndex Q E α β p v) =
    -Matrix.vecMul (fun u=>y (twistNewTestIndex Q E α β p u))
      (testMatrix Q E.placement E.placement α E.differential) v := by
  classical
  change (∑ z:TestIndex Q (E.positiveTwist Q α).placement β,
    y z * pathCoordinates Q (pathBasis Q z.2.val *
      (E.positiveTwist Q α).differential z.1 (Sum.inl v)) p.val)=_
  rw [Fintype.sum_sigma,Fintype.sum_sum_type]
  dsimp only
  have ho:(∑ i:I,∑ z:Zigzag.CornerPath Q β (E.placement i).color,
      y ⟨Sum.inr i,z⟩ * pathCoordinates Q
      (pathBasis Q z.val * (E.positiveTwist Q α).differential (Sum.inr i) (Sum.inl v)) p.val)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro z hz
    change _ * pathCoordinates Q (_ * 0) _=0
    rw [MulZeroClass.mul_zero,coordinates_zero,MulZeroClass.mul_zero]
  have he := congrArg (fun a:K =>
    (∑ u:TestIndex Q E.placement α,∑ z:Zigzag.CornerPath Q β α,
      y ⟨Sum.inl u,z⟩ * pathCoordinates Q (pathBasis Q z.val *
      (E.positiveTwist Q α).differential (Sum.inl u) (Sum.inl v)) p.val) + a) ho
  apply he.trans
  rw [add_zero]
  rw [show -Matrix.vecMul (fun u=>y (twistNewTestIndex Q E α β p u))
      (testMatrix Q E.placement E.placement α E.differential) v =
      ∑ u, -(y (twistNewTestIndex Q E α β p u) *
      testMatrix Q E.placement E.placement α E.differential u v) by
        exact (Finset.sum_neg_distrib _).symm]
  apply Finset.sum_congr rfl
  intro u hu
  change (∑ z:Zigzag.CornerPath Q β α,y ⟨Sum.inl u,z⟩ *
    pathCoordinates Q (pathBasis Q z.val *
      (-(testMatrix Q E.placement E.placement α E.differential u v • vertexId Q (K:=K) α))) p.val)=_
  simp only [_root_.mul_neg,mul_smul,cornerPath_right,map_neg,map_smul,
    pathBasis_coordinates,Pi.neg_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_eq_single p]
  · simp [twistNewTestIndex]
  · intro z hz hzp
    rw [ite_eq_right (fun equality=>hzp (Subtype.ext equality))]
    simp
  · simp

lemma twistTest_old_differential
    (E:BasedComplex Q (K:=K) I) (α β:V)
    (y:TestIndex Q (E.positiveTwist Q α).placement β→K)
    (hy:∀ p:Zigzag.CornerPath Q β α,∀ u:TestIndex Q E.placement α,
      y (twistNewTestIndex Q E α β p u)=0)
    (v:TestIndex Q E.placement β) :
    Matrix.vecMul y (testMatrix Q (E.positiveTwist Q α).placement
      (E.positiveTwist Q α).placement β (E.positiveTwist Q α).differential)
      (twistOldTestIndex Q E α β v) =
    Matrix.vecMul (fun u=>y (twistOldTestIndex Q E α β u))
      (testMatrix Q E.placement E.placement β E.differential) v := by
  classical
  change (∑ z:TestIndex Q (E.positiveTwist Q α).placement β,
    y z * pathCoordinates Q (pathBasis Q z.2.val *
      (E.positiveTwist Q α).differential z.1 (Sum.inr v.1)) v.2.val)=_
  rw [Fintype.sum_sigma,Fintype.sum_sum_type]
  dsimp only
  have hn:(∑ u:TestIndex Q E.placement α,∑ z:Zigzag.CornerPath Q β α,
      y ⟨Sum.inl u,z⟩ * pathCoordinates Q
      (pathBasis Q z.val * (E.positiveTwist Q α).differential (Sum.inl u) (Sum.inr v.1)) v.2.val)=0 := by
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro z hz
    have hh:=hy z u
    change y ⟨Sum.inl u,z⟩=0 at hh
    rw [hh,MulZeroClass.zero_mul]
  have he := congrArg (fun a:K => a+
    (∑ i:I,∑ z:Zigzag.CornerPath Q β (E.placement i).color,
      y ⟨Sum.inr i,z⟩ * pathCoordinates Q (pathBasis Q z.val *
      (E.positiveTwist Q α).differential (Sum.inr i) (Sum.inr v.1)) v.2.val)) hn
  apply he.trans
  rw [zero_add]
  change _ = ∑ z:TestIndex Q E.placement β,
    y (twistOldTestIndex Q E α β z) *
    pathCoordinates Q (pathBasis Q z.2.val * E.differential z.1 v.1) v.2.val
  rw [Fintype.sum_sigma]
  rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
