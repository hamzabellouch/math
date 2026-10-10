import Mathlib
import OAI.Topology.ArtinGroups.Complexes.ReducedAmplitudeTwistLevel
import OAI.Topology.ArtinGroups.Quivers.TokenTestVector
import OAI.Topology.ArtinGroups.Complexes.MinimalGeneratorDualCycle
import OAI.Topology.ArtinGroups.Complexes.CoefficientTopDualRestrict

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem positiveTwist_raised_generator_top_at_cap
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    {l : ℤ} (hE : ∀ i, (E.placement i).level≤l) (α:V)
    (hF : F.IsMinimal Q) (e : HomotopyEquivalence Q (E.positiveTwist Q α) F)
    (j:J) (hj : (F.placement j).level=l+1) (hα : (F.placement j).color=α) :
    ∃ x : I → K, x ∈ coefficientTopDual Q E α ((F.placement j).cochain+1) ∧ x≠0 ∧
      ∀ i, (E.placement i).level≠l → x i=0 := by
  obtain ⟨x,hx,hxs,hxd⟩ := minimal_generator_dual_cycle Q (E.positiveTwist Q α) F hF e j
  have hxold i : x (Sum.inr i)=0 := by
    apply hxs
    intro he
    have hl := congrArg GeneratorPlacement.level he
    change (E.placement i).level = (F.placement j).level at hl
    have hb := hE i
    rw [hj] at hl
    omega
  let y : TestIndex Q E.placement α → K := fun i => x (Sum.inl i)
  have hplace (i : TestIndex Q E.placement α)
      (he : (E.positiveTwist Q α).placement (Sum.inl i)=F.placement j) :
      (E.placement i.1).cochain=(F.placement j).cochain+1 ∧
        Path.length i.2.val=2 ∧ (E.placement i.1).level=l := by
    have hc := congrArg GeneratorPlacement.cochain he
    have hu := congrArg GeneratorPlacement.internal he
    change (E.placement i.1).cochain-1=(F.placement j).cochain at hc
    change (E.placement i.1).internal+Path.length i.2.val=(F.placement j).internal at hu
    have hl := hE i.1
    have hr : Path.length i.2.val≤2 := by
      rcases Path.length_cases i.2.val with h|h|h <;> omega
    dsimp only [GeneratorPlacement.level] at hl hj ⊢
    exact ⟨by omega,by omega,by omega⟩
  have hys i : ¬ ((E.placement i.1).cochain=(F.placement j).cochain+1 ∧
      Path.length i.2.val=2) → y i=0 := by
    intro hi
    apply hxs
    intro he
    exact hi ⟨(hplace i he).1,(hplace i he).2.1⟩
  have hyd : Matrix.vecMul y
      (testMatrix Q E.placement E.placement α E.differential).transpose=0 := by
    funext i
    have hh := hxd (Sum.inl i)
    rw [hα,Fintype.sum_sum_type] at hh
    have ht k : ((E.positiveTwist Q α).differential (Sum.inl i) (Sum.inl k)).vertex α =
        -testMatrix Q E.placement E.placement α E.differential i k := by
      change (-(scalarCornerMatrix Q α
        (testMatrix Q E.placement E.placement α E.differential)) i k).vertex α = _
      change -(testMatrix Q E.placement E.placement α E.differential i k *
        (vertexId Q (K := K) α).vertex α) = _
      simp [vertexId_eval]
    simp only [ht,hxold,MulZeroClass.mul_zero,Finset.sum_const_zero,add_zero,
      neg_mul,Finset.sum_neg_distrib,neg_eq_zero] at hh
    simpa only [Matrix.vecMul,Matrix.transpose_apply,dotProduct,mul_comm,Pi.zero_apply] using hh
  have hy : y ∈ topTestCycles Q E α ((F.placement j).cochain+1) := ⟨hys,hyd⟩
  refine ⟨sumTokenTest Q E.placement α y, sumTokenTest_top Q E α _ hy, ?_, ?_⟩
  · intro hz
    have hyz : y=0 := by
      rw [← tokenTestVector_sum Q E.placement α _ y hys,hz,map_zero]
    apply hx
    funext i
    rcases i with i|i
    · exact congrFun hyz i
    · exact hxold i
  · intro i hi
    apply Finset.sum_eq_zero
    intro z hz
    apply hxs
    intro he
    exact hi (hplace ⟨i,z⟩ he).2.2

theorem positiveTwist_cap_of_top_zero
    (E : BasedComplex Q (K := K) I) (hmin : E.IsMinimal Q) {l : ℤ}
    (hE : ∀ i, (E.placement i).level≤l) (α:V)
    (htop : ∀ c, coefficientTopDual Q (E.pureLayer Q hmin l) α c=⊥) :
    ∃ F : FiniteModel.{u} Q (K := K), F.complex.IsMinimal Q ∧
      Nonempty (HomotopyEquivalence Q (E.positiveTwist Q α) F.complex) ∧
      ∀ j, (F.complex.placement j).level≤l := by
  let B := FiniteModel.ofComplex Q (reducedAmplitudeTwist Q E α)
  obtain ⟨F,hF,⟨e⟩,f,hf⟩ := B.exists_minimal_embedding Q
  have reduction : HomotopyEquivalence Q (E.positiveTwist Q α)
      (reducedAmplitudeTwist Q E α) := by
    convert amplitudeTwistReduction Q E α using 1
  let e' := reduction.trans Q e
  refine ⟨F,hF,⟨e'⟩,?_⟩
  intro j
  by_contra hb
  have hloc : ∃ i:I,
      (F.complex.placement j).level=(E.placement i).level ∨
      ((F.complex.placement j).level=(E.placement i).level+1 ∧
        (F.complex.placement j).color=α) := by
    rw [hf j]
    exact reducedAmplitudeTwist_level Q E α (f j)
  obtain ⟨i,hi⟩ := hloc
  have hbound := hE i
  rcases hi with hi|⟨hi,hα⟩
  · omega
  · have hj : (F.complex.placement j).level=l+1 := by omega
    obtain ⟨x,hx,hxz,hs⟩ := positiveTwist_raised_generator_top_at_cap Q E F.complex hE α hF e' j hj hα
    have hm := coefficientTopDual_restrict_layer Q E hmin l α _ hx hs
    have hn := coefficientTopDual_restrict_layer_ne_zero Q E l hxz hs
    rw [htop] at hm
    exact hn ((Submodule.mem_bot K).mp hm)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
