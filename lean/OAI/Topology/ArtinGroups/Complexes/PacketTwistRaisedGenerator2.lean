import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ClosedNeighborhood

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J P : Type u} [Fintype I] [Fintype J] [Fintype P]
  [DecidableEq I] [DecidableEq J] [DecidableEq P]

theorem packetTwist_raised_generator_top_at_local_cap
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    {l : ℤ} (U:Set V)
    (hE : ∀ i, (E.placement i).color∈Q.closedNeighborhood U → (E.placement i).level≤l)
    (v:P → V) (hv:∀ a,v a∈U)
    (hF : F.IsMinimal Q) (e : HomotopyEquivalence Q (E.packetTwist Q v) F)
    (j:J) (hj : (F.placement j).level=l+1)
    (hcol:(F.placement j).color∈Q.closedNeighborhood U) :
    ∃ a:P, ∃ x:I → K,
      x ∈ coefficientTopDual Q E (v a) ((F.placement j).cochain+1) ∧ x≠0 ∧
      ∀ i, (E.placement i).level≠l → x i=0 := by
  obtain ⟨x,hx,hxs,hxd⟩ := minimal_generator_dual_cycle Q (E.packetTwist Q v) F hF e j
  have hxold i : x (Sum.inr i)=0 := by
    apply hxs
    intro he
    have hl := congrArg GeneratorPlacement.level he
    change (E.placement i).level = (F.placement j).level at hl
    have hc: (E.placement i).color=(F.placement j).color := congrArg GeneratorPlacement.color he
    have hb := hE i (hc.symm ▸ hcol)
    rw [hj] at hl
    omega
  have hex : ∃ z, x z≠0 := not_forall.mp (fun h => hx (funext h))
  obtain ⟨⟨a,u⟩|i,hz⟩ := hex
  swap
  · exact (hz (hxold i)).elim
  have hp : (E.packetTwist Q v).placement (Sum.inl ⟨a,u⟩)=F.placement j :=
    Classical.not_not.mp (fun h => hz (hxs _ h))
  have hα : (F.placement j).color=v a := (congrArg GeneratorPlacement.color hp).symm
  let y : TestIndex Q E.placement (v a) → K := fun i => x (Sum.inl ⟨a,i⟩)
  have hplace (i : TestIndex Q E.placement (v a))
      (he : (E.packetTwist Q v).placement (Sum.inl ⟨a,i⟩)=F.placement j) :
      (E.placement i.1).cochain=(F.placement j).cochain+1 ∧
        Path.length i.2.val=2 ∧ (E.placement i.1).level=l := by
    have hc := congrArg GeneratorPlacement.cochain he
    have hu := congrArg GeneratorPlacement.internal he
    change (E.placement i.1).cochain-1=(F.placement j).cochain at hc
    change (E.placement i.1).internal+Path.length i.2.val=(F.placement j).internal at hu
    have hl := hE i.1 (Q.corner_target_mem_neighborhood (hv a) i.2)
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
      (testMatrix Q E.placement E.placement (v a) E.differential).transpose=0 := by
    funext i
    have hh := hxd (Sum.inl ⟨a,i⟩)
    rw [hα,Fintype.sum_sum_type,Fintype.sum_sigma] at hh
    have ht k : ((E.packetTwist Q v).differential (Sum.inl ⟨a,i⟩) (Sum.inl ⟨a,k⟩)).vertex (v a) =
        -testMatrix Q E.placement E.placement (v a) E.differential i k := by
      change (-(packetDifferential Q E.placement v E.differential) ⟨a,i⟩ ⟨a,k⟩).vertex (v a) = _
      rw [packetDifferential,Matrix.blockDiagonal'_apply_eq]
      change -(testMatrix Q E.placement E.placement (v a) E.differential i k *
        (vertexId Q (K := K) (v a)).vertex (v a)) = _
      simp [vertexId_eval]
    have htne b (hb:b≠a) (k:TestIndex Q E.placement (v b)) :
        ((E.packetTwist Q v).differential (Sum.inl ⟨a,i⟩) (Sum.inl ⟨b,k⟩)).vertex (v a)=0 := by
      change (-(packetDifferential Q E.placement v E.differential) ⟨a,i⟩ ⟨b,k⟩).vertex (v a) = _
      rw [packetDifferential,Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hb),neg_zero]
      rfl
    rw [Finset.sum_eq_single a] at hh
    · simp only [ht,hxold,MulZeroClass.mul_zero,Finset.sum_const_zero,add_zero,
        neg_mul,Finset.sum_neg_distrib,neg_eq_zero] at hh
      simpa only [Matrix.vecMul,Matrix.transpose_apply,dotProduct,mul_comm,Pi.zero_apply] using hh
    · intro b hb hba
      simp only [htne b hba,MulZeroClass.zero_mul,Finset.sum_const_zero]
    · simp
  have hy : y ∈ topTestCycles Q E (v a) ((F.placement j).cochain+1) := ⟨hys,hyd⟩
  refine ⟨a,sumTokenTest Q E.placement (v a) y, sumTokenTest_top Q E (v a) _ hy, ?_, ?_⟩
  · intro hzero
    have hyz : y=0 := by
      rw [← tokenTestVector_sum Q E.placement (v a) _ y hys,hzero,map_zero]
    exact hz (congrFun hyz u)
  · intro i hi
    apply Finset.sum_eq_zero
    intro z hz
    apply hxs
    intro he
    exact hi (hplace ⟨i,z⟩ he).2.2

theorem packetTwist_local_cap_of_top_zero
    (E : BasedComplex Q (K := K) I) (hmin : E.IsMinimal Q) {l : ℤ}
    (U:Set V)
    (hE : ∀ i, (E.placement i).color∈Q.closedNeighborhood U → (E.placement i).level≤l)
    (v:P → V) (hv:∀ a,v a∈U)
    (htop : ∀ a c, coefficientTopDual Q (E.pureLayer Q hmin l) (v a) c=⊥) :
    ∃ F : FiniteModel.{u} Q (K := K), F.complex.IsMinimal Q ∧
      Nonempty (HomotopyEquivalence Q (E.packetTwist Q v) F.complex) ∧
      ∀ j, (F.complex.placement j).color∈Q.closedNeighborhood U →
        (F.complex.placement j).level≤l := by
  let B := FiniteModel.ofComplex Q (E.packetTwist Q v)
  obtain ⟨F,hF,⟨e⟩,f,hf⟩ := B.exists_minimal_embedding Q
  refine ⟨F,hF,⟨e⟩,?_⟩
  intro j hcol
  by_contra hb
  have hj : (F.complex.placement j).level=l+1 := by
    have hmax : (F.complex.placement j).level≤l+1 := by
      rw [hf j] at hcol ⊢
      change ((E.packetTwist Q v).placement (f j)).color∈Q.closedNeighborhood U at hcol
      change ((E.packetTwist Q v).placement (f j)).level≤l+1
      generalize he:f j=k at hcol ⊢
      rcases k with ⟨a,i,p⟩|i
      · change ((E.placement i).cochain-1)+((E.placement i).internal+Path.length p.val)≤l+1
        have hh := hE i (Q.corner_target_mem_neighborhood (hv a) p)
        have hr : Path.length p.val≤2 := by
          rcases Path.length_cases p.val with h|h|h <;> omega
        dsimp only [GeneratorPlacement.level] at hh
        omega
      · have hh := hE i hcol
        change (E.placement i).level≤l+1
        omega
    omega
  obtain ⟨a,x,hx,hxz,hs⟩ := packetTwist_raised_generator_top_at_local_cap Q E F.complex U hE v hv hF e j hj hcol
  have hm := coefficientTopDual_restrict_layer Q E hmin l (v a) _ hx hs
  have hn := coefficientTopDual_restrict_layer_ne_zero Q E l hxz hs
  rw [htop] at hm
  exact hn ((Submodule.mem_bot K).mp hm)

theorem classPacketPerm_local_cap_of_top_zero
    (hn:∀ a,Q.source a≠Q.target a) (v:P→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) {l:ℤ}
    (hcap:ClassCapOn Q x (Q.closedNeighborhood U) l) (hU:∀ a,v a∈U)
    (htop:∀ a c,classLayerTopDimension Q l (v a) c x=0) :
    ClassCapOn Q (classPacketPerm Q hn v hv x) (Q.closedNeighborhood U) l := by
  let E:=minimalClassModel Q x
  have hE:E.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  have ht:∀ a c,coefficientTopDual Q (E.complex.pureLayer Q hE l) (v a) c=⊥ := by
    intro a c
    exact Submodule.finrank_eq_zero.mp (htop a c)
  obtain ⟨F,hF,⟨e⟩,hb⟩:=packetTwist_local_cap_of_top_zero Q E.complex hE U hcap v hU ht
  have hh:ClassCapOn Q (classOfComplex Q F.complex) (Q.closedNeighborhood U) l :=
    minimal_bound_transport Q F.complex _ (minimalClassModel_minimal Q _)
      (minimalClassModelEquivalence Q F.complex).symm (fun p=>p.color∈Q.closedNeighborhood U→p.level≤l) hb
  have hx:classPacketPerm Q hn v hv x=classOfComplex Q F.complex := by
    rw [← minimalClassModel_class Q x,classPacketPerm_apply]
    exact classOfComplex_eq Q e
  rw [hx]
  exact hh

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
