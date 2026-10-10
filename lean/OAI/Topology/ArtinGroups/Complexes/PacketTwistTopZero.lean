import Mathlib
import OAI.Topology.ArtinGroups.Complexes.UpperBound
import OAI.Topology.ArtinGroups.Complexes.HighDualCycleZero

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J P:Type u} [Fintype I] [Fintype J] [Fintype P]
  [DecidableEq I] [DecidableEq J] [DecidableEq P]

theorem packetTwist_top_zero_of_cap
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (q:ℤ) (hE:∀ i,(E.placement i).level=q) (v:P→V)
    (e:HomotopyEquivalence Q (E.packetTwist Q v) F)
    (hF:∀ j,(F.placement j).level≤q) :
    ∀ a c,coefficientTopDual Q E (v a) c=⊥ := by
  intro a c
  apply eq_bot_iff.mpr
  intro x hx
  change x=0
  let t:=tokenTestVector Q E.placement (v a) x
  have ht:t∈topTestCycles Q E (v a) c:=tokenTestVector_top Q E hE (v a) c hx
  let z':∀ b:P,TestIndex Q E.placement (v b)→K:=Pi.single a t
  let z:PacketIndex Q E.placement v→K:=fun b=>z' b.1 b.2
  let y:PacketIndex Q E.placement v⊕I→K:=Sum.elim z (fun _=>0)
  have hz:∀ (b:P) (i:TestIndex Q E.placement (v b)),b≠a→z ⟨b,i⟩=0 := by
    intro b i h
    simp [z,z',Pi.single_eq_of_ne h]
  have hza:∀ i,z ⟨a,i⟩=t i := by intro i; simp [z,z']
  have hy:y=0 := by
    apply high_dual_cycle_zero Q (E.packetTwist Q v) F e (v a) (q+1)
    · intro i
      rcases i with ⟨b,i⟩|i
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
      rcases i with ⟨b,i⟩|i
      · change z ⟨b,i⟩=0
        by_cases hb:b=a
        · subst b
          rw [hza]
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
        · exact hz b i hb
      · rfl
    · funext i
      rcases i with ⟨b,i⟩|i
      · change (∑ j:PacketIndex Q E.placement v⊕I,
          ((E.packetTwist Q v).differential (.inl ⟨b,i⟩) j).vertex (v a)*y j)=0
        rw [Fintype.sum_sum_type]
        simp only [y,Sum.elim_inl,Sum.elim_inr,MulZeroClass.mul_zero,Finset.sum_const_zero,_root_.add_zero]
        rw [Fintype.sum_sigma,Finset.sum_eq_single a]
        · simp only [hza]
          by_cases hb:b=a
          · subst b
            have hh:=congrFun ht.2 i
            change (∑ j,t j * testMatrix Q E.placement E.placement (v a) E.differential i j)=0 at hh
            have hm j:((E.packetTwist Q v).differential (.inl ⟨a,i⟩) (.inl ⟨a,j⟩)).vertex (v a) =
                -testMatrix Q E.placement E.placement (v a) E.differential i j := by
              change (-packetDifferential Q E.placement v E.differential ⟨a,i⟩ ⟨a,j⟩).vertex (v a)=_
              rw [packetDifferential,Matrix.blockDiagonal'_apply_eq]
              change -(testMatrix Q E.placement E.placement (v a) E.differential i j *
                (vertexId Q (K:=K) (v a)).vertex (v a)) = _
              rw [vertexId_eval,ite_eq_left rfl,_root_.mul_one]
            simp only [hm,_root_.neg_mul,Finset.sum_neg_distrib]
            rw [show (∑ j,testMatrix Q E.placement E.placement (v a) E.differential i j*t j)=0 from by
              simpa only [_root_.mul_comm] using hh,_root_.neg_zero]
          · apply Finset.sum_eq_zero
            intro j _
            change (-packetDifferential Q E.placement v E.differential ⟨b,i⟩ ⟨a,j⟩).vertex (v a)*t j=0
            rw [packetDifferential,Matrix.blockDiagonal'_apply_ne _ _ _ hb]
            simp
        · intro b hb hba
          apply Finset.sum_eq_zero
          intro j _
          rw [hz b j hba,MulZeroClass.mul_zero]
        · simp
      · change (∑ j:PacketIndex Q E.placement v⊕I,
          ((E.packetTwist Q v).differential (.inr i) j).vertex (v a)*y j)=0
        rw [Fintype.sum_sum_type]
        simp [y,BasedComplex.packetTwist,Map.cone,Map.coneDifferential,Matrix.fromBlocks]
  have ht0:t=0:=funext fun i=>by simpa only [y,Sum.elim_inl,hza,Pi.zero_apply] using congrFun hy (.inl ⟨a,i⟩)
  have hr:=sumTokenTest_unit Q E.placement (v a) x (fun i hi=>hx.1 i (Or.inl hi))
  change sumTokenTest Q E.placement (v a) t=x at hr
  rw [ht0,map_zero] at hr
  exact hr.symm

theorem classPacketPerm_top_zero_of_layer_cap
    (hn:∀ a,Q.source a≠Q.target a) (v:P→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hh:ClassUpperBound Q q (classPacketPerm Q hn v hv (classLayer Q q x))) :
    ∀ a c,classLayerTopDimension Q q (v a) c x=0 := by
  let E:=(minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) q
  let y:=classPacketPerm Q hn v hv (classLayer Q q x)
  let F:=(minimalClassModel Q y).complex
  have he:classOfComplex Q (E.packetTwist Q v)=classOfComplex Q F := by
    have hp:=classPacketPerm_apply Q hn v hv (FiniteModel.ofComplex Q E)
    change classPacketPerm Q hn v hv (classOfComplex Q E)=
      classOfComplex Q (E.packetTwist Q v) at hp
    rw [← hp]
    exact (minimalClassModel_class Q y).symm
  obtain ⟨e⟩:=Quotient.exact he
  have ht:=packetTwist_top_zero_of_cap Q E F q (fun i=>i.property) v e hh
  intro a c
  change Module.finrank K (coefficientTopDual Q E (v a) c)=0
  rw [ht,finrank_bot]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
