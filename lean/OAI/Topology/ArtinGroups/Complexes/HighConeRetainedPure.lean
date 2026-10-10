import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PositiveTwistRaisedGenerator
import OAI.Topology.ArtinGroups.Complexes.LayerConeEquivalence
import OAI.Topology.ArtinGroups.Complexes.HighConeIndex
import OAI.Topology.ArtinGroups.Complexes.PositiveConeIndex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma top_zero_regraded (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (e:I≃J) (n:ℤ) (r:K) (hr:r≠0)
    (hc:∀ i,(F.placement (e i)).color=(E.placement i).color)
    (hd:∀ i,(F.placement (e i)).cochain=(E.placement i).cochain+n)
    (hf:∀ i j a,(F.differential (e i) (e j)).arrow a=r*(E.differential i j).arrow a)
    (α:V) (hz:∀ c,coefficientTopDual Q E α c=⊥) :
    ∀ c,coefficientTopDual Q F α c=⊥ := by
  intro c
  apply le_antisymm _ bot_le
  intro x hx
  have hy:(fun i=>x (e i))∈coefficientTopDual Q E α (c-n) := by
    constructor
    · intro i hi
      apply hx.1 (e i)
      rcases hi with hi|hi
      · exact Or.inl (by rwa [hc])
      · exact Or.inr (by rw [hd]; omega)
    · intro i a
      apply (mul_eq_zero.mp (show r*(∑ j:I,(E.differential i j).arrow a*x (e j))=0 from ?_)).resolve_left hr
      calc
        r*(∑ j:I,(E.differential i j).arrow a*x (e j))=
            ∑ j:I,(F.differential (e i) (e j)).arrow a*x (e j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [hf i j a]
          ring
        _ = ∑ j:J,(F.differential (e i) j).arrow a*x j := e.sum_comp (fun j:J=>(F.differential (e i) j).arrow a*x j)
        _ = 0 := hx.2 (e i) a
  rw [hz] at hy
  have hy':(fun i=>x (e i))=0:=(Submodule.mem_bot K).mp hy
  apply (Submodule.mem_bot K).mpr
  funext j
  obtain ⟨i,rfl⟩:=e.surjective j
  exact congrFun hy' i

omit [Fintype V] [DecidableEq A] in
lemma highConeRetained_differential (E:BasedComplex Q (K:=K) I) (T:Set I)
    (h:DownClosed Q E T) (i j:T) :
    ((highConePivot Q E T h).reduced Q).differential i j= -E.differential i j := by
  rw [BlockPivot.reduced_differential]
  have hz (k:(Tᶜ:Set I)) :
      (highConeNormalized Q E T h).differential (.inr (.inr i)) (.inr (.inl k))=0 := by
    change (highProjection Q E T h).matrix i k=0
    change (if (i:I)=(k:I) then vertexId Q (K:=K) (E.placement i).color else 0)=0
    have hne:(i:I)≠(k:I):=fun he=>k.property (he ▸ i.property)
    exact ite_eq_right hne
  simp only [hz,smul_zero,zero_mul,Finset.sum_const_zero,sub_zero]
  rfl

omit [Fintype V] [DecidableEq A] in
lemma highConeRetained_minimal (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (T:Set I) (h:DownClosed Q E T) :
    ((highConePivot Q E T h).reduced Q).IsMinimal Q := by
  intro i j
  funext α
  rw [highConeRetained_differential]
  change -(E.differential i j).vertex α=0
  have hh:=congrFun (hE i j) α
  change (E.differential i j).vertex α=0 at hh
  rw [hh,neg_zero]

noncomputable def highConeRetainedPureIndex (E:BasedComplex Q (K:=K) I)
    (hE:E.IsMinimal Q) (q:ℤ) :
    {i:I // (E.placement i).level=q-1} ≃
      {i:lowerLevelSet Q E (q-1) //
        (((highConePivot Q E _ (levelDownClosed Q E hE (q-1))).reduced Q).placement i).level=q-2} where
  toFun i:=⟨⟨i.val,le_of_eq i.property⟩,by
    rw [highConeRetained_level]
    have hi:=i.property
    change (E.placement i.val).level-1=q-2
    omega⟩
  invFun i:=⟨i.val.val,by
    have hi:=i.property
    rw [highConeRetained_level] at hi
    omega⟩
  left_inv _:=rfl
  right_inv _:=rfl

omit [Fintype V] [DecidableEq A] in
lemma highConeRetained_top_zero (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (α:V)
    (ht:∀ c,coefficientTopDual Q (E.pureLayer Q hE (q-1)) α c=⊥) :
    ∀ c,coefficientTopDual Q
      (((highConePivot Q E _ (levelDownClosed Q E hE (q-1))).reduced Q).pureLayer Q
        (highConeRetained_minimal Q E hE _ _) (q-2)) α c=⊥ := by
  apply top_zero_regraded Q (E.pureLayer Q hE (q-1)) _
    (highConeRetainedPureIndex Q E hE q) (-1) (-1) (neg_ne_zero.mpr one_ne_zero)
    (fun _=>rfl) (fun i=>by
      change (E.placement i).cochain-1=(E.placement i).cochain+ -1
      omega) _ α ht
  intro i j a
  change (((highConePivot Q E _ (levelDownClosed Q E hE (q-1))).reduced Q).differential
    (highConeRetainedPureIndex Q E hE q i).val
    (highConeRetainedPureIndex Q E hE q j).val).arrow a= -1*(E.differential i j).arrow a
  rw [highConeRetained_differential]
  change -(E.differential i j).arrow a= -1*(E.differential i j).arrow a
  ring

lemma positiveLayer_top (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (hhi:∀ i,(E.placement i).level≤q) (α:V)
    (ht:∀ c,coefficientTopDual Q (E.pureLayer Q hE (q-1)) α c=⊥) :
    classLayer Q q (classPositiveTwist Q α (classOfComplex Q E))=
      classLayer Q q (classPositiveTwist Q α (classLayer Q q (classOfComplex Q E))) := by
  let f:=highProjection Q E _ (levelDownClosed Q E hE (q-1))
  let D:=(highConePivot Q E _ (levelDownClosed Q E hE (q-1))).reduced Q
  have hd:∀ i,(D.placement i).level≤q-2 := by
    intro i
    rw [highConeRetained_level]
    have hi:=i.property
    change (E.placement i).level≤q-1 at hi
    omega
  obtain ⟨G,hG,⟨eg⟩,hg⟩:=positiveTwist_cap_of_top_zero Q D
    (highConeRetained_minimal Q E hE _ _) hd α (highConeRetained_top_zero Q E hE q α ht)
  have coneIso : ChainIsomorphism Q ((f.cone Q).positiveTwist Q α)
      ((f.positiveTwist Q α).cone Q) := by
    convert positiveTwistCone Q f α using 1
  have twistedReduction : HomotopyEquivalence Q ((f.cone Q).positiveTwist Q α)
      (D.positiveTwist Q α) := by
    convert (highConeReduction Q E _ (levelDownClosed Q E hE (q-1))).positiveTwist Q α using 1
  let e:HomotopyEquivalence Q ((f.positiveTwist Q α).cone Q) G.complex:=
    ((coneIso.toHomotopyEquivalence Q).symm Q).trans Q
      (twistedReduction.trans Q eg)
  have hh:=classLayer_eq_of_cone_equivalence Q (f.positiveTwist Q α) G.complex e q
    (fun i=>by have hi:=hg i; constructor <;> omega)
  change classLayer Q q (classPositiveTwist Q α (classOfComplex Q E))=
    classLayer Q q (classPositiveTwist Q α (classOfComplex Q (upperTruncation Q E hE (q-1)))) at hh
  rwa [highRestriction_top_eq_layer Q E hE q hhi] at hh

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
