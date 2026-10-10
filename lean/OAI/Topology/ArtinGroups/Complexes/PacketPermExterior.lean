import Mathlib
import OAI.Topology.ArtinGroups.Complexes.GeneratorArray2
import OAI.Topology.ArtinGroups.Complexes.Initial
import OAI.Topology.ArtinGroups.Complexes.PacketPermReindex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  (hn:∀ a,Q.source a≠Q.target a)

lemma classPacketPerm_exterior {J:Type u} [Fintype J] (v:J → V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K:=K)) (a:GeneratorPlacement V)
    (ha:∀ j,v j≠a.color) :
    classGeneratorArray Q (classPacketPerm Q hn v hv x) a=classGeneratorArray Q x a := by
  suffices hh:∀ (J:Type u) [Fintype J] (v:J → V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)),
    (∀ j,v j≠a.color) →
      classGeneratorArray Q (classPacketPerm Q hn v hv x) a=classGeneratorArray Q x a from
    hh J v hv ha
  intro J inst
  apply Fintype.induction_empty_option (P:=fun J _=>∀ (v:J → V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)),
    (∀ j,v j≠a.color) →
      classGeneratorArray Q (classPacketPerm Q hn v hv x) a=classGeneratorArray Q x a) _ _ _ J
  · intro J L instL e ih
    let :=Fintype.ofEquiv L e.symm
    intro v hv ha
    rw [classPacketPerm_reindex Q hn v hv e]
    exact ih _ _ (fun j=>ha (e j))
  · intro v hv ha
    rw [classPacketPerm_empty Q hn v hv]
    rfl
  · intro J instJ ih v hv ha
    rw [classPacketPerm_cons Q hn v hv]
    change classGeneratorArray Q
      (classPositiveTwist Q (v none) (classPacketPerm Q hn (v ∘ some) _ x)) a=_
    rw [classPositiveTwist_exterior Q _ _ _ (ha none)]
    exact ih _ _ (fun j=>ha (some j))

lemma classPacketPerm_inverse_exterior {J:Type u} [Fintype J] (v:J → V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K:=K)) (a:GeneratorPlacement V)
    (ha:∀ j,v j≠a.color) :
    classGeneratorArray Q ((classPacketPerm Q hn v hv).symm x) a=classGeneratorArray Q x a := by
  have h:=classPacketPerm_exterior Q hn v hv ((classPacketPerm Q hn v hv).symm x) a ha
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

omit [Fintype V] [DecidableEq A] in
lemma classLevelArray_initial (α β:V) (q:ℤ) :
    classLevelArray Q (initialClass Q (K:=K) α) (β,q)=if α=β ∧ q=0 then 1 else 0 := by
  classical
  rw [initialClass,classLevelArray_of_minimal Q _ (show (initialProjective Q α).IsMinimal Q from
    fun i j=>rfl)]
  change (initialProjective Q α).levelArray Q (β,q)=_
  rw [levelArray_eq_sum]
  simp only [initialProjective,GeneratorPlacement.level,Finset.univ_unique,
    Finset.sum_singleton,Finsupp.single_apply,Prod.mk.injEq]
  simp [eq_comm]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
