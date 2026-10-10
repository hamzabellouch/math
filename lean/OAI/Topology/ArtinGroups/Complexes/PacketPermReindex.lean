import Mathlib
import OAI.Topology.ArtinGroups.Complexes.Sum

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  (hn : ∀ a, Q.source a ≠ Q.target a)
  {J L : Type u} [Fintype J] [Fintype L]

lemma classPacketPerm_reindex (v:J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) (e:L ≃ J) :
    classPacketPerm Q (K := K) hn v hv = classPacketPerm Q hn (v ∘ e)
      (fun _ _ hab => hv (fun he => hab (e.injective he))) := by
  classical
  apply Equiv.ext
  intro x
  induction x using Quotient.inductionOn with | _ E =>
    erw [classPacketPerm_apply,classPacketPerm_apply]
    exact classOfComplex_packet_reindex Q E.complex v e

lemma classPacketPerm_empty [IsEmpty J] (v:J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) :
    classPacketPerm Q (K := K) hn v hv = Equiv.refl _ := by
  classical
  apply Equiv.ext
  intro x
  induction x using Quotient.inductionOn with | _ E =>
    rw [classPacketPerm_apply]
    exact (classOfComplex_reindex Q _ (packetEmptyEquiv Q E.complex v)).trans
      (congrArg (classOfComplex Q) (packetEmpty_eq Q E.complex v))

lemma classPacketPerm_cons (v:Option J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) :
    classPacketPerm Q (K := K) hn v hv =
      classTwistPerm Q hn (v none) * classPacketPerm Q hn (v ∘ some)
        (fun _ _ hab => hv (fun he => hab (Option.some.inj he))) := by
  classical
  apply Equiv.ext
  intro x
  induction x using Quotient.inductionOn with | _ E =>
    change _ = classPositiveTwist Q (v none) (classPacketPerm Q hn (v ∘ some) _ ⟦E⟧)
    erw [classPacketPerm_apply,classPacketPerm_apply]
    have he : v = fun z : Option J => z.elim (v none) (v ∘ some) := by
      funext z; cases z <;> rfl
    conv_lhs => rw [he]
    convert classOfComplex_packet_cons Q E.complex (v none) (v ∘ some)
      (fun a => hv (by simp)) using 1

variable {I : Type u} [Fintype I] [DecidableEq I]
lemma classPacketPerm_sum (v:J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b))
    (x : I → FiniteHomotopyClass Q (K := K)) :
    classPacketPerm Q hn v hv (classSum Q x) =
      classSum Q (fun i => classPacketPerm Q hn v hv (x i)) := by
  classical
  suffices hh : ∀ (J : Type u) [Fintype J] (v:J → V)
      (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b)),
      classPacketPerm Q hn v hv (classSum Q x) =
        classSum Q (fun i => classPacketPerm Q hn v hv (x i)) from hh J v hv
  intro J inst
  apply Fintype.induction_empty_option (P := fun J _ => ∀ (v:J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b)),
    classPacketPerm Q hn v hv (classSum Q x) =
      classSum Q (fun i => classPacketPerm Q hn v hv (x i))) _ _ _ J
  · intro J L instL e ih
    let := Fintype.ofEquiv L e.symm
    intro v hv
    rw [classPacketPerm_reindex Q hn v hv e]
    exact ih _ _
  · intro v hv
    rw [classPacketPerm_empty Q hn v hv]
    rfl
  · intro J instJ ih v hv
    rw [classPacketPerm_cons Q hn v hv]
    change classPositiveTwist Q (v none) (classPacketPerm Q hn (v ∘ some) _ (classSum Q x)) =
      classSum Q (fun i => classPositiveTwist Q (v none) (classPacketPerm Q hn (v ∘ some) _ (x i)))
    erw [ih,classPositiveTwist_sum]

lemma classPacketPerm_inverse_sum (v:J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b))
    (x : I → FiniteHomotopyClass Q (K := K)) :
    (classPacketPerm Q hn v hv).symm (classSum Q x) =
      classSum Q (fun i => (classPacketPerm Q hn v hv).symm (x i)) := by
  apply (classPacketPerm Q hn v hv).injective
  rw [Equiv.apply_symm_apply,classPacketPerm_sum]
  simp only [Equiv.apply_symm_apply]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
