import Mathlib
import OAI.Topology.ArtinGroups.Quivers.Iso
import OAI.Topology.ArtinGroups.Complexes.PacketPermReindex
import OAI.Topology.ArtinGroups.Functors.TestIndex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag Zigzag.BasedComplex

universe u
variable {V A W B : Type u} {K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R) [Field K] [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B]
  {I : Type u} [Fintype I] [DecidableEq I]

omit [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B] [DecidableEq I] in
lemma complex_symm (E:BasedComplex Q (K := K) I) :
    e.symm.complex (e.complex E) = E := by
  apply ext_placement_differential Q
  · funext i
    change GeneratorPlacement.mk (e.vertex.symm (e.vertex (E.placement i).color))
      (E.placement i).cochain (E.placement i).internal = E.placement i
    rw [e.vertex.symm_apply_apply]
  · apply Matrix.ext
    intro i j
    apply Zigzag.ext
    · ext v
      change (E.differential i j).vertex (e.vertex.symm (e.vertex v)) = _
      rw [e.vertex.symm_apply_apply]
    · ext a
      change (E.differential i j).arrow (e.arrow.symm (e.arrow a)) = _
      rw [e.arrow.symm_apply_apply]
    · ext v
      change (E.differential i j).token (e.vertex.symm (e.vertex v)) = _
      rw [e.vertex.symm_apply_apply]

noncomputable def classMap : FiniteHomotopyClass Q (K := K) → FiniteHomotopyClass R (K := K) :=
  Quotient.map (fun E => FiniteModel.ofComplex R (e.complex E.complex)) (by
    intro E F ⟨h⟩
    exact ⟨e.homotopyEquivalence h⟩)

omit [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B] in
@[simp] lemma classMap_complex (E:BasedComplex Q (K := K) I) :
    e.classMap (classOfComplex Q E) = classOfComplex R (e.complex E) := rfl

omit [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B] in
lemma classMap_symm (x:FiniteHomotopyClass Q (K := K)) : e.symm.classMap (e.classMap x)=x := by
  induction x using Quotient.inductionOn with | _ E =>
    change classOfComplex Q (e.symm.complex (e.complex E.complex)) = classOfComplex Q E.complex
    rw [e.complex_symm]

noncomputable def classEquiv : FiniteHomotopyClass Q (K := K) ≃ FiniteHomotopyClass R (K := K) where
  toFun := e.classMap
  invFun := e.symm.classMap
  left_inv := e.classMap_symm
  right_inv := e.symm.classMap_symm

lemma classMap_positiveTwist (α:V) (x:FiniteHomotopyClass Q (K := K)) :
    e.classMap (classPositiveTwist Q α x) = classPositiveTwist R (e.vertex α) (e.classMap x) := by
  induction x using Quotient.inductionOn with | _ E =>
    change classOfComplex R (e.complex (E.complex.positiveTwist Q α)) =
      classOfComplex R ((e.complex E.complex).positiveTwist R (e.vertex α))
    rw [← e.positiveTwist_transport]
    exact (classOfComplex_reindex R _ _).symm

omit [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B] in
lemma loopless (e : Iso Q R) (hn:∀ a,Q.source a ≠ Q.target a) : ∀ b,R.source b ≠ R.target b := by
  intro b h
  apply hn (e.arrow.symm b)
  rw [e.source_symm,e.target_symm,h]

omit [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B] in
lemma orthogonal {s t:V} (h:OrthogonalVertices Q s t) :
    OrthogonalVertices R (e.vertex s) (e.vertex t) := by
  constructor
  · exact fun he => h.1 (e.vertex.injective he)
  · intro b hs ht
    apply h.2 (e.arrow.symm b)
    · rw [e.source_symm,hs,Equiv.symm_apply_apply]
    · rw [e.target_symm,ht,Equiv.symm_apply_apply]

omit [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B] in
lemma orthogonal_pairwise {J:Type*} (v:J → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) :
    Pairwise fun a b => OrthogonalVertices R ((e.vertex ∘ v) a) ((e.vertex ∘ v) b) :=
  fun _ _ h => e.orthogonal (hv h)

lemma classMap_packet (hn:∀ a,Q.source a ≠ Q.target a)
    {J:Type u} [Fintype J] (v:J → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K := K)) :
    e.classMap (classPacketPerm Q hn v hv x) =
      classPacketPerm R (e.loopless hn) (e.vertex ∘ v) (e.orthogonal_pairwise v hv) (e.classMap x) := by
  classical
  suffices hh : ∀ (J:Type u) [Fintype J] (v:J → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)), ∀ x,
    e.classMap (classPacketPerm Q hn v hv x) =
      classPacketPerm R (e.loopless hn) (e.vertex ∘ v) (e.orthogonal_pairwise v hv) (e.classMap x) from hh J v hv x
  intro J inst
  apply Fintype.induction_empty_option (P := fun J _ => ∀ (v:J → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)), ∀ x,
    e.classMap (classPacketPerm Q hn v hv x) =
      classPacketPerm R (e.loopless hn) (e.vertex ∘ v) (e.orthogonal_pairwise v hv) (e.classMap x)) _ _ _ J
  · intro J L instL f ih
    let := Fintype.ofEquiv L f.symm
    intro v hv x
    rw [classPacketPerm_reindex Q hn v hv f,
      classPacketPerm_reindex R (e.loopless hn) (e.vertex ∘ v) _ f]
    exact ih _ _ x
  · intro v hv x
    rw [classPacketPerm_empty Q hn v hv,classPacketPerm_empty R (e.loopless hn)]
    rfl
  · intro J instJ ih v hv x
    rw [classPacketPerm_cons Q hn v hv,classPacketPerm_cons R (e.loopless hn)]
    change e.classMap (classPositiveTwist Q (v none) (classPacketPerm Q hn (v ∘ some) _ x)) =
      classPositiveTwist R (e.vertex (v none)) (classPacketPerm R _ ((e.vertex ∘ v) ∘ some) _ (e.classMap x))
    rw [e.classMap_positiveTwist]
    exact congrArg (classPositiveTwist R (e.vertex (v none)))
      (ih (v ∘ some) (fun a b hab => hv (fun h => hab (Option.some.inj h))) x)

lemma classMap_packet_inverse (hn:∀ a,Q.source a ≠ Q.target a)
    {J:Type u} [Fintype J] (v:J → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K := K)) :
    e.classMap ((classPacketPerm Q hn v hv).symm x) =
      (classPacketPerm R (e.loopless hn) (e.vertex ∘ v) (e.orthogonal_pairwise v hv)).symm (e.classMap x) := by
  apply (classPacketPerm R (e.loopless hn) (e.vertex ∘ v) (e.orthogonal_pairwise v hv)).injective
  rw [← e.classMap_packet hn v hv,Equiv.apply_symm_apply,Equiv.apply_symm_apply]

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
