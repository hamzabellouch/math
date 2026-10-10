import Mathlib
import OAI.Topology.ArtinGroups.Complexes.FiniteHomotopySetoid
import OAI.Topology.ArtinGroups.Complexes.PacketConsEquiv

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def classOfComplex {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K := K) I) : FiniteHomotopyClass Q (K := K) :=
  Quotient.mk (finiteHomotopySetoid Q) (FiniteModel.ofComplex Q E)

omit [Fintype V] [DecidableEq A] in
lemma classOfComplex_eq {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (e : HomotopyEquivalence Q E F) : classOfComplex Q E = classOfComplex Q F :=
  Quotient.sound ⟨e⟩

omit [Fintype V] [DecidableEq A] in
lemma classOfComplex_reindex {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (E : BasedComplex Q (K := K) I) (e : J ≃ I) :
    classOfComplex Q E = classOfComplex Q (E.reindex Q e) :=
  classOfComplex_eq Q (E.reindexHomotopyEquivalence Q e)

lemma classOfComplex_packet_reindex {I J L : Type u}
    [Fintype I] [Fintype J] [Fintype L] [DecidableEq I] [DecidableEq J] [DecidableEq L]
    (E : BasedComplex Q (K := K) I) (v:J → V) (e:L ≃ J) :
    classOfComplex Q (E.packetTwist Q v) = classOfComplex Q (E.packetTwist Q (v ∘ e)) := by
  rw [classOfComplex_reindex Q _ (packetReindexEquiv Q E v e),packetReindex_eq]

lemma classOfComplex_packet_cons {I J : Type u}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (E : BasedComplex Q (K := K) I) (α:V) (v:J → V)
    (h : ∀ a, OrthogonalVertices Q α (v a)) :
    classOfComplex Q (E.packetTwist Q (fun z : Option J => z.elim α v)) =
      classPositiveTwist Q α (classOfComplex Q (E.packetTwist Q v)) := by
  change _ = classOfComplex Q ((E.packetTwist Q v).positiveTwist Q α)
  rw [classOfComplex_reindex Q _ (packetConsEquiv Q E α v h),packetCons_eq]

theorem exists_packetPerm (hn : ∀ a, Q.source a ≠ Q.target a)
    {J : Type u} [Fintype J] (v : J → V)
    (hv : Pairwise (fun a b => OrthogonalVertices Q (v a) (v b))) :
    ∃ π : Equiv.Perm (FiniteHomotopyClass Q (K := K)),
      ∀ E : FiniteModel.{u} Q (K := K), classOfComplex Q (E.complex.packetTwist Q v) =
        π (Quotient.mk (finiteHomotopySetoid Q) E) := by
  classical
  suffices hh : ∀ (J : Type u) [Fintype J] (v:J → V),
      Pairwise (fun a b => OrthogonalVertices Q (v a) (v b)) →
      ∃ π : Equiv.Perm (FiniteHomotopyClass Q (K := K)),
        ∀ E : FiniteModel.{u} Q (K := K), classOfComplex Q (E.complex.packetTwist Q v) =
          π (Quotient.mk (finiteHomotopySetoid Q) E) from hh J v hv
  intro J inst
  apply Fintype.induction_empty_option (P := fun J _ => ∀ v:J → V,
    Pairwise (fun a b => OrthogonalVertices Q (v a) (v b)) →
    ∃ π : Equiv.Perm (FiniteHomotopyClass Q (K := K)),
      ∀ E : FiniteModel.{u} Q (K := K), classOfComplex Q (E.complex.packetTwist Q v) =
        π (Quotient.mk (finiteHomotopySetoid Q) E)) _ _ _ J
  · intro J L instL e ih
    let := Fintype.ofEquiv L e.symm
    intro v hv
    obtain ⟨π,hπ⟩ := ih (v ∘ e) (fun a b hab => hv (fun he => hab (e.injective he)))
    refine ⟨π,fun E => ?_⟩
    rw [classOfComplex_packet_reindex Q E.complex v e]
    exact hπ E
  ·
    intro v hv
    refine ⟨Equiv.refl _,fun E => ?_⟩
    convert (classOfComplex_reindex Q _ (packetEmptyEquiv Q E.complex v)).trans
      (congrArg (classOfComplex Q) (packetEmpty_eq Q E.complex v)) using 1 <;> (congr 2 <;> exact Subsingleton.elim _ _)
  · intro J instJ ih v hv
    obtain ⟨π,hπ⟩ := ih (v ∘ some) (fun a b hab => hv (fun he => hab (Option.some.inj he)))
    refine ⟨classTwistPerm Q hn (v none) * π,fun E => ?_⟩
    have hv' : v = fun z : Option J => z.elim (v none) (v ∘ some) := by
      funext z; cases z <;> rfl
    conv_lhs => rw [hv']
    convert (classOfComplex_packet_cons Q E.complex (v none) (v ∘ some)
      (fun a => hv (by simp))).trans (congrArg (classPositiveTwist Q (v none)) (hπ E)) using 1 <;> (congr 2 <;> exact Subsingleton.elim _ _)

noncomputable def classPacketPerm (hn : ∀ a, Q.source a ≠ Q.target a)
    {J : Type u} [Fintype J] (v : J → V)
    (hv : Pairwise (fun a b => OrthogonalVertices Q (v a) (v b))) :
    Equiv.Perm (FiniteHomotopyClass Q (K := K)) :=
  (exists_packetPerm Q (K := K) hn v hv).choose

lemma classPacketPerm_apply (hn : ∀ a, Q.source a ≠ Q.target a)
    {J : Type u} [Fintype J] [DecidableEq J] (v : J → V)
    (hv : Pairwise (fun a b => OrthogonalVertices Q (v a) (v b)))
    (E : FiniteModel.{u} Q (K := K)) :
    classPacketPerm Q hn v hv (Quotient.mk (finiteHomotopySetoid Q) E) =
      classOfComplex Q (E.complex.packetTwist Q v) :=
by
  convert ((exists_packetPerm Q (K := K) hn v hv).choose_spec E).symm using 1 <;>
    (congr 2 <;> exact Subsingleton.elim _ _)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
