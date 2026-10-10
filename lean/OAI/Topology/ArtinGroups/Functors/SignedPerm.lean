import Mathlib
import OAI.Topology.ArtinGroups.Functors.ProbeEmbeddingMap
import OAI.Topology.ArtinGroups.Complexes.HomDimensionDual

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A:Type} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A]
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q

lemma classMap_absent (x:FiniteHomotopyClass Q (K:=K)) (α:V) (b:Bool) :
    ∀i,((minimalClassModel R (classMap Q x)).complex.placement i).color≠.inr (α,b) := by
  intro i hi
  let E:=minimalClassModel R (classMap Q x)
  let d:ℤ:=(E.complex.placement i).level
  have hz:=classLevelArray_leaf Q x α b d
  rw [← minimalClassModel_class R (classMap Q x),
    classLevelArray_of_minimal R _ (minimalClassModel_minimal R _),levelArray_apply] at hz
  have hh:Nonempty {j:E.Index // (E.complex.placement j).color=.inr (α,b) ∧
      (E.complex.placement j).level=d}:=⟨⟨i,hi,rfl⟩⟩
  have hp:0<Nat.card {j:E.Index // (E.complex.placement j).color=.inr (α,b) ∧
      (E.complex.placement j).level=d}:=Nat.card_pos
  change Nat.card {j:E.Index // (E.complex.placement j).color=.inr (α,b) ∧
      (E.complex.placement j).level=d}=0 at hz
  omega

lemma classHom_dimension (x:FiniteHomotopyClass Q (K:=K)) (α:V) (b:Bool) (n v:ℤ) :
    classHomDimension R n v (initialClass R (.inr (α,b))) (classMap Q x)=
      classGeneratorArray Q x ⟨α,n,v-1⟩ := by
  rw [probeClassHomDimension_generatorArray Q _ α b (classMap_absent Q x α b)]
  exact classGeneratorArray_core Q x ⟨α,n,v-1⟩

variable (hn:∀a,Q.source a≠Q.target a)
noncomputable def signedPerm (a:V×Bool) : Equiv.Perm (FiniteHomotopyClass Q (K:=K)) :=
  if a.2 then classTwistPerm Q hn a.1 else (classTwistPerm Q hn a.1).symm
noncomputable def wordPerm : List (V×Bool) → Equiv.Perm (FiniteHomotopyClass Q (K:=K))
  | []=>1
  | a::w=>signedPerm Q hn a*wordPerm w

lemma classMap_signedPerm (a:V×Bool) (x:FiniteHomotopyClass Q (K:=K)) :
    classMap Q (signedPerm Q hn a x)=probeSignedPerm Q hn a (classMap Q x) := by
  rcases a with ⟨v,b⟩
  cases b
  · exact classMap_negativeTwist Q hn v x
  · exact classMap_positiveTwist Q v x

lemma classMap_wordPerm (w:List (V×Bool)) (x:FiniteHomotopyClass Q (K:=K)) :
    classMap Q (wordPerm Q hn w x)=probeWordPerm Q hn w (classMap Q x) := by
  induction w with
  | nil=>rfl
  | cons a w ih=>
    change classMap Q (signedPerm Q hn a (wordPerm Q hn w x))=_
    rw [classMap_signedPerm,ih]
    rfl

lemma orbit_classHom_dimension (w:List (V×Bool)) (x:FiniteHomotopyClass Q (K:=K))
    (α:V) (b:Bool) (n v:ℤ) :
    classHomDimension R n v
      (probeOrbit Q hn (w.reverse.map fun a=>(a.1,!a.2)) α b) (classMap Q x)=
      classGeneratorArray Q (wordPerm Q hn w x) ⟨α,n,v-1⟩ := by
  rw [← classHom_dimension Q (wordPerm Q hn w x) α b n v,classMap_wordPerm]
  unfold probeOrbit
  rw [probeWordPerm_inverse]
  have h:=probeWordPerm_homDimension Q hn w
    ((probeWordPerm Q hn w).symm (initialClass R (.inr (α,b)))) (classMap Q x) n v
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
