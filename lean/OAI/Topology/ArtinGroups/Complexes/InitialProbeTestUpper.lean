import Mathlib
import OAI.Topology.ArtinGroups.Complexes.OutsideCap
import OAI.Topology.ArtinGroups.Quivers.ProbeVertex
import OAI.Topology.ArtinGroups.Complexes.ScalarExactNotZero

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
local notation "R" => probeQuiver Q

lemma initialProbe_test_upper (α:V) (b:Bool) (U:Set (ProbeVertex V))
    (hU:U⊆Set.range (Sum.inl:V→ProbeVertex V)) :
    ClassTestUpper R (initialClass R (K:=K) (.inr (α,b))) U 1 := by
  intro β hβ l hl c
  obtain ⟨β,rfl⟩:=hU hβ
  change ScalarExactAt R ((initialProjective R (.inr (α,b))).testComplex R (.inl β)) _ _ _
  apply scalarExact_of_absent_degree R
  rintro ⟨i,⟨p,hs,ht⟩⟩ he
  change Path.target R p=Sum.inr (α,b) at ht
  dsimp only [testComplex,testPlacement,initialProjective,GeneratorPlacement.level] at he
  rcases p with a|a|a
  · exact Sum.inl_ne_inr ((hs.symm.trans ht))
  · norm_num [Path.length] at he; omega
  · exact Sum.inl_ne_inr ((hs.symm.trans ht))

lemma initialProbe_top_not_exact (α:V) (b:Bool) :
    ¬ClassTestExact R (.inl α) 1 0 (initialClass R (K:=K) (.inr (α,b))) :=
  initialClass_test_not_exact R (.inl α) (.inr (α,b))
    ⟨.inr (.inl (.inr (α,b,false))),rfl,rfl⟩

omit [Fintype V] [Fintype A] [DecidableEq (ProbeVertex V)]
  [DecidableEq (ProbeArrow V A)] in
lemma probe_core_leaf_orthogonal {α β:V} (h:α≠β) (b:Bool) :
    OrthogonalVertices R (.inl α) (.inr (β,b)) := by
  refine ⟨Sum.inl_ne_inr,?_⟩
  intro a hs ht
  have ha: a=.inr (β,b,false):=(probe_target_iff Q β b a).mp ht
  rw [ha] at hs
  exact h (Sum.inl.inj hs).symm

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
