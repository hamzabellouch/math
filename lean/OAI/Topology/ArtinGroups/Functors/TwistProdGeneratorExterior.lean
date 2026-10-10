import Mathlib
import OAI.Topology.ArtinGroups.Complexes.GeneratorArray2
import OAI.Topology.ArtinGroups.Quivers.ProbeVertex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A:Type} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
local notation "R" => probeQuiver Q
lemma twistProd_generator_exterior (hn:∀a,Q.source a≠Q.target a) (w:List V)
    (x:FiniteHomotopyClass R (K:=K)) (p:GeneratorPlacement (ProbeVertex V))
    (hw:∀a∈w,Sum.inl a≠p.color) :
    classGeneratorArray R (((w.map (fun a=>classTwistPerm R (probeQuiver_no_loops Q hn) (.inl a))).prod) x) p=
      classGeneratorArray R x p := by
  induction w generalizing x with
  | nil=>rfl
  | cons a w ih=>
    simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply]
    change classGeneratorArray R (classPositiveTwist R (.inl a) _) p=_
    rw [classPositiveTwist_exterior R _ _ _ (hw a (by simp))]
    exact ih x (fun b hb=>hw b (by simp [hb]))
end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
