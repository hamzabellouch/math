import Mathlib
import OAI.Topology.ArtinGroups.Functors.SignedPerm

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A:Type} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A]
  [DecidableEq V] [DecidableEq A] [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q
variable (hn:∀a,Q.source a≠Q.target a)

lemma classHom_dimension_flexible (x:FiniteHomotopyClass Q (K:=K))
    (α:V) (b:Bool) (n v:ℤ) :
    classHomDimension R n v (initialClass R (.inr (α,b))) (classMap Q x)=
      classGeneratorArray Q x ⟨α,n,v-1⟩ := by
  cases Subsingleton.elim (inferInstance : DecidableEq V) (Classical.decEq V)
  cases Subsingleton.elim (inferInstance : DecidableEq A) (Classical.decEq A)
  cases Subsingleton.elim (inferInstance : DecidableEq (ProbeVertex V))
    (@instDecidableEqSum V (V×Bool) (Classical.decEq V)
      (@instDecidableEqProd V Bool (Classical.decEq V) inferInstance))
  cases Subsingleton.elim (inferInstance : DecidableEq (ProbeArrow V A))
    (@instDecidableEqSum A (V×Bool×Bool) (Classical.decEq A)
      (@instDecidableEqProd V (Bool×Bool) (Classical.decEq V) inferInstance))
  exact classHom_dimension Q x α b n v

lemma classMap_twistProd (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :
    classMap Q (((w.map (classTwistPerm Q hn)).prod) x)=
      ((w.map (fun v=>classTwistPerm R (probeQuiver_no_loops Q hn) (.inl v))).prod)
        (classMap Q x) := by
  induction w generalizing x with
  | nil=>rfl
  | cons a w ih=>
    simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply]
    change classMap Q (classPositiveTwist Q a _) = _
    rw [classMap_positiveTwist,ih]
    rfl

omit [DecidableEq V] [DecidableEq A] in
lemma twistProd_homDimension (w:List V) (x y:FiniteHomotopyClass R (K:=K)) (n v:ℤ) :
    classHomDimension R n v
      (((w.map (fun v=>classTwistPerm R (probeQuiver_no_loops Q hn) (.inl v))).prod) x)
      (((w.map (fun v=>classTwistPerm R (probeQuiver_no_loops Q hn) (.inl v))).prod) y)=
      classHomDimension R n v x y := by
  induction w generalizing x y with
  | nil=>rfl
  | cons a w ih=>
    simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply]
    rw [show ∀x y,classHomDimension R n v
        (classTwistPerm R (probeQuiver_no_loops Q hn) (.inl a) x)
        (classTwistPerm R (probeQuiver_no_loops Q hn) (.inl a) y)=classHomDimension R n v x y
      from classPositiveTwist_homDimension R (probeQuiver_no_loops Q hn) (.inl a) n v]
    exact ih x y

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
