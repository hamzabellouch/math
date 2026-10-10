import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.AltList
import OAI.Topology.ArtinGroups.Coxeter.OrdinaryCoxeterMatrix
import OAI.Topology.ArtinGroups.Quivers.ProbeVertex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
open Zigzag Zigzag.BasedComplex CoxeterExchange

variable {V A:Type} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q
variable [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)] in
lemma probe_orthogonal {α β:V} (h:OrthogonalVertices Q α β) :
    OrthogonalVertices R (.inl α) (.inl β) := by
  refine ⟨fun hh=>h.1 (Sum.inl.inj hh),?_⟩
  rintro (a|⟨v,b,dir⟩) hs ht
  · exact h.2 a (Sum.inl.inj hs) (Sum.inl.inj ht)
  · cases dir <;> simp [probeQuiver] at hs ht

def probe_simpleEdge {α β:V} (e:SimpleEdge Q α β) :
    SimpleEdge R (.inl α) (.inl β) where
  arrow:=.inl e.arrow
  source:=congrArg Sum.inl e.source
  target:=congrArg Sum.inl e.target
  distinct:=fun h=>e.distinct (Sum.inl.inj h)
  unique:=by
    rintro (a|⟨v,b,dir⟩) hs ht
    · exact congrArg Sum.inl (e.unique a (Sum.inl.inj hs) (Sum.inl.inj ht))
    · cases dir <;> simp [probeQuiver] at hs ht

variable (hn:∀a,Q.source a≠Q.target a)
omit [DecidableEq A] in
lemma probe_core_braid (α β:V) :
    ((altList α β (ordinaryCoxeterMatrix Q α β)).map
      (fun v=>classTwistPerm R (K:=K) (probeQuiver_no_loops Q hn) (.inl v))).prod=
    ((altList β α (ordinaryCoxeterMatrix Q α β)).map
      (fun v=>classTwistPerm R (K:=K) (probeQuiver_no_loops Q hn) (.inl v))).prod := by
  by_cases he:α=β
  · subst β; rfl
  by_cases ho:OrthogonalVertices Q α β
  · rw [ordinaryCoxeterMatrix_orthogonal Q ho]
    simpa only [altList_succ,altList_zero,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      _root_.mul_one] using classTwistPerm_orthogonal R (K:=K)
        (probeQuiver_no_loops Q hn) (probe_orthogonal Q ho)
  by_cases ha:Nonempty (SimpleEdge Q α β)
  · obtain ⟨e⟩:=ha
    rw [ordinaryCoxeterMatrix_adjacent Q e]
    simpa only [altList_succ,altList_zero,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      _root_.mul_one,_root_.mul_assoc] using classTwistPerm_adjacent R (K:=K)
        (probeQuiver_no_loops Q hn) (probe_simpleEdge Q e)
  · have hz:ordinaryCoxeterMatrix Q α β=0:=by simp [ordinaryCoxeterMatrix,he,ho,ha]
    rw [hz]; rfl
end HarmonicArtin.ReversibleQuiver

end OAI
