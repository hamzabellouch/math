import Mathlib
import OAI.Topology.ArtinGroups.Quivers.CornerPath
import OAI.Topology.ArtinGroups.Quivers.Iso

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag

variable {V A W B K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R)

def path : Path V A ≃ Path W B := e.vertex.sumCongr (e.arrow.sumCongr e.vertex)

@[simp] lemma path_source (p:Path V A) : Path.source R (e.path p) = e.vertex (Path.source Q p) := by
  rcases p with v|a|v
  · rfl
  · exact e.source a
  · rfl
@[simp] lemma path_target (p:Path V A) : Path.target R (e.path p) = e.vertex (Path.target Q p) := by
  rcases p with v|a|v
  · rfl
  · exact e.target a
  · rfl
@[simp] lemma path_length (p:Path V A) : Path.length (e.path p) = Path.length p := by
  rcases p with v|a|v <;> rfl

variable [Field K] [Fintype A] [Fintype B] [DecidableEq V] [DecidableEq W]
lemma path_coordinates (x:Q.Zigzag K) (p:Path V A) :
    pathCoordinates R (e.zigzagLinear x) (e.path p) = pathCoordinates Q x p := by
  rcases p with v|a|v
  · change x.vertex (e.vertex.symm (e.vertex v)) = x.vertex v
    rw [Equiv.symm_apply_apply]
  · change x.arrow (e.arrow.symm (e.arrow a)) = x.arrow a
    rw [Equiv.symm_apply_apply]
  · change x.token (e.vertex.symm (e.vertex v)) = x.token v
    rw [Equiv.symm_apply_apply]

variable [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B]
lemma path_basis (p:Path V A) :
    e.zigzagLinear (pathBasis Q (K := K) p) = pathBasis R (e.path p) := by
  apply (pathCoordinates R).injective
  funext q
  obtain ⟨q,rfl⟩ := e.path.surjective q
  rw [e.path_coordinates,pathBasis_coordinates,pathBasis_coordinates]
  simp only [e.path.injective.eq_iff]

def cornerPath (s t:V) : CornerPath Q s t ≃ CornerPath R (e.vertex s) (e.vertex t) where
  toFun p := ⟨e.path p, (e.path_source p).trans (congrArg e.vertex p.property.1),
    (e.path_target p).trans (congrArg e.vertex p.property.2)⟩
  invFun p := ⟨e.path.symm p,by
    have hs := e.path_source (e.path.symm p)
    have ht := e.path_target (e.path.symm p)
    simp only [Equiv.apply_symm_apply,p.property.1,p.property.2] at hs ht
    exact ⟨e.vertex.injective hs.symm,e.vertex.injective ht.symm⟩⟩
  left_inv p := Subtype.ext (e.path.symm_apply_apply p)
  right_inv p := Subtype.ext (e.path.apply_symm_apply p)

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
