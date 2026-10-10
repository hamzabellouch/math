import Mathlib
import OAI.Topology.ArtinGroups.Complexes.CornerPath
import OAI.Topology.ArtinGroups.Functors.ZigzagLinear

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A K:Type*} (Q:ReversibleQuiver V A)
local notation "R" => probeQuiver Q

def path : Path V A → Path (ProbeVertex V) (ProbeArrow V A) :=
  Sum.map Sum.inl (Sum.map Sum.inl Sum.inl)

lemma path_injective : Function.Injective (path (V:=V) (A:=A)) := by
  exact Sum.map_injective.mpr ⟨Sum.inl_injective,Sum.map_injective.mpr ⟨Sum.inl_injective,Sum.inl_injective⟩⟩
@[simp] lemma path_source (p:Path V A) : Path.source R (path p)=.inl (Path.source Q p) := by
  rcases p with v|a|v <;> rfl
@[simp] lemma path_target (p:Path V A) : Path.target R (path p)=.inl (Path.target Q p) := by
  rcases p with v|a|v <;> rfl
@[simp] lemma path_length (p:Path V A) : Path.length (path p)=Path.length p := by
  rcases p with v|a|v <;> rfl

lemma cornerPath_surjective (s t:V)
    (p:CornerPath R (.inl s) (.inl t)) :
    ∃q:CornerPath Q s t,path q.val=p.val := by
  rcases p with ⟨p,hs,ht⟩
  rcases p with (v|v)|(a|⟨v,b,d⟩)|(v|v)
  · exact ⟨⟨.inl v,Sum.inl.inj hs,Sum.inl.inj ht⟩,rfl⟩
  · cases hs
  · exact ⟨⟨.inr (.inl a),Sum.inl.inj hs,Sum.inl.inj ht⟩,rfl⟩
  · cases d
    · cases ht
    · cases hs
  · exact ⟨⟨.inr (.inr v),Sum.inl.inj hs,Sum.inl.inj ht⟩,rfl⟩
  · cases hs

noncomputable def cornerPath (s t:V) : CornerPath Q s t ≃ CornerPath R (.inl s) (.inl t) :=
  Equiv.ofBijective (fun p=>⟨path p.val,by
    rw [path_source,path_target,p.property.1,p.property.2]; exact ⟨rfl,rfl⟩⟩)
    ⟨fun _ _ h=>Subtype.ext (path_injective (congrArg Subtype.val h)),by
      intro p; obtain ⟨q,hq⟩:=cornerPath_surjective Q s t p
      exact ⟨q,Subtype.ext hq⟩⟩

variable [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma path_coordinates (x:Q.Zigzag K) (p:Path V A) :
    pathCoordinates R (zigzagLinear Q x) (path p)=pathCoordinates Q x p := by
  rcases p with v|a|v <;> rfl

lemma path_basis (p:Path V A) : zigzagLinear Q (pathBasis Q (K:=K) p)=pathBasis R (path p) := by
  apply (pathCoordinates R).injective
  funext q
  rcases q with (v|v)|(a|a)|(v|v)
  · change pathCoordinates Q (pathBasis Q p) (.inl v)=_
    rw [pathBasis_coordinates,pathBasis_coordinates]
    exact if_congr (path_injective.eq_iff.symm) rfl rfl
  · rw [pathCoordinates_vertex,zigzag_vertex_leaf,pathBasis_coordinates]
    rcases p with p|p|p <;> simp [path]
  · change pathCoordinates Q (pathBasis Q p) (.inr (.inl a))=_
    rw [pathBasis_coordinates,pathBasis_coordinates]
    exact if_congr (path_injective.eq_iff.symm) rfl rfl
  · rw [pathCoordinates_arrow,zigzag_arrow_leaf,pathBasis_coordinates]
    rcases p with p|p|p <;> simp [path]
  · change pathCoordinates Q (pathBasis Q p) (.inr (.inr v))=_
    rw [pathBasis_coordinates,pathBasis_coordinates]
    exact if_congr (path_injective.eq_iff.symm) rfl rfl
  · rw [pathCoordinates_token,zigzag_token_leaf,pathBasis_coordinates]
    rcases p with p|p|p <;> simp [path]

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
