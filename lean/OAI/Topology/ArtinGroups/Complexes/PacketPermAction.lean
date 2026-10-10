import Mathlib
import OAI.Topology.ArtinGroups.Complexes.UnfoldedPresentation
import OAI.Topology.ArtinGroups.Complexes.PacketPermReindex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  (hn : ∀ a, Q.source a ≠ Q.target a)
  (M:CoxeterMatrix V) (hM:UnfoldedPresentation Q M)
local notation "Act" => unfoldedArtinAction Q (K:=K) hn M hM

lemma classPacketPerm_in_action {J:Type u} [Fintype J] (v:J → V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)) :
    ∃ x:Artin M,Act x=classPacketPerm Q hn v hv := by
  suffices hh : ∀ (J:Type u) [Fintype J] (v:J → V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)),
    ∃ x:Artin M,Act x=classPacketPerm Q hn v hv from hh J v hv
  intro J inst
  apply Fintype.induction_empty_option (P:=fun J _=>∀ (v:J → V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)),
    ∃ x:Artin M,Act x=classPacketPerm Q hn v hv) _ _ _ J
  · intro J L instL e ih
    let := Fintype.ofEquiv L e.symm
    intro v hv
    rw [classPacketPerm_reindex Q hn v hv e]
    exact ih _ _
  · intro v hv
    refine ⟨1,?_⟩
    rw [map_one,classPacketPerm_empty]
    rfl
  · intro J inst ih v hv
    obtain ⟨x,hx⟩:=ih (v ∘ some) (fun a b hab=>hv (fun he=>hab (Option.some.inj he)))
    refine ⟨generator M (v none)*x,?_⟩
    rw [map_mul,unfoldedArtinAction_generator,hx,classPacketPerm_cons]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
