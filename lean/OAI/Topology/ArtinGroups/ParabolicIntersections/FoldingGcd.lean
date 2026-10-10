import OAI.Topology.ArtinGroups.ParabolicIntersections.FoldingHead
import OAI.Topology.ArtinGroups.ParabolicIntersections.BraidRestriction

namespace OAI

/-! Discharge of the published common-left-atom folding input. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
    (Y : Set S) (hY : IsSpherical M Y)
local notation "R" => restrictedMatrix M Y
local notation "N" => unfoldedMatrix M Y
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "f" => unfoldedInclusion M Y

private lemma expanded_braid_prefix (u : List Y) (a : Y × FusionLabel m)
    (r : List (FusionVertex (V:=S⊕Unit) m))
    (hu : PositiveBraidRel Q
      (fusionExpandedWord m (u.map fun j : Y => (Sum.inl (j:S) : S⊕Unit))) (f a::r)) :
    PositivePrefix N (positiveGenerator N a) (foldedPositiveHom M Y hY (wordPositive R u)) := by
  let : Nonempty (Y × FusionLabel m) := ⟨a⟩
  rw [fusionExpandedWord_map] at hu
  have hs : ∀ x ∈ (fusionExpandedWord m u).map f, x ∈ Set.range f := by
    intro x hx
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
    exact ⟨b,rfl⟩
  have he := positiveBraidRel_restrict Q N f (unfoldedInclusion_injective M Y)
    (unfolded_ordinaryMatrix M Y hY) hu hs
  have hinv : ∀ x, Function.invFun f (f x)=x :=
    Function.leftInverse_invFun (unfoldedInclusion_injective M Y)
  have hw : ((fusionExpandedWord m u).map f).map (Function.invFun f)=fusionExpandedWord m u := by
    rw [List.map_map]
    have hi : (Function.invFun f ∘ f)=id := funext hinv
    rw [hi,List.map_id]
  rw [hw,List.map_cons,hinv] at he
  rw [foldedPositiveHom_word]
  exact ⟨wordPositive N (r.map (Function.invFun f)),he⟩

/-- Castella's common-atom consequence, now proved for the particular
color folding rather than supplied as a hypothesis. -/
theorem folding_gcd_input : PublishedFoldingGcd M Y hY where
  common_atom := by
    intro u v α r s hu hv
    have hmem := (hu.mem_iff Q α).mpr (by simp)
    rw [fusionExpandedWord_map] at hmem
    obtain ⟨a,_,ha⟩ := List.mem_map.mp hmem
    change f a=α at ha
    subst α
    exact ⟨a.1,
      folded_atom_reflect M Y hY _ a (expanded_braid_prefix M Y hY u a r hu),
      folded_atom_reflect M Y hY _ a (expanded_braid_prefix M Y hY v a s hv)⟩

end HarmonicArtin.ParabolicIntersections

end OAI
