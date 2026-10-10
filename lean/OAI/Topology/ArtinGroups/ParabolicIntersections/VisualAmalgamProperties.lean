import OAI.Topology.ArtinGroups.ParabolicIntersections.VisualNonVirtuallyCyclic

namespace OAI

/-! The nondegeneracy and edge-identification hypotheses of the published
amalgam criterion, verified for the actual Artin visual splitting. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]
include hSplit

omit [Fintype S] in
lemma visual_edge_comap :
    (Monoid.PushoutI.base (visualEdgeInclusion M Y Z)).range.comap
      (visualFromArtin M Y Z hSplit.out)=artinParabolic M (Y∩Z) := by
  ext a
  constructor
  · rintro ⟨c,hc⟩
    have he := congrArg (visualToArtin M Y Z) hc
    rw [visualToArtin_from] at he
    have hc' : visualToArtin M Y Z (Monoid.PushoutI.base (visualEdgeInclusion M Y Z) c)=c.val := by
      rw [←Monoid.PushoutI.of_apply_eq_base (visualEdgeInclusion M Y Z) false c]
      exact Monoid.PushoutI.lift_of _ _ _ _
    rw [hc'] at he
    exact he ▸ c.property
  · intro ha
    refine ⟨⟨a,ha⟩,?_⟩
    rw [←Monoid.PushoutI.of_apply_eq_base (visualEdgeInclusion M Y Z) false ⟨a,ha⟩]
    exact (visualFromArtin_factor M Y Z hSplit.out false
      ⟨a,standard_mono M Set.inter_subset_left ha⟩).symm

lemma visual_edge_inclusion_proper (b : Bool) :
    (visualEdgeInclusion M Y Z b).range≠⊤ := by
  have hproper : visualSide Y Z (!b)≠Set.univ := by
    cases b
    · exact (Set.ssubset_iff_subset_ne.mp hSplit.out.2.2.1).2
    · exact (Set.ssubset_iff_subset_ne.mp hSplit.out.2.1).2
  obtain ⟨s,hs⟩ := Set.nonempty_compl.mpr hproper
  have hside : s∈visualSide Y Z b := by
    cases b
    · exact (hSplit.out.1.symm ▸ Set.mem_univ s : s∈Y∪Z).resolve_right hs
    · exact (hSplit.out.1.symm ▸ Set.mem_univ s : s∈Y∪Z).resolve_left hs
  let a : artinParabolic M (visualSide Y Z b) :=
    ⟨generator M s,(generator_mem_standard_iff M _ _).mpr hside⟩
  intro he
  have ha : a∈(visualEdgeInclusion M Y Z b).range := he ▸ Subgroup.mem_top a
  obtain ⟨c,hc⟩ := ha
  have hc' : generator M s∈artinParabolic M (Y∩Z) := by
    change a.val∈artinParabolic M (Y∩Z)
    rw [←congrArg Subtype.val hc]
    exact c.property
  have hs' := (generator_mem_standard_iff M (Y∩Z) s).mp hc'
  cases b
  · exact hs hs'.2
  · exact hs hs'.1

end HarmonicArtin.ParabolicIntersections

end OAI
