import OAI.Topology.ArtinGroups.ParabolicIntersections.VisualInfiniteBranching
import OAI.Topology.ArtinGroups.ParabolicIntersections.AmalgamNoncommuting
import Mathlib.GroupTheory.SpecificGroups.VirtuallyCyclic

namespace OAI

/-! Visual Artin splittings are not virtually cyclic. Powers of generators
on opposite sides give nontrivial reduced commutators. This verifies the
exception exclusion in the Minasyan--Osin amalgam criterion. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]

omit [Fintype S] hSplit in
private lemma visual_factor_not_base (i : Bool)
    (a : artinParabolic M (visualSide Y Z i)) (ha : a.val∉artinParabolic M (Y∩Z)) :
    a∉(visualEdgeInclusion M Y Z i).range := by
  rintro ⟨c,hc⟩
  apply ha
  rw [←congrArg Subtype.val hc]
  exact c.property

include hSplit

lemma visual_opposite_powers_not_commute (s : S) (hs : s ∈ Y \ Z)
    (t : S) (ht : t ∈ Z \ Y) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    generator M s^m * generator M t^n ≠ generator M t^n * generator M s^m := by
  let a : artinParabolic M Y := ⟨generator M s^m,
    (artinParabolic M Y).pow_mem ((generator_mem_standard_iff M Y s).mpr hs.1) m⟩
  let b : artinParabolic M Z := ⟨generator M t^n,
    (artinParabolic M Z).pow_mem ((generator_mem_standard_iff M Z t).mpr ht.1) n⟩
  have ha : a∉(visualEdgeInclusion M Y Z false).range := by
    apply visual_factor_not_base M Y Z false a
    simpa only [a,zpow_natCast] using
      generator_zpow_not_mem M (Y∩Z) s (fun h => hs.2 h.2) (m : ℤ) (by omega)
  have hb : b∉(visualEdgeInclusion M Y Z true).range := by
    apply visual_factor_not_base M Y Z true b
    simpa only [b,zpow_natCast] using
      generator_zpow_not_mem M (Y∩Z) t (fun h => ht.2 h.1) (n : ℤ) (by omega)
  have hh := AmalgamTree.factor_commutator_ne_one (visualEdgeInclusion M Y Z)
    (fun _ => Subgroup.inclusion_injective _) a b ha hb
  intro he
  have hc : generator M s^m * generator M t^n *
      (generator M s^m)⁻¹ * (generator M t^n)⁻¹=1 := by
    rw [he]
    group
  have hc' := congrArg (visualFromArtin M Y Z hSplit.out) hc
  simp only [map_mul,map_inv,map_one] at hc'
  rw [show generator M s^m=a.val from rfl,
    show generator M t^n=b.val from rfl,
    visualFromArtin_factor M Y Z hSplit.out false a,
    visualFromArtin_factor M Y Z hSplit.out true b] at hc'
  exact hh hc'

/-- A visual Artin splitting never gives the virtually cyclic exception. -/
theorem visual_not_virtuallyCyclic : ¬Group.IsVirtuallyCyclic (Artin M) := by
  intro hVC
  let : Group.IsVirtuallyCyclic (Artin M) := hVC
  obtain ⟨C,hC,hindex⟩ := Group.IsVirtuallyCyclic.exists_isCyclic_and_finiteIndex (Artin M)
  let : IsCyclic C := hC
  let : CommGroup C := IsCyclic.commGroup
  let : C.FiniteIndex := hindex
  obtain ⟨s,hs⟩ := Set.nonempty_compl.mpr (Set.ssubset_iff_subset_ne.mp hSplit.out.2.2.1).2
  obtain ⟨t,ht⟩ := Set.nonempty_compl.mpr (Set.ssubset_iff_subset_ne.mp hSplit.out.2.1).2
  have hsY : s∈Y := (hSplit.out.1.symm ▸ Set.mem_univ s : s∈Y∪Z).resolve_right hs
  have htZ : t∈Z := (hSplit.out.1.symm ▸ Set.mem_univ t : t∈Y∪Z).resolve_left ht
  obtain ⟨m,hm,_,hmC⟩ := C.exists_pow_mem_of_index_ne_zero Subgroup.FiniteIndex.index_ne_zero (generator M s)
  obtain ⟨n,hn,_,hnC⟩ := C.exists_pow_mem_of_index_ne_zero Subgroup.FiniteIndex.index_ne_zero (generator M t)
  apply visual_opposite_powers_not_commute M Y Z s ⟨hsY,hs⟩ t ⟨htZ,ht⟩ m n hm hn
  exact congrArg Subtype.val (mul_comm (⟨generator M s^m,hmC⟩ : C) ⟨generator M t^n,hnC⟩)

end HarmonicArtin.ParabolicIntersections

end OAI
