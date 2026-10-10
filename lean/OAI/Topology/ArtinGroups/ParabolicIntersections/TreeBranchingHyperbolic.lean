import OAI.Topology.ArtinGroups.ParabolicIntersections.PeriodicBoundary

namespace OAI

/-! The sufficient tree-action case of the published amalgam criterion, proved directly. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
open GraphRealization
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V)

lemma zpow_orbit_moves {a : G} {x : V}
    (ha : Function.Injective (fun n : ℤ => a^n • x)) : a • x≠x := by
  intro he
  have h : (1 : ℤ)=0 := ha (by simpa only [zpow_one,zpow_zero,one_smul] using he)
  norm_num at h

lemma zpow_third_direction {a : G} {x y z : V} (hx : a • x=x)
    (ha : Function.Injective (fun n : ℤ => a^n • y)) :
    ∃ c : G,c • x=x ∧ c • y≠y ∧ c • y≠z := by
  have ha₁ : a • y≠y := zpow_orbit_moves ha
  by_cases haz : a • y=z
  · have ha₂ : a^2 • y≠y := by
      intro he
      have h : (2 : ℤ)=0 := ha (by simpa using he)
      norm_num at h
    have ha₂₁ : a^2 • y≠a • y := by
      intro he
      have h : (2 : ℤ)=1 := ha (by simpa using he)
      norm_num at h
    refine ⟨a^2,?_,ha₂,?_⟩
    · rw [pow_two,mul_smul,hx,hx]
    · exact fun he => ha₂₁ (he.trans haz.symm)
  · exact ⟨a,hx,ha₁,haz⟩

/-- A free segment and infinite branching provide an explicit
non-elementary acylindrical action on a geodesic hyperbolic space. -/
theorem acylindricallyHyperbolic_of_free_segment
    (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    (hbranch : ∀ x y : V,T.Adj x y →
      ∃ a : G,a • x=x ∧ Function.Injective (fun n : ℤ => a^n • y))
    (u v : V) (hne : u≠v) (hnadj : ¬T.Adj u v)
    (hfree : pairStabilizer (G := G) u v=⊥) : AcylindricallyHyperbolic G := by
  obtain ⟨p,hp⟩ := hT.connected.exists_isPath u v
  have hpn : ¬p.Nil := fun h => hne (hp.nil_iff_eq.mp h)
  have hprn : ¬p.reverse.Nil := by
    intro h
    have hl := h.length_eq_zero
    rw [SimpleGraph.Walk.length_reverse] at hl
    exact hpn (SimpleGraph.Walk.length_eq_zero_iff.mp hl)
  obtain ⟨a,ha,ha'⟩ := hbranch u p.snd (p.adj_snd hpn)
  obtain ⟨b,hb,hb'⟩ := hbranch v p.reverse.snd (p.reverse.adj_snd hprn)
  obtain ⟨q,hq,hqn,hqt,hqu,hqv⟩ := translation_segment T hA hT.isAcyclic p hp hpn
    a b ha hb (zpow_orbit_moves ha') (zpow_orbit_moves hb')
  obtain ⟨c,hc,hc'⟩ := hbranch u q.snd (q.adj_snd hqn)
  obtain ⟨d,hd,hd₁,hd₂⟩ := zpow_third_direction (z := (a*b)⁻¹ • q.reverse.snd) hc hc'
  let H := avoidingGraph (G := G) T u v
  have hH := avoidingGraph_connected T u v hT hA hne hnadj
  have hB := avoidingGraph_preservesAdj T u v hA
  let X := Space H hH
  let _ := action H hB hH
  obtain ⟨hgeo,hhyp,hiso,hacyl⟩ := avoiding_realization_geometry T u v hT hA hfree hne hnadj
  have hlim : HasThreeOrbitLimitPoints G X :=
    periodic_three_limit_points T u v hT hA hfree hne hnadj (a*b) q hq hqn hqt a hqu hqv d hd hd₁ hd₂
  exact ⟨X,inferInstance,action H hB hH,hgeo,hhyp,hiso,hacyl,hlim⟩

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
