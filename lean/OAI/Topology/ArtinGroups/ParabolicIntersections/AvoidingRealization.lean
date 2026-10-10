import OAI.Topology.ArtinGroups.ParabolicIntersections.DynamicsDefinitions
import OAI.Topology.ArtinGroups.ParabolicIntersections.GraphRealizationGeodesic
import OAI.Topology.ArtinGroups.ParabolicIntersections.GraphRealizationAcylindrical
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeShortcutAcylindrical

namespace OAI

/-! The genuine geodesic acylindrical hyperbolic space of a free tree segment. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (u v : V)

theorem avoiding_realization_geometry (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    (hfree : pairStabilizer (G := G) u v=⊥) (hne : u≠v) (hnadj : ¬T.Adj u v) :
    let H := avoidingGraph (G := G) T u v
    let hH := avoidingGraph_connected T u v hT hA hne hnadj
    let hB := avoidingGraph_preservesAdj T u v hA
    let X := GraphRealization.Space H hH
    let _ := GraphRealization.action H hB hH
    IsGeodesicMetric X ∧ IsGromovHyperbolic X ∧
      (∀ g : G,Isometry (fun x : X => g • x)) ∧ IsAcylindrical G X := by
  let H := avoidingGraph (G := G) T u v
  have hH := avoidingGraph_connected T u v hT hA hne hnadj
  have hB := avoidingGraph_preservesAdj T u v hA
  let _ := GraphRealization.action H hB hH
  refine ⟨GraphRealization.realization_geodesic H hH,?_,GraphRealization.action_isometric H hB hH,?_⟩
  · refine ⟨9,by norm_num,?_⟩
    intro o x y z
    simpa only [gromovProduct,GraphRealization.product,show (3 : ℝ)+6=9 by norm_num] using GraphRealization.realization_hyperbolic H hH 3
      (shortcut_graph_hyperbolic T H hT hH (avoidingGraph_pathSaturated T u v hT.isAcyclic)) o x y z
  · intro ε hε
    let r := Nat.ceil ε
    let R := 2*(r+2)+10
    let N := R*(2*T.dist u v+1)^2
    refine ⟨(R : ℝ)+2,N,?_⟩
    intro x y hxy
    have hcount (a b : V) (hab : R ≤ H.dist a b) :
        {g : G | H.dist a (g • a) ≤ r+2 ∧ H.dist b (g • b) ≤ r+2}.Finite ∧
        {g : G | H.dist a (g • a) ≤ r+2 ∧ H.dist b (g • b) ≤ r+2}.ncard ≤ N :=
      avoidingGraph_acylindrical_count T u v hT hA hfree hne hnadj (r+2) a b hab
    obtain ⟨hfin,hcard⟩ := GraphRealization.acylindricity_transfer H hB hH r R N hcount x y hxy
    have hεr : ε ≤ (r : ℝ) := Nat.le_ceil ε
    have hsub : {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε} ⊆
        {g : G | dist x (g • x) ≤ r ∧ dist y (g • y) ≤ r} :=
      fun _ hg => ⟨hg.1.trans hεr,hg.2.trans hεr⟩
    exact ⟨hfin.subset hsub,(Set.ncard_le_ncard hsub hfin).trans hcard⟩

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
