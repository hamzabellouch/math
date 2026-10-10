import OAI.Topology.ArtinGroups.ParabolicIntersections.Basic
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreePaths
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeActionDefinitions

namespace OAI

/-! Fixed paths and branching for group actions on simplicial trees. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V)

lemma stabilizer_smul (g : G) (v : V) :
    MulAction.stabilizer G (g • v)=conjugate g (MulAction.stabilizer G v) := by
  ext a
  rw [mem_conjugate,MulAction.mem_stabilizer_iff,MulAction.mem_stabilizer_iff,
    ←smul_left_cancel_iff g⁻¹]
  simp only [smul_smul,inv_mul_cancel,one_smul,mul_assoc]

lemma pairStabilizer_smul (g : G) (u v : V) :
    pairStabilizer (G := G) (g • u) (g • v)=conjugate g (pairStabilizer (G := G) u v) := by
  rw [pairStabilizer,stabilizer_smul,stabilizer_smul,←conjugate_inf]
  rfl

/-- An element fixing the endpoints of a tree path fixes each vertex of it. -/
theorem fixes_path (hT : T.IsAcyclic) (hA : PreservesAdj (G := G) T)
    {u v : V} (p : T.Walk u v) (hp : p.IsPath) (g : G)
    (hu : g • u=u) (hv : g • v=v) (n : ℕ) : g • p.getVert n=p.getVert n := by
  let q := (p.map (translate T hA g)).copy hu hv
  have hq : q.IsPath := by
    apply (SimpleGraph.Walk.isPath_copy _ _ _).mpr
    exact hp.map (MulAction.toPerm g).injective
  have he : q=p := congrArg Subtype.val (hT.subsingleton_path u v |>.elim ⟨q,hq⟩ ⟨p,hp⟩)
  have hh := congrArg (fun r : T.Walk u v => r.getVert n) he
  calc
    g • p.getVert n = (p.map (translate T hA g)).getVert n :=
      (SimpleGraph.Walk.getVert_map (translate T hA g) p n).symm
    _ = q.getVert n := (SimpleGraph.Walk.getVert_copy _ n hu hv).symm
    _ = p.getVert n := hh

theorem fixes_path_support (hT : T.IsAcyclic) (hA : PreservesAdj (G := G) T)
    {u v : V} (p : T.Walk u v) (hp : p.IsPath) (g : G)
    (hu : g • u=u) (hv : g • v=v) {w : V} (hw : w∈p.support) : g • w=w := by
  have h := fixes_path T hT hA p hp g hu hv (p.support.idxOf w)
  simpa only [SimpleGraph.Walk.getVert_support_idxOf _ hw] using h

/-- Endpoint stabilizers also fix all intermediate vertices. -/
lemma pairStabilizer_le_at_path (hT : T.IsAcyclic) (hA : PreservesAdj (G := G) T)
    {u v : V} (p : T.Walk u v) (hp : p.IsPath) {w : V} (hw : w∈p.support) :
    pairStabilizer (G := G) u v≤MulAction.stabilizer G w := by
  intro g hg
  exact fixes_path_support T hT hA p hp g hg.1 hg.2 hw

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
