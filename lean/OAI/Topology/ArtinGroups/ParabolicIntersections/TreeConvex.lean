import OAI.Topology.ArtinGroups.ParabolicIntersections.OrbitEdgeGraph

namespace OAI

/-! Convex vertex sets and boundary edges in a simplicial tree. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]

lemma orbit_pathClosed (T : SimpleGraph V) (hT : T.IsAcyclic)
    (hA : PreservesAdj (G := G) T) (P : Subgroup G) (u v : V) (huv : T.Adj u v)
    {A : Set G} (hP : P=Subgroup.closure A)
    (hgen : ∀ a∈A,a • u=u ∨ a • v=v) : PathClosed T (orbitVertices P u v) := by
  intro x y hx hy p hp w hw
  have hr := (orbit_reachable (hne := huv.ne) hP hgen hx).symm.trans
    (orbit_reachable (hne := huv.ne) hP hgen hy)
  obtain ⟨q,hq⟩ := hr.exists_isPath
  have hle := orbit_graph_le (P := P) (hne := huv.ne) T hA huv
  have hqm : (q.mapLe hle).IsPath := hq.map Function.injective_id
  have he : q.mapLe hle=p :=
    congrArg Subtype.val (hT.subsingleton_path x y |>.elim ⟨_,hqm⟩ ⟨p,hp⟩)
  have hwq : w∈q.support := by
    rw [←SimpleGraph.Walk.support_mapLe_eq_support hle q,he]
    exact hw
  exact orbit_walk_support q hx w hwq

lemma pathClosed_smul (T : SimpleGraph V) (hA : PreservesAdj (G := G) T)
    {U : Set V} (hU : PathClosed T U) (g : G) : PathClosed T ((g • ·) '' U) := by
  intro x y hx hy p hp w hw
  have hx' : g⁻¹ • x∈U := by
    obtain ⟨a,ha,rfl⟩ := hx
    simpa only [inv_smul_smul] using ha
  have hy' : g⁻¹ • y∈U := by
    obtain ⟨a,ha,rfl⟩ := hy
    simpa only [inv_smul_smul] using ha
  have hm : g⁻¹ • w∈(p.map (translate T hA g⁻¹)).support := by
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨w,hw,rfl⟩
  have hmem := hU hx' hy' _ (hp.map (MulAction.toPerm g⁻¹).injective) _ hm
  exact ⟨g⁻¹ • w,hmem,smul_inv_smul g w⟩

lemma exists_boundary_edge (T : SimpleGraph V) {U : Set V} {u v : V}
    (hu : u∈U) (hv : v∉U) (p : T.Walk u v) :
    ∃ x y,T.Adj x y ∧ x∈U ∧ y∉U := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons u w v h p ih =>
    by_cases hw : w∈U
    · exact ih hw hv
    · exact ⟨u,w,h,hu,hw⟩

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
