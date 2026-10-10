import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeMinimalPair

namespace OAI

/-! A minimal segment stabilizer in a branching tree action is normal when
adjacent vertex stabilizers generate the acting group. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (hT : T.IsAcyclic) (hA : PreservesAdj (G := G) T)
include hT hA

theorem minimal_pair_normal (u v : V) (hne : u≠v)
    (hmin : ∀ a b : V, a≠b → pairStabilizer (G := G) a b≤pairStabilizer (G := G) u v →
      pairStabilizer (G := G) a b=pairStabilizer (G := G) u v)
    (p : T.Walk v u) (hp : p.IsPath)
    (hbranch : ∀ v w : V, T.Adj v w → ∃ a : G, a • v=v ∧ a • w≠w)
    (hgen : ∀ v w : V, T.Adj v w →
      MulAction.stabilizer G v ⊔ MulAction.stabilizer G w=⊤) :
    (pairStabilizer (G := G) u v).Normal := by
  let P := pairStabilizer (G := G) u v
  have hnV := minimal_pair_endpoint T hT hA u v hne hmin p hp (hbranch v)
  have hpnot : ¬p.Nil := fun h => hne (hp.nil_iff_eq.mp h).symm
  obtain ⟨a,ha,haw⟩ := hbranch v p.snd (p.adj_snd hpnot)
  have haN : conjugate a P=P := (mem_normalizer_iff_conjugate a P).mp (hnV ha)
  have hadj : T.Adj v (a • p.snd) := by
    have h := hA a (p.adj_snd hpnot)
    rwa [ha] at h
  have hfix : P≤MulAction.stabilizer G (a • p.snd) := by
    rw [stabilizer_smul,←haN]
    apply conjugate_mono
    exact pairStabilizer_le_at_path T hT hA p.reverse hp.reverse
      (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse]
        using p.getVert_mem_support 1)
  have he : pairStabilizer (G := G) u (a • p.snd)=P :=
    extended_pair T hT hA u v (a • p.snd) p hp hadj haw hfix
  have hne' : u≠a • p.snd := by
    intro hu
    have hmem : a • p.snd∈p.support := hu ▸ p.end_mem_support
    exact haw (hT.eq_snd_of_adj_start hp hadj hmem)
  have hmin' : ∀ x y : V, x≠y →
      pairStabilizer (G := G) x y≤pairStabilizer (G := G) u (a • p.snd) →
      pairStabilizer (G := G) x y=pairStabilizer (G := G) u (a • p.snd) := by
    intro x y hxy hle
    rw [he] at hle ⊢
    exact hmin x y hxy hle
  have hpath := reverse_concat_isPath T hT p hp hadj haw
  have hnW := minimal_pair_endpoint T hT hA u (a • p.snd) hne' hmin'
    (p.reverse.concat hadj).reverse hpath.reverse (hbranch (a • p.snd))
  rw [he] at hnW
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_le_iff.mp
  rw [←hgen v (a • p.snd) hadj]
  exact sup_le hnV hnW

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
