import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeBranch
import OAI.Topology.ArtinGroups.ParabolicIntersections.NormalizerAlgebra

namespace OAI

/-! A minimal segment stabilizer is normalized by its endpoint stabilizers. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (hT : T.IsAcyclic) (hA : PreservesAdj (G := G) T)
include hT hA

theorem minimal_pair_endpoint (u v : V) (hne : u≠v)
    (hmin : ∀ a b : V, a≠b → pairStabilizer (G := G) a b≤pairStabilizer (G := G) u v →
      pairStabilizer (G := G) a b=pairStabilizer (G := G) u v)
    (p : T.Walk v u) (hp : p.IsPath)
    (hbranch : ∀ w : V, T.Adj v w → ∃ a : G, a • v=v ∧ a • w≠w) :
    MulAction.stabilizer G v≤Subgroup.normalizer (pairStabilizer (G := G) u v : Set G) := by
  let P := pairStabilizer (G := G) u v
  let C := MulAction.stabilizer G v ⊓ MulAction.stabilizer G p.snd
  have hpnot : ¬p.Nil := fun h => hne (hp.nil_iff_eq.mp h).symm
  obtain ⟨a,ha,haw⟩ := hbranch p.snd (p.adj_snd hpnot)
  have haC : a∉C := fun h => haw h.2
  apply le_normalizer_of_outside P (MulAction.stabilizer G v) C ⟨a,ha,haC⟩
  have hle (g : G) (hg : g • v=v) (hw : g • p.snd≠p.snd) : P≤conjugate g P := by
    have hne' : u≠g • u := (moved_first_vertex_ne_endpoint T hT hA p hp g hg hw).symm
    have he := reflected_pair T hT hA u v p hp g hg hw
    have hm := hmin u (g • u) hne' (by rw [he]; exact inf_le_left)
    rw [he] at hm
    have hi : P ⊓ conjugate g P≤conjugate g P := inf_le_right
    rwa [hm] at hi
  intro g hg hgC
  have hw : g • p.snd≠p.snd := fun h => hgC ⟨hg,h⟩
  have hgi : g⁻¹ • v=v := by
    have hh := congrArg (fun x : V => g⁻¹ • x) hg
    simpa only [inv_smul_smul] using hh.symm
  have hwi : g⁻¹ • p.snd≠p.snd := by
    intro h
    have hh := congrArg (fun x : V => g • x) h
    exact hw (by simpa only [smul_inv_smul] using hh.symm)
  apply le_antisymm
  · have h := conjugate_mono g (hle g⁻¹ hgi hwi)
    simpa only [←conjugate_mul,mul_inv_cancel,conjugate_one] using h
  · exact hle g hg hw

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
