import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeActionDefinitions

namespace OAI

/-!
# Finite translates of a segment inside a finite path

This is the finite-pattern input for constructing an acylindrical graph
from a tree action. The segment is in the actual tree and its pointwise
stabilizer is trivial; its occurrences are group elements, not formal labels.
-/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]

lemma pair_orbit_injective {u v : V} (h : pairStabilizer (G := G) u v=⊥) :
    Function.Injective (fun g : G => (g • u,g • v)) := by
  intro a b hab
  have hu : a • u=b • u := congrArg Prod.fst hab
  have hv : a • v=b • v := congrArg Prod.snd hab
  have hm : b⁻¹*a∈pairStabilizer (G := G) u v := by
    constructor
    · change (b⁻¹*a) • u=u
      rw [mul_smul,hu,inv_smul_smul]
    · change (b⁻¹*a) • v=v
      rw [mul_smul,hv,inv_smul_smul]
  rw [h,Subgroup.mem_bot] at hm
  exact (inv_mul_eq_one.mp hm).symm

/-- Group translates whose two endpoints occur in a specified finite path. -/
def segmentOccurrences (u v : V) (T : SimpleGraph V) {x y : V} (p : T.Walk x y) : Set G :=
  {g | g • u∈p.support ∧ g • v∈p.support}

lemma segmentOccurrences_finite {u v : V} (h : pairStabilizer (G := G) u v=⊥)
    (T : SimpleGraph V) {x y : V} (p : T.Walk x y) :
    (segmentOccurrences (G := G) u v T p).Finite := by
  let A : Set V := {w | w∈p.support}
  have hA : A.Finite := p.support.finite_toSet
  have hprod : (A×ˢA).Finite := hA.prod hA
  exact hprod.preimage (pair_orbit_injective h).injOn

/-- A path contains a translate of the fixed segment. In a tree the
endpoint condition also puts the entire translated segment in the path. -/
def ContainsSegment (u v : V) (T : SimpleGraph V) {x y : V} (p : T.Walk x y) : Prop :=
  (segmentOccurrences (G := G) u v T p).Nonempty


lemma segmentOccurrences_reverse (u v : V) (T : SimpleGraph V) {x y : V} (p : T.Walk x y) :
    segmentOccurrences (G := G) u v T p.reverse=segmentOccurrences u v T p := by
  ext g
  simp only [segmentOccurrences,Set.mem_ofPred_eq,SimpleGraph.Walk.support_reverse,List.mem_reverse]

lemma segmentOccurrences_subpath (u v : V) (T : SimpleGraph V) {x y a b : V}
    (p : T.Walk x y) (q : T.Walk a b) (hq : q.support.Sublist p.support) :
    segmentOccurrences (G := G) u v T q⊆segmentOccurrences u v T p := by
  intro g hg
  exact ⟨hq.subset hg.1,hq.subset hg.2⟩

lemma smul_mem_mapped_support (T : SimpleGraph V) (hA : PreservesAdj (G := G) T)
    {x y w : V} (p : T.Walk x y) (g h : G) :
    h • w∈(p.map (translate T hA g)).support ↔ (g⁻¹*h) • w∈p.support := by
  rw [SimpleGraph.Walk.support_map]
  constructor
  · intro hm
    obtain ⟨z,hz,he⟩ := List.mem_map.mp hm
    change g • z=h • w at he
    have hzw : z=(g⁻¹*h) • w := by
      have hh := congrArg (fun t : V => g⁻¹ • t) he
      simpa only [←mul_smul,inv_mul_cancel,one_smul] using hh
    exact hzw ▸ hz
  · intro hh
    refine List.mem_map.mpr ⟨(g⁻¹*h) • w,hh,?_⟩
    change g • ((g⁻¹*h) • w)=h • w
    rw [←mul_smul,mul_inv_cancel_left]

lemma segmentOccurrences_map (u v : V) (T : SimpleGraph V)
    (hA : PreservesAdj (G := G) T) {x y : V} (p : T.Walk x y) (g h : G) :
    h∈segmentOccurrences (G := G) u v T (p.map (translate T hA g)) ↔
      g⁻¹*h∈segmentOccurrences u v T p := by
  exact and_congr (smul_mem_mapped_support T hA p g h)
    (smul_mem_mapped_support T hA p g h)

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
