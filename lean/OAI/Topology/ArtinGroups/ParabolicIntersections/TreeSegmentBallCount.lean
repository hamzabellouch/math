import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeSegmentOccurrences
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeBallCount

namespace OAI

/-! Uniform counts for translates of a free segment near a path vertex. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (u v : V)

def localSegmentOccurrences {x y : V} (p : T.Walk x y) (b : V) (L : ℕ) : Set G :=
  {g | (g • u∈p.support ∧ T.dist b (g • u)≤L) ∧
    (g • v∈p.support ∧ T.dist b (g • v)≤L)}

/-- The bound is independent of the path length and of vertex valences. -/
theorem localSegmentOccurrences_bound (hT : T.IsTree)
    (hfree : pairStabilizer (G := G) u v=⊥)
    {x y b : V} (p : T.Walk x y) (hp : p.IsPath) (hb : b∈p.support) (L : ℕ) :
    (localSegmentOccurrences (G := G) T u v p b L).Finite ∧
      (localSegmentOccurrences (G := G) T u v p b L).ncard≤(2*L+1)^2 := by
  let B : Set V := {w | w∈p.support ∧ T.dist b w≤L}
  have hB : B.Finite := p.support.finite_toSet.subset (fun _ hw => hw.1)
  have hcard : B.ncard≤2*L+1 := path_ball_ncard T hT p hp hb L
  have hpair := pair_orbit_injective hfree
  have hfin : (localSegmentOccurrences (G := G) T u v p b L).Finite :=
    (hB.prod hB).preimage hpair.injOn
  refine ⟨hfin,?_⟩
  calc
    (localSegmentOccurrences (G := G) T u v p b L).ncard ≤ (B×ˢB).ncard :=
      Set.ncard_le_ncard_of_injOn (fun g : G => (g • u,g • v))
        (fun _ hg => hg) hpair.injOn (hB.prod hB)
    _ = B.ncard*B.ncard := Set.ncard_prod
    _ ≤ (2*L+1)*(2*L+1) := Nat.mul_le_mul hcard hcard
    _ = (2*L+1)^2 := (pow_two _).symm

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
