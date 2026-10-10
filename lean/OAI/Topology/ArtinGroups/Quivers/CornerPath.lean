import Mathlib
import OAI.Topology.ArtinGroups.Quivers.Path

namespace OAI

namespace HarmonicArtin.ReversibleQuiver

namespace Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

abbrev CornerPath (s t : V) := {p : Path V A // Path.source Q p = s ∧ Path.target Q p = t}

omit [Fintype V] [DecidableEq A] in
lemma coordinates_zero (p : Path V A) : pathCoordinates Q (0 : Q.Zigzag K) p = 0 := by
  rcases p with v | a | v <;> rfl

omit [Fintype V] [DecidableEq A] in
lemma coordinates_add (x y : Q.Zigzag K) (p : Path V A) :
    pathCoordinates Q (x + y) p = pathCoordinates Q x p + pathCoordinates Q y p := by
  rcases p with v | a | v <;> rfl

omit [Fintype V] [DecidableEq A] in
lemma coordinates_smul (r : K) (x : Q.Zigzag K) (p : Path V A) :
    pathCoordinates Q (r • x) p = r * pathCoordinates Q x p := by
  rcases p with v | a | v <;> rfl

omit [Fintype V] [DecidableEq A] in
lemma coordinates_sum {B : Type*} (T : Finset B) (f : B → Q.Zigzag K) (p : Path V A) :
    pathCoordinates Q (∑ b ∈ T, f b) p = ∑ b ∈ T, pathCoordinates Q (f b) p := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [coordinates_zero]
  | @insert b T hb ih => simp [Finset.sum_insert hb, coordinates_add, ih]

omit [DecidableEq A] in
lemma sum_cornerPath {s t : V} (x : Q.Zigzag K)
    (hl : vertexId Q s * x = x) (hr : x * vertexId Q t = x) :
    ∑ p : CornerPath Q s t, pathCoordinates Q x p.val • pathBasis Q p.val = x := by
  classical
  conv_rhs => rw [← sum_pathBasis Q x]
  apply Fintype.sum_of_injective (fun p : CornerPath Q s t => p.val) Subtype.val_injective
  · intro p hp
    have hz : pathCoordinates Q x p = 0 := by
      by_contra h
      have hc := coordinates_corner Q hl hr h
      exact hp ⟨⟨p, hc⟩, rfl⟩
    rw [hz, zero_smul]
  · intro p
    rfl

lemma cornerPath_left {s t : V} (p : CornerPath Q s t) :
    vertexId Q s * pathBasis Q (K := K) p.val = pathBasis Q p.val := by
  simpa only [p.property.1] using pathBasis_left Q (K := K) p.val

lemma cornerPath_right {s t : V} (p : CornerPath Q s t) :
    pathBasis Q (K := K) p.val * vertexId Q t = pathBasis Q p.val := by
  simpa only [p.property.2] using pathBasis_right Q (K := K) p.val

omit [DecidableEq A] in
lemma sum_cornerPath_mul {s t : V} (x y : Q.Zigzag K)
    (hl : vertexId Q s * x = x) (hr : x * vertexId Q t = x) :
    ∑ p : CornerPath Q s t, pathCoordinates Q x p.val • (pathBasis Q p.val * y) = x * y := by
  conv_rhs => rw [← sum_cornerPath Q x hl hr]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  exact (smul_mul Q _ _ _).symm

omit [DecidableEq A] in
lemma coordinates_mul_expansion {s t : V} (x y : Q.Zigzag K)
    (hl : vertexId Q s * x = x) (hr : x * vertexId Q t = x) (r : Path V A) :
    ∑ p : CornerPath Q s t, pathCoordinates Q x p.val *
      pathCoordinates Q (pathBasis Q p.val * y) r = pathCoordinates Q (x * y) r := by
  rw [← sum_cornerPath_mul Q x y hl hr, coordinates_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact (coordinates_smul Q _ _ _).symm

end Zigzag
end HarmonicArtin.ReversibleQuiver

end OAI
