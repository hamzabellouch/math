import Mathlib
import OAI.Topology.ArtinGroups.Quivers.CornerPath

namespace OAI

namespace HarmonicArtin.ReversibleQuiver

namespace Path

variable {V A : Type*} (Q : ReversibleQuiver V A)

def dual : Path V A → Path V A
  | .inl v => .inr (.inr v)
  | .inr (.inl a) => .inr (.inl (Q.reverse a))
  | .inr (.inr v) => .inl v

@[simp] lemma dual_dual (p : Path V A) : dual Q (dual Q p) = p := by
  rcases p with v | a | v <;> simp [dual]

@[simp] lemma source_dual (p : Path V A) : source Q (dual Q p) = target Q p := by
  rcases p with v | a | v
  · rfl
  · exact Q.source_reverse a
  · rfl

@[simp] lemma target_dual (p : Path V A) : target Q (dual Q p) = source Q p := by
  rcases p with v | a | v
  · rfl
  · exact Q.target_reverse a
  · rfl

lemma length_dual (p : Path V A) : length (dual Q p) = 2 - length p := by
  rcases p with v | a | v <;> rfl

end Path

namespace Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

def cornerDual (s t : V) : CornerPath Q s t ≃ CornerPath Q t s where
  toFun p := ⟨Path.dual Q p.val, by simpa only [Path.source_dual, Path.target_dual] using p.property.symm⟩
  invFun p := ⟨Path.dual Q p.val, by simpa only [Path.source_dual, Path.target_dual] using p.property.symm⟩
  left_inv p := by apply Subtype.ext; exact Path.dual_dual Q p.val
  right_inv p := by apply Subtype.ext; exact Path.dual_dual Q p.val

lemma coordinates_trace (x : Q.Zigzag K) (p : Path V A) :
    pathCoordinates Q x p = trace Q (x * pathBasis Q (Path.dual Q p)) := by
  rcases p with v | a | v
  · simp only [Path.dual, pathBasis_token, trace_mul_tokenBasis, pathCoordinates_vertex]
  · simp only [Path.dual, pathBasis_arrow, trace_mul_arrowBasis, pathCoordinates_arrow]
  · rw [Path.dual, pathBasis_vertex]
    exact (trace_mul_vertexBasis Q x v).symm

omit [DecidableEq A] in
lemma sum_dual_cornerPath {s t : V} (x : Q.Zigzag K)
    (hl : vertexId Q t * x = x) (hr : x * vertexId Q s = x) :
    ∑ p : CornerPath Q s t, pathCoordinates Q x (Path.dual Q p.val) •
      pathBasis Q (Path.dual Q p.val) = x := by
  classical
  calc
    _ = ∑ p : CornerPath Q t s, pathCoordinates Q x p.val • pathBasis Q p.val := by
      apply Fintype.sum_equiv (cornerDual Q s t)
      intro p
      rfl
    _ = x := sum_cornerPath Q x hl hr

lemma dual_right_action {s t α : V} (x : Q.Zigzag K)
    (hl : vertexId Q s * x = x)
    (q : CornerPath Q α t) :
    ∑ p : CornerPath Q α s, pathCoordinates Q (pathBasis Q p.val * x) q.val •
      pathBasis Q (Path.dual Q p.val) = x * pathBasis Q (Path.dual Q q.val) := by
  have hl' : vertexId Q s * (x * pathBasis Q (Path.dual Q q.val)) =
      x * pathBasis Q (Path.dual Q q.val) := by
    rw [← _root_.mul_assoc, hl]
  have hr' : (x * pathBasis Q (Path.dual Q q.val)) * vertexId Q α =
      x * pathBasis Q (Path.dual Q q.val) := by
    rw [_root_.mul_assoc]
    exact congrArg (fun z => x * z) (cornerPath_right Q ((cornerDual Q α t) q))
  conv_rhs => rw [← sum_dual_cornerPath Q _ hl' hr']
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  rw [coordinates_trace, coordinates_trace, Path.dual_dual]
  rw [trace_mul_comm Q (x * pathBasis Q (Path.dual Q q.val)) (pathBasis Q p.val)]
  exact congrArg (trace Q) (_root_.mul_assoc _ _ _)

end Zigzag
end HarmonicArtin.ReversibleQuiver

end OAI
