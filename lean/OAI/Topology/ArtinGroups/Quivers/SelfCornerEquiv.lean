import Mathlib
import OAI.Topology.ArtinGroups.Quivers.CotestPlacement

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I : Type*} (Q : ReversibleQuiver V A)

def selfCornerEquiv (hn : ∀ a, Q.source a ≠ Q.target a) (α : V) :
    Bool ≃ CornerPath Q α α where
  toFun b := if b then ⟨.inr (.inr α), rfl, rfl⟩ else ⟨.inl α, rfl, rfl⟩
  invFun p := match p.val with
    | .inl _ => false
    | .inr (.inl _) => false
    | .inr (.inr _) => true
  left_inv b := by cases b <;> rfl
  right_inv p := by
    rcases p with ⟨v | a | v, hs, ht⟩
    · apply Subtype.ext
      change Sum.inl α = Sum.inl v
      exact congrArg Sum.inl hs.symm
    · exact (hn a (hs.trans ht.symm)).elim
    · apply Subtype.ext
      change Sum.inr (Sum.inr α) = Sum.inr (Sum.inr v)
      exact congrArg (fun x => Sum.inr (Sum.inr x)) hs.symm

@[simp] lemma selfCornerEquiv_false (hn : ∀ a, Q.source a ≠ Q.target a) (α : V) :
    ((selfCornerEquiv Q hn α) false).val = .inl α := rfl
@[simp] lemma selfCornerEquiv_true (hn : ∀ a, Q.source a ≠ Q.target a) (α : V) :
    ((selfCornerEquiv Q hn α) true).val = .inr (.inr α) := rfl

variable [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma diagonal_corner_decomposition (hn : ∀ a, Q.source a ≠ Q.target a)
    (α : V) (x : Q.Zigzag K) (hl : vertexId Q α * x = x)
    (hr : x * vertexId Q α = x) :
    x = x.vertex α • vertexId Q α + x.token α • tokenBasis Q α := by
  calc
    x = ∑ p : CornerPath Q α α, pathCoordinates Q x p.val • pathBasis Q p.val :=
      (sum_cornerPath Q x hl hr).symm
    _ = ∑ b : Bool, pathCoordinates Q x ((selfCornerEquiv Q hn α) b).val •
        pathBasis Q ((selfCornerEquiv Q hn α) b).val :=
      (Equiv.sum_comp (selfCornerEquiv Q hn α) _).symm
    _ = _ := by simpa only [Fintype.sum_bool, selfCornerEquiv_false, selfCornerEquiv_true,
      pathCoordinates_vertex, pathCoordinates_token, pathBasis_vertex, pathBasis_token]
      using add_comm (x.token α • tokenBasis Q α) (x.vertex α • vertexId Q α)

lemma cornerPath_basis_dual_token {α β : V} (u v : CornerPath Q α β) :
    (pathBasis Q (K := K) u.val * pathBasis Q (Path.dual Q v.val)).token α =
      if u = v then 1 else 0 := by
  have hl : vertexId Q α * (pathBasis Q (K := K) u.val *
      pathBasis Q (Path.dual Q v.val)) =
      pathBasis Q u.val * pathBasis Q (Path.dual Q v.val) := by
    rw [← _root_.mul_assoc, cornerPath_left]
  have hc := coordinates_vertexId_left Q α
    (pathBasis Q (K := K) u.val * pathBasis Q (Path.dual Q v.val))
  have ht : trace Q (pathBasis Q (K := K) u.val * pathBasis Q (Path.dual Q v.val)) =
      (pathBasis Q (K := K) u.val * pathBasis Q (Path.dual Q v.val)).token α := by
    unfold trace
    apply Finset.sum_eq_single α
    · intro β _ hb
      have he := hc (.inr (.inr β))
      rw [hl] at he
      simpa [Path.source, hb] using he
    · simp
  rw [← ht, ← coordinates_trace, pathBasis_coordinates]
  simp only [Subtype.ext_iff]

noncomputable def unitContraction (p : I → GeneratorPlacement V) (α : V) :
    Matrix (TestIndex Q p α) (TestIndex Q p α) (Q.Zigzag K) := by
  classical
  exact fun u v => if u.1 = v.1 then
    (pathBasis Q (K := K) u.2.val * pathBasis Q (Path.dual Q v.2.val)).vertex α •
      vertexId Q α else 0

noncomputable def testToken [DecidableEq I] (p : I → GeneratorPlacement V) (α : V) :
    Matrix (TestIndex Q p α) (TestIndex Q p α) (Q.Zigzag K) :=
  Matrix.diagonal (fun _ => tokenBasis Q α)

lemma evaluation_coevaluation [Fintype I] [DecidableEq I]
    (hn : ∀ a, Q.source a ≠ Q.target a) (p : I → GeneratorPlacement V) (α : V) :
    evaluationMatrix Q p α (K := K) * coevaluationMatrix Q p α (K := K) =
      unitContraction Q p α + testToken Q p α := by
  apply Matrix.ext
  intro u v
  rw [evaluation_mul]
  dsimp only [coevaluationMatrix]
  by_cases hi : u.1 = v.1
  · rcases u with ⟨i, u⟩
    rcases v with ⟨j, v⟩
    dsimp only at hi
    subst j
    rw [ite_eq_left rfl]
    have hl : vertexId Q α * (pathBasis Q (K := K) u.val * pathBasis Q (Path.dual Q v.val)) =
        pathBasis Q u.val * pathBasis Q (Path.dual Q v.val) := by
      rw [← _root_.mul_assoc, cornerPath_left]
    have hr : (pathBasis Q (K := K) u.val * pathBasis Q (Path.dual Q v.val)) * vertexId Q α =
        pathBasis Q u.val * pathBasis Q (Path.dual Q v.val) := by
      rw [_root_.mul_assoc]
      exact congrArg (fun z => pathBasis Q (K := K) u.val * z)
        (cornerPath_right Q (K := K) ((cornerDual Q α (p i).color) v))
    rw [diagonal_corner_decomposition Q hn α _ hl hr, cornerPath_basis_dual_token]
    simp only [Matrix.add_apply, unitContraction, testToken, Matrix.diagonal_apply, ite_true]
    by_cases hp : u = v
    · subst v
      simp
    · simp [hp]
  · have huv : u ≠ v := fun h => hi (congrArg Sigma.fst h)
    simp only [ite_eq_right hi, MulZeroClass.mul_zero, unitContraction, testToken,
      Matrix.add_apply, Matrix.diagonal_apply, ite_eq_right huv, add_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
