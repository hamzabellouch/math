import Mathlib
import OAI.Topology.ArtinGroups.Quivers.SmulMul

namespace OAI

namespace HarmonicArtin.ReversibleQuiver

abbrev Path (V A : Type*) := V ⊕ A ⊕ V

namespace Path

variable {V A : Type*} (Q : ReversibleQuiver V A)

def source : Path V A → V
  | .inl v => v
  | .inr (.inl a) => Q.source a
  | .inr (.inr v) => v

def target : Path V A → V
  | .inl v => v
  | .inr (.inl a) => Q.target a
  | .inr (.inr v) => v

def length : Path V A → ℤ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

end Path

namespace Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]

local instance pathModule : Module K (Q.Zigzag K) :=
  inferInstanceAs (Module K ((V → K) × (A → K) × (V → K)))

def pathCoordinates : Q.Zigzag K ≃ₗ[K] (Path V A → K) where
  toFun x := Sum.elim x.vertex (Sum.elim x.arrow x.token)
  invFun f := (fun v => f (.inl v), (fun a => f (.inr (.inl a))),
    fun v => f (.inr (.inr v)))
  left_inv x := by rfl
  right_inv f := by funext p; rcases p with v | a | v <;> rfl
  map_add' x y := by funext p; rcases p with v | a | v <;> rfl
  map_smul' r x := by funext p; rcases p with v | a | v <;> rfl

@[simp] lemma pathCoordinates_vertex (x : Q.Zigzag K) (v : V) :
    pathCoordinates Q x (.inl v) = x.vertex v := rfl
@[simp] lemma pathCoordinates_arrow (x : Q.Zigzag K) (a : A) :
    pathCoordinates Q x (.inr (.inl a)) = x.arrow a := rfl
@[simp] lemma pathCoordinates_token (x : Q.Zigzag K) (v : V) :
    pathCoordinates Q x (.inr (.inr v)) = x.token v := rfl

variable [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def pathBasis : Module.Basis (Path V A) K (Q.Zigzag K) :=
  Module.Basis.ofEquivFun (pathCoordinates Q)

omit [DecidableEq A] in
lemma pathBasis_repr (x : Q.Zigzag K) (p : Path V A) :
    (pathBasis Q).repr x p = pathCoordinates Q x p := rfl

lemma pathBasis_coordinates (p q : Path V A) :
    pathCoordinates Q (pathBasis Q (K := K) p) q = if p = q then 1 else 0 := by
  exact (pathBasis Q).repr_self_apply p q

omit [DecidableEq A] in
lemma sum_pathBasis (x : Q.Zigzag K) :
    ∑ p, pathCoordinates Q x p • pathBasis Q p = x := (pathBasis Q).sum_repr x

lemma pathBasis_vertex (v : V) : pathBasis Q (K := K) (.inl v) = vertexId Q v := by
  apply (pathCoordinates Q).injective
  funext p
  rw [pathBasis_coordinates]
  rcases p with w | a | w
  all_goals simp only [pathCoordinates_vertex, pathCoordinates_arrow, pathCoordinates_token]
  all_goals simp [vertexId, vertex, arrow, token, Pi.single_apply, eq_comm]

lemma pathBasis_arrow (a : A) : pathBasis Q (K := K) (.inr (.inl a)) = arrowBasis Q a := by
  apply (pathCoordinates Q).injective
  funext p
  rw [pathBasis_coordinates]
  rcases p with w | b | w
  all_goals simp only [pathCoordinates_vertex, pathCoordinates_arrow, pathCoordinates_token]
  all_goals simp [arrowBasis, vertex, arrow, token, Pi.single_apply, eq_comm]

lemma pathBasis_token (v : V) : pathBasis Q (K := K) (.inr (.inr v)) = tokenBasis Q v := by
  apply (pathCoordinates Q).injective
  funext p
  rw [pathBasis_coordinates]
  rcases p with w | a | w
  all_goals simp only [pathCoordinates_vertex, pathCoordinates_arrow, pathCoordinates_token]
  all_goals simp [tokenBasis, vertex, arrow, token, Pi.single_apply, eq_comm]

omit [Fintype V] [DecidableEq A] in
lemma coordinates_vertexId_left (v : V) (x : Q.Zigzag K) (p : Path V A) :
    pathCoordinates Q (vertexId Q v * x) p =
      if Path.source Q p = v then pathCoordinates Q x p else 0 := by
  rcases p with w | a | w
  · simp [Path.source, Pi.single_apply]
    rfl
  · simp [Path.source, leftScale, rightScale, Pi.single_apply]
    rfl
  · simp [Path.source, Pi.single_apply]
    rfl

omit [Fintype V] [DecidableEq A] in
lemma coordinates_vertexId_right (v : V) (x : Q.Zigzag K) (p : Path V A) :
    pathCoordinates Q (x * vertexId Q v) p =
      if Path.target Q p = v then pathCoordinates Q x p else 0 := by
  rcases p with w | a | w
  · simp [Path.target, Pi.single_apply]
    rfl
  · simp [Path.target, leftScale, rightScale, Pi.single_apply]
    rfl
  · simp [Path.target, Pi.single_apply]
    rfl

lemma pathBasis_left (p : Path V A) :
    vertexId Q (Path.source Q p) * pathBasis Q (K := K) p = pathBasis Q p := by
  apply (pathCoordinates Q).injective
  funext q
  rw [coordinates_vertexId_left, pathBasis_coordinates]
  by_cases h : p = q
  · subst q
    simp
  · simp [h]

lemma pathBasis_right (p : Path V A) :
    pathBasis Q (K := K) p * vertexId Q (Path.target Q p) = pathBasis Q p := by
  apply (pathCoordinates Q).injective
  funext q
  rw [coordinates_vertexId_right, pathBasis_coordinates]
  by_cases h : p = q
  · subst q
    simp
  · simp [h]

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma coordinates_homogeneous (a : ℤ) (x : Q.Zigzag K) :
    Homogeneous Q a x ↔ ∀ p, Path.length p ≠ a → pathCoordinates Q x p = 0 := by
  constructor
  · intro h p hp
    rcases p with v | b | v
    · exact congrFun (h.1 (Ne.symm hp)) v
    · exact congrFun (h.2.1 (Ne.symm hp)) b
    · exact congrFun (h.2.2 (Ne.symm hp)) v
  · intro h
    constructor
    · intro ha
      funext v
      exact h (.inl v) (Ne.symm ha)
    constructor
    · intro ha
      funext b
      exact h (.inr (.inl b)) (Ne.symm ha)
    · intro ha
      funext v
      exact h (.inr (.inr v)) (Ne.symm ha)

lemma pathBasis_homogeneous (p : Path V A) :
    Homogeneous Q (Path.length p) (pathBasis Q (K := K) p) := by
  rw [coordinates_homogeneous]
  intro q hq
  rw [pathBasis_coordinates, ite_eq_right]
  intro hp
  exact hq (congrArg Path.length hp.symm)

omit [Fintype V] [DecidableEq A] in
lemma coordinates_corner {s t : V} {x : Q.Zigzag K}
    (hl : vertexId Q s * x = x) (hr : x * vertexId Q t = x)
    {p : Path V A} (hp : pathCoordinates Q x p ≠ 0) :
    Path.source Q p = s ∧ Path.target Q p = t := by
  constructor
  · by_contra h
    have he := congrArg (fun z => pathCoordinates Q z p) hl
    rw [coordinates_vertexId_left, ite_eq_right h] at he
    exact hp he.symm
  · by_contra h
    have he := congrArg (fun z => pathCoordinates Q z p) hr
    rw [coordinates_vertexId_right, ite_eq_right h] at he
    exact hp he.symm

omit [Fintype V] [DecidableEq A] in
lemma coordinates_mul_degree {a b : ℤ} {x y : Q.Zigzag K}
    (hx : Homogeneous Q a x) (hy : Homogeneous Q b y) {p : Path V A}
    (hp : pathCoordinates Q (x * y) p ≠ 0) : Path.length p = a + b := by
  by_contra h
  exact hp ((coordinates_homogeneous Q (a + b) (x * y)).mp (homogeneous_mul Q hx hy) p h)

end Zigzag
end HarmonicArtin.ReversibleQuiver

end OAI
