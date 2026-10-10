import OAI.RepresentationTheory.YoungSymmetry.UnitaryModel

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace RowColumn
open CubeShuffle CubeShuffle.Specht CubeShuffle.UnitaryFinite

/-- Permutations preserving each fibre of a given line map. -/
def lineGroup {α β : Type*} (f : α → β) : Subgroup (Equiv.Perm α) where
  carrier := {g | ∀ x, f (g x) = f x}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro a b ha hb x
    exact (ha (b x)).trans (hb x)
  inv_mem' := by
    intro a ha x
    simpa using (ha (a⁻¹ x)).symm

abbrev Board (m n : ℕ) := Fin m × Fin n
abbrev rowGroup {m n : ℕ} (Ω : Finset (Board m n)) :=
  lineGroup (fun x : Ω => x.1.1)
abbrev columnGroup {m n : ℕ} (Ω : Finset (Board m n)) :=
  lineGroup (fun x : Ω => x.1.2)

/-- Zero-based form of the manuscript's (h,h)-hook. -/
def InHook (a : YoungDiagram) (h : ℕ) : Prop :=
  ∀ c ∈ a.cells, c.1 < h ∨ c.2 < h

section Copies
variable {G V W : Type*} [Group G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

/-- An actual equivariant inclusion, not an unspecified overlap matrix. -/
def Intertwines (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
    (I : V →ₗ[ℂ] W) : Prop :=
  ∀ g v, I (ρ g v) = τ g (I v)

/-- All orthogonal multiplicity copies of one irreducible type. The completeness
condition quantifies over genuine intertwiners, i.e. it is exactly the isotypic
space condition. -/
def CompleteCopies (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
    {u : ℕ} (I : Fin u → V →ₗᵢ[ℂ] W) : Prop :=
  (∀ i, Intertwines ρ τ (I i).toLinearMap) ∧
  (∀ i j, i ≠ j → ∀ v w, inner ℂ (I i v) (I j w) = 0) ∧
  ∀ J : V →ₗ[ℂ] W, Intertwines ρ τ J →
    LinearMap.range J ≤ ⨆ i, LinearMap.range (I i).toLinearMap

end Copies

/-- The all-copy operator-overlap sum, with each squared operator norm. -/
def allCopyOverlap {V W X : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    {u v : ℕ} (I : Fin u → V →ₗᵢ[ℂ] X) (J : Fin v → W →ₗᵢ[ℂ] X) : ℝ :=
  ∑ i, ∑ j, ‖((I i).toContinuousLinearMap.adjoint).comp
    (J j).toContinuousLinearMap‖ ^ 2

/-- Exact occupied-board main. Carriers are in orthonormal coordinates; arbitrary
unitary irreducibles of the two actual line groups are quantified over (equivalently,
the tuples of line partitions in the manuscript). Labelling `e` chooses the action
of the Specht module on the occupied cells and forces |a| = |Ω|. -/
abbrev OccupiedOverlapEndpoint : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ) (Ω : Finset (Board m n))
    (a : YoungDiagram) (e : Ω ≃ Cell a) (h : ℕ),
    1 ≤ h → h ≤ m * n → InHook a h →
    ∀ (r c u v : ℕ)
      (ρ : Representation ℂ (rowGroup Ω) (EuclideanSpace ℂ (Fin r)))
      (τ : Representation ℂ (columnGroup Ω) (EuclideanSpace ℂ (Fin c))),
      Representation.IsIrreducible ρ → Representation.IsIrreducible τ →
      IsUnitary ρ → IsUnitary τ →
    ∀ (I : Fin u → EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ] hilbertSpace a)
      (J : Fin v → EuclideanSpace ℂ (Fin c) →ₗᵢ[ℂ] hilbertSpace a),
      CompleteCopies (V := EuclideanSpace ℂ (Fin r)) (W := hilbertSpace a) ρ ((relabelledUnitary a e).comp (rowGroup Ω).subtype) I →
      CompleteCopies (V := EuclideanSpace ℂ (Fin c)) (W := hilbertSpace a) τ ((relabelledUnitary a e).comp (columnGroup Ω).subtype) J →
      allCopyOverlap (V := EuclideanSpace ℂ (Fin r)) (W := EuclideanSpace ℂ (Fin c))
        (X := hilbertSpace a) I J ≤
        Real.exp (C * (((m + n + 1 : ℕ) : ℝ) * (h : ℝ)^2 *
          Real.log ((m * n : ℕ) + 2) + (m * n - Ω.card : ℕ))) *
          min 1 ((r : ℝ) * c / Module.finrank ℂ (space a))

end RowColumn

end

end OAI
