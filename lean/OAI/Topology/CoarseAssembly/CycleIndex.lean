import OAI.Topology.CoarseAssembly.ToeplitzCompression
import Mathlib.Topology.Connected.TotallyDisconnected

namespace OAI

/-! # The scalar-unitary index of normalized odd cycles

This constructs the Fredholm operator and its integer index. Descent to the
cycle quotient and the explicit circle-generator calculation are separate
steps; neither is assumed by these declarations.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

def positiveProjection (F : End H) : End H := (1 / 2 : ℝ) • (F + 1)

theorem positiveProjection_selfAdjoint (F : End H) (hF : IsSelfAdjoint F) :
    IsSelfAdjoint (positiveProjection F) := by
  change star ((1 / 2 : ℝ) • (F + 1)) = _
  rw [star_smul, star_trivial, star_add, hF.star_eq, star_one]
  rfl

theorem positiveProjection_sq (F : End H) (hF : F * F = 1) :
    positiveProjection F * positiveProjection F = positiveProjection F := by
  have he : (F + 1) * (F + 1) = (2 : ℝ) • (F + 1) := by
    rw [add_mul, mul_add, mul_add, hF, one_mul, mul_one, one_mul]
    module
  unfold positiveProjection
  rw [smul_mul_assoc, mul_smul_comm, he]
  module

theorem positiveProjection_commutator (F U : End H) :
    positiveProjection F * U - U * positiveProjection F =
      (1 / 2 : ℝ) • (F * U - U * F) := by
  simp only [positiveProjection, smul_mul_assoc, mul_smul_comm, add_mul, mul_add,
    one_mul, mul_one]
  module

variable {A : Type} [CStarAlgebra A]

def cycleToeplitz (c : OddCycle A) (u : A) : End c.space :=
  toeplitzCompression (positiveProjection c.operator) (c.representation u)

def cycleIndex (c : OddCycle A) (u : A) : ℤ := (cycleToeplitz c u).toLinearMap.index

theorem cycleToeplitz_fredholm (c : OddCycle A) (u : A)
    (hunit : c.representation 1 = 1) (hself : IsSelfAdjoint c.operator)
    (hsq : c.operator * c.operator = 1) (hul : star u * u = 1) (hur : u * star u = 1) :
    (cycleToeplitz c u).IsFredholm := by
  apply toeplitzCompression_fredholm _ _ (positiveProjection_selfAdjoint _ hself)
    (positiveProjection_sq _ hsq)
  · rw [← map_star, ← map_mul, hul, hunit]
  · rw [← map_star, ← map_mul, hur, hunit]
  · rw [positiveProjection_commutator]
    exact (c.commutator_compact u).smul (1 / 2 : ℝ)

theorem fredholmIndex_homotopy (T : Interval → End H) (hT : Continuous T)
    (hf : ∀ t, (T t).IsFredholm) :
    (T start).toLinearMap.index = (T finish).toLinearMap.index := by
  have hc : Continuous (fun t => (T t).toLinearMap.index) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hf t).index_continuousAt.comp hT.continuousAt
  exact IsPreconnected.constant isPreconnected_univ hc.continuousOn
    (Set.mem_univ start) (Set.mem_univ finish)

theorem cycleIndex_homotopy (h : OddHomotopy A) (u : A)
    (hunit : ∀ t, h.representation t 1 = 1)
    (hself : ∀ t, IsSelfAdjoint (h.operator t))
    (hsq : ∀ t, h.operator t * h.operator t = 1)
    (hul : star u * u = 1) (hur : u * star u = 1) :
    cycleIndex (h.eval start) u = cycleIndex (h.eval finish) u := by
  apply fredholmIndex_homotopy (fun t => cycleToeplitz (h.eval t) u)
  · change Continuous (fun t => positiveProjection (h.operator t) * h.representation t u *
      positiveProjection (h.operator t) + (1 - positiveProjection (h.operator t)))
    have hp : Continuous (fun t => positiveProjection (h.operator t)) :=
      (h.continuous_operator.add continuous_const).const_smul (1 / 2 : ℝ)
    exact ((hp.mul (h.continuous_representation u)).mul hp).add (continuous_const.sub hp)
  · intro t
    exact cycleToeplitz_fredholm (h.eval t) u (hunit t) (hself t) (hsq t) hul hur

theorem cycleIndex_degenerate (c : OddCycle A) (u : A) (hd : c.Degenerate)
    (hunit : c.representation 1 = 1) (hself : IsSelfAdjoint c.operator)
    (hsq : c.operator * c.operator = 1) (hul : star u * u = 1) (hur : u * star u = 1) :
    cycleIndex c u = 0 := by
  have hUl : star (c.representation u) * c.representation u = 1 := by
    rw [← map_star, ← map_mul, hul, hunit]
  have hUr : c.representation u * star (c.representation u) = 1 := by
    rw [← map_star, ← map_mul, hur, hunit]
  have hc : Commute (positiveProjection c.operator) (c.representation u) := by
    apply sub_eq_zero.mp
    rw [positiveProjection_commutator, hd.1 u, smul_zero]
  obtain ⟨hl, hr⟩ := toeplitzCompression_unitary _ _ (positiveProjection_selfAdjoint _ hself)
    (positiveProjection_sq _ hsq) hUl hUr hc
  have hinv : (cycleToeplitz c u).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse (g := star (cycleToeplitz c u)) hr hl
  exact LinearMap.index_of_bijective hinv.bijective

end CoarseAssembly.Analytic

end

end OAI
