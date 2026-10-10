import OAI.Topology.CoarseAssembly.RepresentedNormalization
import OAI.Topology.CoarseAssembly.CycleIndex

namespace OAI

/-! # The Toeplitz index for nonunital representations

A represented unitary is extended by the identity on the complement of the
represented subspace. This supplies a genuine unitary even when the original
representation does not preserve the unit.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

def unitaryExtension (c : OddCycle A) (u : A) : End c.space :=
  c.representation u + (1 - c.representation 1)

theorem unitaryExtension_star (c : OddCycle A) (u : A) :
    star (unitaryExtension c u) = unitaryExtension c (star u) := by
  rw [unitaryExtension, star_add, star_sub, star_one, ← map_star, ← map_star, star_one]
  rfl

theorem unitaryExtension_mul (c : OddCycle A) (u v : A) :
    unitaryExtension c u * unitaryExtension c v = unitaryExtension c (u * v) := by
  simp only [unitaryExtension, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
    ← map_mul, one_mul, mul_one]
  abel

theorem unitaryExtension_unitary (c : OddCycle A) (u : A)
    (hul : star u * u = 1) (hur : u * star u = 1) :
    star (unitaryExtension c u) * unitaryExtension c u = 1 ∧
      unitaryExtension c u * star (unitaryExtension c u) = 1 := by
  rw [unitaryExtension_star, unitaryExtension_mul, unitaryExtension_mul, hul, hur]
  constructor <;> simp only [unitaryExtension, add_sub_cancel]

theorem unitaryExtension_commutator (c : OddCycle A) (u : A)
    (hcomm : Commute c.operator (c.representation 1)) :
    c.operator * unitaryExtension c u - unitaryExtension c u * c.operator =
      c.operator * c.representation u - c.representation u * c.operator := by
  simp only [unitaryExtension, mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul]
  rw [hcomm.eq]
  abel

def representedToeplitz (c : OddCycle A) (u : A) : End c.space :=
  toeplitzCompression (positiveProjection c.operator) (unitaryExtension c u)

def representedIndex (c : OddCycle A) (u : A) : ℤ :=
  (representedToeplitz c u).toLinearMap.index

theorem representedToeplitz_fredholm (c : OddCycle A) (u : A)
    (hself : IsSelfAdjoint c.operator) (hsq : c.operator * c.operator = 1)
    (hcomm : Commute c.operator (c.representation 1))
    (hul : star u * u = 1) (hur : u * star u = 1) :
    (representedToeplitz c u).IsFredholm := by
  obtain ⟨hUl, hUr⟩ := unitaryExtension_unitary c u hul hur
  apply toeplitzCompression_fredholm _ _ (positiveProjection_selfAdjoint _ hself)
    (positiveProjection_sq _ hsq) hUl hUr
  rw [positiveProjection_commutator, unitaryExtension_commutator c u hcomm]
  exact (c.commutator_compact u).smul (1 / 2 : ℝ)

theorem exists_representedToeplitz_fredholm (c : OddCycle A) (u : A)
    (hul : star u * u = 1) (hur : u * star u = 1) :
    ∃ d : OddCycle A, cycleClass A d = cycleClass A c ∧
      (representedToeplitz d u).IsFredholm := by
  obtain ⟨d, hdc, hdself, hdsq, hdcomm⟩ := exists_represented_involutive_representative c
  exact ⟨d, hdc, representedToeplitz_fredholm d u hdself hdsq hdcomm hul hur⟩

theorem representedIndex_homotopy (h : OddHomotopy A) (u : A)
    (hself : ∀ t, IsSelfAdjoint (h.operator t))
    (hsq : ∀ t, h.operator t * h.operator t = 1)
    (hcomm : ∀ t, Commute (h.operator t) (h.representation t 1))
    (hul : star u * u = 1) (hur : u * star u = 1) :
    representedIndex (h.eval start) u = representedIndex (h.eval finish) u := by
  apply fredholmIndex_homotopy (fun t => representedToeplitz (h.eval t) u)
  · change Continuous (fun t => positiveProjection (h.operator t) *
      (h.representation t u + (1 - h.representation t 1)) * positiveProjection (h.operator t) +
      (1 - positiveProjection (h.operator t)))
    have hp : Continuous (fun t => positiveProjection (h.operator t)) :=
      (h.continuous_operator.add continuous_const).const_smul (1 / 2 : ℝ)
    exact ((hp.mul ((h.continuous_representation u).add
      (continuous_const.sub (h.continuous_representation 1)))).mul hp).add
      (continuous_const.sub hp)
  · intro t
    exact representedToeplitz_fredholm (h.eval t) u (hself t) (hsq t) (hcomm t) hul hur

theorem representedIndex_degenerate (c : OddCycle A) (u : A) (hd : c.Degenerate)
    (hself : IsSelfAdjoint c.operator) (hsq : c.operator * c.operator = 1)
    (hul : star u * u = 1) (hur : u * star u = 1) : representedIndex c u = 0 := by
  have hcomm : Commute c.operator (c.representation 1) := sub_eq_zero.mp (hd.1 1)
  have hc : Commute (positiveProjection c.operator) (unitaryExtension c u) := by
    apply sub_eq_zero.mp
    rw [positiveProjection_commutator, unitaryExtension_commutator c u hcomm, hd.1 u, smul_zero]
  obtain ⟨hUl, hUr⟩ := unitaryExtension_unitary c u hul hur
  obtain ⟨hl, hr⟩ := toeplitzCompression_unitary _ _ (positiveProjection_selfAdjoint _ hself)
    (positiveProjection_sq _ hsq) hUl hUr hc
  have hinv : (representedToeplitz c u).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse (g := star (representedToeplitz c u)) hr hl
  exact LinearMap.index_of_bijective hinv.bijective

end CoarseAssembly.Analytic

end

end OAI
