import OAI.Topology.CoarseAssembly.CompactFamilyMap
import OAI.Topology.CoarseAssembly.SigmaFunctionNorms
import OAI.Topology.CoarseAssembly.CompactHomotopy

namespace OAI

/-! # Norm continuity of pullback along component-preserving family homotopies -/

noncomputable section

namespace CoarseAssembly.Analytic

open Filter
open scoped ZeroAtInfty Topology CStarAlgebra

variable {X Y : ℕ → Type} [∀ j, TopologicalSpace (X j)]
  [∀ j, TopologicalSpace (Y j)] [∀ j, CompactSpace (X j)]
  [∀ j, CompactSpace (Y j)] [∀ j, T2Space (Y j)]

def compactFamilySlice (F : ∀ j, C(Interval × X j, Y j)) (t : Interval) :
    CocompactMap (Sigma X) (Sigma Y) :=
  compactFamilyMap (fun j => (F j).curry t)

theorem compactFamilyPullback_continuous (F : ∀ j, C(Interval × X j, Y j))
    (f : C₀(Sigma Y, ℂ)) :
    Continuous (fun t => pullback (compactFamilySlice F t) f) := by
  have hlocal (j : ℕ) : Continuous (fun t : Interval =>
      (sigmaFunctionRestriction Y j f).comp ((F j).curry t)) :=
    (ContinuousMap.continuous_postcomp (sigmaFunctionRestriction Y j f)).comp
      (F j).curry.continuous
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    (sigmaFunctionRestriction_norm_tendsto Y f) (ε / 4) (by positivity)
  have hhead : ∀ᶠ t in 𝓝 t₀, ∀ j ∈ Finset.range N,
      dist ((sigmaFunctionRestriction Y j f).comp ((F j).curry t))
        ((sigmaFunctionRestriction Y j f).comp ((F j).curry t₀)) < ε / 2 := by
    apply (Finset.eventually_all _).mpr
    intro j _
    exact Metric.tendsto_nhds.mp (hlocal j).continuousAt (ε / 2) (by positivity)
  filter_upwards [hhead] with t ht
  change dist (pullback (compactFamilySlice F t) f).toBCF
    (pullback (compactFamilySlice F t₀) f).toBCF < ε
  apply lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (by positivity : 0 ≤ ε / 2)).mpr ?_)
    (by linarith : ε / 2 < ε)
  rintro ⟨j, x⟩
  change dist (sigmaFunctionRestriction Y j f ((F j).curry t x))
    (sigmaFunctionRestriction Y j f ((F j).curry t₀ x)) ≤ ε / 2
  by_cases hj : j < N
  · exact (ContinuousMap.dist_apply_le_dist x).trans
      (ht j (Finset.mem_range.mpr hj)).le
  · have hb : ‖sigmaFunctionRestriction Y j f‖ < ε / 4 := by
      simpa only [dist_zero_right, norm_norm] using hN j (by omega)
    calc
      _ ≤ ‖sigmaFunctionRestriction Y j f ((F j).curry t x)‖ +
          ‖sigmaFunctionRestriction Y j f ((F j).curry t₀ x)‖ := dist_le_norm_add_norm _ _
      _ ≤ ‖sigmaFunctionRestriction Y j f‖ + ‖sigmaFunctionRestriction Y j f‖ :=
        add_le_add (ContinuousMap.norm_coe_le_norm _ _) (ContinuousMap.norm_coe_le_norm _ _)
      _ ≤ ε / 2 := by linarith

def compactFamilyCycleHomotopy (F : ∀ j, C(Interval × X j, Y j))
    (c : OddCycle C₀(Sigma X, ℂ)) : OddHomotopy C₀(Sigma Y, ℂ) where
  space := c.space
  representation t := c.representation.comp (pullback (compactFamilySlice F t))
  operator _ := c.operator
  continuous_representation f :=
    (show Continuous (c.representation : C₀(Sigma X, ℂ) → End c.space) from
      map_continuous _).comp (compactFamilyPullback_continuous F f)
  continuous_operator := continuous_const
  commutator_compact t f := c.commutator_compact (pullback (compactFamilySlice F t) f)
  square_compact t f := c.square_compact (pullback (compactFamilySlice F t) f)
  adjoint_compact t f := c.adjoint_compact (pullback (compactFamilySlice F t) f)

/-- Componentwise compact homotopies give a proper family homotopy on analytic classes. -/
theorem compactFamily_homotopy_invariance (f g : ∀ j, C(X j, Y j))
    (H : ∀ j, (f j).Homotopy (g j)) :
    pushforward (compactFamilyMap f) = pushforward (compactFamilyMap g) := by
  have hstart : compactFamilySlice (fun j => (H j).toContinuousMap) start =
      compactFamilyMap f := by
    apply CocompactMap.ext
    rintro ⟨j, x⟩
    apply congrArg (Sigma.mk j)
    exact (H j).map_zero_left x
  have hfinish : compactFamilySlice (fun j => (H j).toContinuousMap) finish =
      compactFamilyMap g := by
    apply CocompactMap.ext
    rintro ⟨j, x⟩
    apply congrArg (Sigma.mk j)
    exact (H j).map_one_left x
  apply hom_ext
  intro c
  change precomp _ (cycleClass C₀(Sigma X, ℂ) c) =
    precomp _ (cycleClass C₀(Sigma X, ℂ) c)
  rw [precomp_cycleClass, precomp_cycleClass]
  have hh := homotopy_eq (compactFamilyCycleHomotopy (fun j => (H j).toContinuousMap) c)
  change cycleClass C₀(Sigma Y, ℂ) (c.precomp (pullback
    (compactFamilySlice (fun j => (H j).toContinuousMap) start))) =
      cycleClass C₀(Sigma Y, ℂ) (c.precomp (pullback
        (compactFamilySlice (fun j => (H j).toContinuousMap) finish))) at hh
  rwa [hstart, hfinish] at hh

end CoarseAssembly.Analytic

end

end OAI
