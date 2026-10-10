import OAI.Topology.CoarseAssembly.CompactIndexPairing

namespace OAI

/-! # Homotopy invariance in the unitary argument of the index pairing -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped CStarAlgebra

variable {A : Type} [CStarAlgebra A]

theorem rawCycleIndex_unitaryHomotopy (c : OddCycle A) (u : Interval → A)
    (hu : Continuous u) (hul : ∀ t, star (u t) * u t = 1)
    (hur : ∀ t, u t * star (u t) = 1) :
    rawCycleIndex c (u start) = rawCycleIndex c (u finish) := by
  apply fredholmIndex_homotopy (fun t => rawCycleToeplitz c (u t))
  · have hrep : Continuous (fun t => c.representation (u t)) := (map_continuous c.representation).comp hu
    have hext : Continuous (fun t => unitaryExtension c (u t)) := hrep.add continuous_const
    exact ((continuous_const.mul hext).mul continuous_const).add continuous_const
  · intro t
    exact rawCycleToeplitz_fredholm c (u t) (hul t) (hur t)

theorem indexPairing_unitaryHomotopy (u : Interval → A) (hu : Continuous u)
    (hul : ∀ t, star (u t) * u t = 1) (hur : ∀ t, u t * star (u t) = 1) :
    indexPairing (u start) (hul start) (hur start) =
      indexPairing (u finish) (hul finish) (hur finish) := by
  apply hom_ext
  intro c
  simp only [indexPairing_cycleClass]
  exact rawCycleIndex_unitaryHomotopy c u hu hul hur

open scoped ZeroAtInfty

variable {X : Type} [TopologicalSpace X] [CompactSpace X]

theorem compactIndexPairing_homotopy {f g : C(X, Circle)} (F : f.Homotopy g) :
    compactIndexPairing f = compactIndexPairing g := by
  let u : Interval → C(X, ℂ) := fun t => compactUnitary (homotopySlice F t)
  have hu : Continuous u := by
    let coeCircle : C(Circle, ℂ) := ⟨fun z => (z : ℂ), continuous_subtype_val⟩
    exact (ContinuousMap.continuous_postcomp coeCircle).comp F.toContinuousMap.curry.continuous
  have hul (t : Interval) : star (u t) * u t = 1 := compactUnitary_star_mul _
  have hur (t : Interval) : u t * star (u t) = 1 := compactUnitary_mul_star _
  have hi := indexPairing_unitaryHomotopy u hu hul hur
  have he : indexPairing (compactUnitary f) (compactUnitary_star_mul f)
      (compactUnitary_mul_star f) = indexPairing (compactUnitary g)
      (compactUnitary_star_mul g) (compactUnitary_mul_star g) := by
    simpa only [u, homotopySlice_start, homotopySlice_finish] using hi
  unfold compactIndexPairing
  rw [he]

end CoarseAssembly.Analytic

end

end OAI
