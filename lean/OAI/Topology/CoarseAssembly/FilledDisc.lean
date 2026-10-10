import OAI.Topology.CoarseAssembly.LatticeHat
import OAI.Topology.CoarseAssembly.ConcreteSpaces
import OAI.Topology.CoarseAssembly.RipsPaths
import OAI.Topology.CoarseAssembly.HomotopyFilling

namespace OAI

/-! # The actual filled hexagonal discs

The compact polygon is contracted by radial scaling. The triangular-lattice
hat functions give a continuous map of this polygon into the scale-one Rips
realization of its lattice vertices. Thus the filling is constructed, not
assumed as an analytic vanishing premise.
-/

noncomputable section

namespace CoarseAssembly

open Topology Rips Analytic

theorem realLatticeRadius_nonneg (p : ℝ × ℝ) : 0 ≤ realLatticeRadius p :=
  (abs_nonneg _).trans (le_max_right _ _)

theorem realLatticeRadius_smul (c : ℝ) (hc : 0 ≤ c) (p : ℝ × ℝ) :
    realLatticeRadius (c • p) = c * realLatticeRadius p := by
  simp only [realLatticeRadius, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    ← mul_add, abs_mul, abs_of_nonneg hc, mul_max_of_nonneg _ _ hc]

def FilledDisc (j : ℕ) := {p : ℝ × ℝ // realLatticeRadius p ≤ j}

instance (j : ℕ) : TopologicalSpace (FilledDisc j) := inferInstanceAs
  (TopologicalSpace {p : ℝ × ℝ // realLatticeRadius p ≤ j})

instance (j : ℕ) : T2Space (FilledDisc j) := inferInstanceAs
  (T2Space {p : ℝ × ℝ // realLatticeRadius p ≤ j})

instance (j : ℕ) : CompactSpace (FilledDisc j) := by
  apply isCompact_iff_compactSpace.mp
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc (a := (-(j : ℝ), -(j : ℝ))) (b := ((j : ℝ), (j : ℝ))))
    (isClosed_le realLatticeRadius_continuous continuous_const)
  intro p hp
  have h := realLatticeRadius_le_iff.mp hp
  rw [abs_le] at h
  exact ⟨⟨h.1.1, (abs_le.mp h.2.1).1⟩, ⟨h.1.2, (abs_le.mp h.2.1).2⟩⟩

def filledDiscCenter (j : ℕ) : FilledDisc j :=
  ⟨(0, 0), by simp [realLatticeRadius]⟩

def filledDiscContraction (j : ℕ) : CompactContraction (FilledDisc j) where
  center := filledDiscCenter j
  homotopy :=
    { toFun := fun z => ⟨(1 - (z.1 : ℝ)) • z.2.val, by
        rw [realLatticeRadius_smul _ (sub_nonneg.mpr z.1.2.2)]
        exact (mul_le_of_le_one_left (realLatticeRadius_nonneg z.2.val)
          (by linarith [z.1.2.1] : 1 - (z.1 : ℝ) ≤ 1)).trans z.2.property⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        fun_prop
      map_zero_left := by intro x; apply Subtype.ext; simp
      map_one_left := by
        intro x
        apply Subtype.ext
        change (1 - (1 : ℝ)) • x.val = (0, 0)
        simp
        rfl }

def discHatWeights (j : ℕ) (p : FilledDisc j) : Disc j →₀ ℝ :=
  (latticeHatWeights p.val).comapDomain Subtype.val Subtype.val_injective.injOn

@[simp] theorem discHatWeights_apply (j : ℕ) (p : FilledDisc j) (v : Disc j) :
    discHatWeights j p v = latticeHat p.val v.val := rfl

theorem latticeHatWeights_disc_support (j : ℕ) (p : FilledDisc j) :
    ↑(latticeHatWeights p.val).support ⊆ Set.range (@Subtype.val LatticeVertex
      (fun v => latticeRadius v ≤ (j : ℤ))) := by
  intro v hv
  have hpos : 0 < latticeHat p.val v := lt_of_le_of_ne (latticeHat_nonneg _ _)
    (Finsupp.mem_support_iff.mp hv).symm
  exact ⟨⟨v, latticeHat_in_disc p.property hpos⟩, rfl⟩

theorem discHatWeights_total (j : ℕ) (p : FilledDisc j) :
    (discHatWeights j p).sum (fun _ t => t) = 1 := by
  have hm := Finsupp.embDomain_comapDomain
    (f := (⟨Subtype.val, Subtype.val_injective⟩ : Disc j ↪ LatticeVertex))
    (latticeHatWeights_disc_support j p)
  have hs := congrArg (fun f : LatticeVertex →₀ ℝ => f.sum (fun _ t => t)) hm
  simp only [Finsupp.sum_embDomain, latticeHatWeights_total] at hs
  convert hs using 1
  apply congrArg (fun f : Disc j →₀ ℝ => f.sum (fun _ t => t))
  apply Finsupp.ext
  intro v
  rfl

def filledToRipsPoint (j : ℕ) (p : FilledDisc j) : Point (Disc j) 1 where
  weight := discHatWeights j p
  nonneg v := latticeHat_nonneg p.val v.val
  total := discHatWeights_total j p
  diameter v hv w hw := by
    have hv' : 0 < latticeHat p.val v.val := lt_of_le_of_ne (latticeHat_nonneg _ _)
      (Finsupp.mem_support_iff.mp hv).symm
    have hw' : 0 < latticeHat p.val w.val := lt_of_le_of_ne (latticeHat_nonneg _ _)
      (Finsupp.mem_support_iff.mp hw).symm
    rcases latticeHat_adjacent hv' hw' with heq | hadj
    · have hvw : v = w := Subtype.ext heq
      simp [hvw]
    · rw [discGraphMetric_eq]
      change ((discGraph j).dist v w : ℝ) ≤ 1
      exact_mod_cast (discGraph j).dist_le (SimpleGraph.Adj.toWalk hadj)

def filledToRips (j : ℕ) : C(FilledDisc j, Point (Disc j) 1) where
  toFun := filledToRipsPoint j
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro v
    change Continuous (fun p : FilledDisc j => latticeHat p.val v.val)
    exact (latticeHat_continuous v.val).comp continuous_subtype_val

end CoarseAssembly

end

end OAI
