import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.SeparatedRips
import OAI.Topology.CoarseAssembly.RipsCompactSupport

namespace OAI

/-! # Proper maps from componentwise compact families into Rips realizations

The boundary family will be a countable family of parametrized circles.
Compact subsets of the target use finitely many vertices, hence meet only
finitely many members of this family. This proves properness directly.
-/

noncomputable section

namespace CoarseAssembly

open Topology Rips

variable {V : ℕ → Type} [∀ j, MetricSpace (V j)]
  {Z : ℕ → Type} [∀ j, TopologicalSpace (Z j)] [∀ j, CompactSpace (Z j)]

theorem separatedRipsMap_continuous (o : ∀ j, V j) (r : ℝ) (j : ℕ) :
    letI := separatedMetric o
    Continuous (separatedRipsMap o r j) := by
  let := separatedMetric o
  exact mapPoint_continuous (separatedComponent j)
    (fun x y => ((separatedComponent_isometry o j).dist_eq x y).le)

@[simp] theorem separatedRipsMap_weight (o : ∀ j, V j) (r : ℝ) (j : ℕ)
    (p : Point (V j) r) (x : V j) :
    letI := separatedMetric o
    (separatedRipsMap o r j p).weight ⟨j, x⟩ = p.weight x := by
  let := separatedMetric o
  exact mapPoint_weight_self (separatedComponent j)
    (fun x y => ((separatedComponent_isometry o j).dist_eq x y).le) p x

def ripsFamilyContinuousMap (o : ∀ j, V j) (r : ℝ)
    (γ : ∀ j, C(Z j, Point (V j) r)) :
    letI := separatedMetric o
    C(Sigma Z, Point (Sigma V) r) := by
  let := separatedMetric o
  refine ⟨fun z => separatedRipsMap o r z.1 (γ z.1 z.2), ?_⟩
  exact continuous_sigma (fun j => (separatedRipsMap_continuous o r j).comp (γ j).continuous)

variable [∀ j, Fintype (V j)]

theorem ripsFamily_preimage_compact (o : ∀ j, V j) (r : ℝ)
    (γ : ∀ j, C(Z j, Point (V j) r)) :
    letI := separatedMetric o
    ∀ K, IsCompact K → IsCompact ((ripsFamilyContinuousMap o r γ) ⁻¹' K) := by
  classical
  let := separatedMetric o
  intro K hK
  obtain ⟨s, hs⟩ := compact_support_finite (fun x => separated_closedBall_finite o x r) hK
  let a : Finset ℕ := s.image Sigma.fst
  have hcover : (ripsFamilyContinuousMap o r γ) ⁻¹' K ⊆
      ⋃ j ∈ a, Set.range (@Sigma.mk ℕ Z j) := by
    rintro ⟨j, z⟩ hz
    obtain ⟨x, hx⟩ := (γ j z).exists_positive
    have hmem : (⟨j, x⟩ : Sigma V) ∈ s := hs _ hz
      (Finsupp.mem_support_iff.mpr (by
        change (separatedRipsMap o r j (γ j z)).weight ⟨j, x⟩ ≠ 0
        rw [separatedRipsMap_weight]
        exact ne_of_gt hx))
    have hj : j ∈ a := Finset.mem_image.mpr ⟨⟨j, x⟩, hmem, rfl⟩
    exact Set.mem_iUnion₂.mpr ⟨j, hj, ⟨z, rfl⟩⟩
  have hcompact : IsCompact (⋃ j ∈ a, Set.range (@Sigma.mk ℕ Z j)) :=
    a.isCompact_biUnion (fun j _ => isCompact_range continuous_sigmaMk)
  exact hcompact.of_isClosed_subset
    (hK.isClosed.preimage (ripsFamilyContinuousMap o r γ).continuous) hcover

def ripsFamilyMap (o : ∀ j, V j) (r : ℝ)
    (γ : ∀ j, C(Z j, Point (V j) r)) :
    letI := separatedMetric o
    CocompactMap (Sigma Z) (Point (Sigma V) r) := by
  let := separatedMetric o
  exact
    { toContinuousMap := ripsFamilyContinuousMap o r γ
      cocompact_tendsto' := CocompactMap.tendsto_of_forall_preimage
        (ripsFamily_preimage_compact o r γ) }

theorem ripsFamilyMap_coarsen (o : ∀ j, V j) {r s : ℝ} (hrs : r ≤ s)
    (γ : ∀ j, C(Z j, Point (V j) r)) (δ : ∀ j, C(Z j, Point (V j) s))
    (hγ : ∀ j z, coarsen hrs (γ j z) = δ j z) :
    letI := separatedMetric o
    (inclusion hrs).comp (ripsFamilyMap o r γ) = ripsFamilyMap o s δ := by
  let := separatedMetric o
  apply CocompactMap.ext
  rintro ⟨j, z⟩
  change coarsen hrs (separatedRipsMap o r j (γ j z)) = separatedRipsMap o s j (δ j z)
  dsimp only [separatedRipsMap]
  rw [coarsen_mapPoint, hγ]

end CoarseAssembly

end

end OAI
