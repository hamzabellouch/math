import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.RipsFamilyMap
import OAI.Topology.CoarseAssembly.CountableAdditivity
import OAI.Topology.CoarseAssembly.ClopenNaturality

namespace OAI

/-! # Exact coordinates of the pushed-forward family

Restriction to a late Rips component recovers precisely the corresponding
member of the source family, irrespective of links among other components.
-/

noncomputable section

namespace CoarseAssembly

open Topology Rips Analytic

variable {V : ℕ → Type} [∀ j, MetricSpace (V j)] [∀ j, Fintype (V j)]
  {Z : ℕ → Type} [∀ j, TopologicalSpace (Z j)] [∀ j, CompactSpace (Z j)]

theorem separatedRipsEmbedding_open (o : ∀ j, V j) (r : ℝ) (j : ℕ) (hj : r < j) :
    letI := separatedMetric o
    IsOpenEmbedding (separatedRipsEmbedding o r j) := lateRipsComponent_openEmbedding o j r hj

theorem ripsFamily_component_preimage (o : ∀ j, V j) (r : ℝ)
    (γ : ∀ j, C(Z j, Point (V j) r)) (j : ℕ) :
    letI := separatedMetric o
    ∀ z, ripsFamilyMap o r γ z ∈ Set.range (separatedRipsEmbedding o r j) ↔
      z ∈ Set.range (sigmaComponent Z j) := by
  let := separatedMetric o
  rintro ⟨k, z⟩
  constructor
  · intro h
    have hs : ↑(ripsFamilyMap o r γ ⟨k, z⟩).weight.support ⊆
        Set.range (separatedComponent (V := V) j) := by
      exact (Set.ext_iff.mp (mapPoint_range (separatedComponent j)
        (separatedComponent_isometry o j)) _).mp h
    obtain ⟨x, hx⟩ := (γ k z).exists_positive
    have hmem : (⟨k, x⟩ : Sigma V) ∈ (ripsFamilyMap o r γ ⟨k, z⟩).weight.support := by
      apply Finsupp.mem_support_iff.mpr
      change (separatedRipsMap o r k (γ k z)).weight ⟨k, x⟩ ≠ 0
      rw [separatedRipsMap_weight]
      exact ne_of_gt hx
    obtain ⟨y, hy⟩ := hs hmem
    have hjk : j = k := congrArg Sigma.fst hy
    subst k
    exact ⟨z, rfl⟩
  · rintro ⟨z', hz'⟩
    change Sigma.mk j z' = Sigma.mk k z at hz'
    cases hz'
    exact ⟨γ j z', rfl⟩

theorem ripsFamily_restriction [∀ j, T2Space (Z j)] (o : ∀ j, V j) (r : ℝ)
    (γ : ∀ j, C(Z j, Point (V j) r)) (j : ℕ) (hj : r < j)
    (hadd : CountableAdditivityInput Z) (a : ∀ k, LocallyFiniteK1 (Z k)) :
    letI := separatedMetric o
    restrictComponent (separatedRipsEmbedding o r j) (separatedRipsEmbedding_open o r j hj)
      (pushforward (ripsFamilyMap o r γ) (familyClass Z hadd a)) =
        pushforward (compactMap (γ j)) (a j) := by
  let := separatedMetric o
  have h := restrictComponent_natural (sigmaComponent Z j) (sigmaComponent_open Z j)
    (separatedRipsEmbedding o r j) (separatedRipsEmbedding_open o r j hj)
    (ripsFamilyMap o r γ) (compactMap (γ j)) (fun _ => rfl)
    (ripsFamily_component_preimage o r γ j)
  have heq := DFunLike.congr_fun h (familyClass Z hadd a)
  simpa only [AddMonoidHom.comp_apply, familyClass_coordinate] using heq

end CoarseAssembly

end

end OAI
