import OAI.Topology.CoarseAssembly.ComponentInclusion
import OAI.Topology.CoarseAssembly.RipsMapCalculus

namespace OAI

/-! # Exact component preimages for the geometric inclusions -/

noncomputable section

namespace CoarseAssembly.Rips

variable {Q P : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)]

theorem componentRips_preimage (o : ∀ i, Q i) (p : ∀ i, P i)
    (e : ∀ i, Q i ↪ P i) (r : ℝ)
    (he : letI := separatedMetric o; letI := separatedMetric p
      ∀ x y, dist (componentEmbedding e x) (componentEmbedding e y) ≤ dist x y)
    (i : ℕ) :
    letI := separatedMetric o
    letI := separatedMetric p
    ∀ x : Point (Sigma Q) r,
      mapPoint (componentEmbedding e) he x ∈ Set.range (separatedRipsEmbedding p r i) ↔
        x ∈ Set.range (separatedRipsEmbedding o r i) := by
  let := separatedMetric o
  let := separatedMetric p
  intro x
  change mapPoint (componentEmbedding e) he x ∈ Set.range (mapPoint (separatedComponent i)
      (fun a b => ((separatedComponent_isometry p i).dist_eq a b).le)) ↔
    x ∈ Set.range (mapPoint (separatedComponent i)
      (fun a b => ((separatedComponent_isometry o i).dist_eq a b).le))
  rw [mapPoint_range (separatedComponent i) (separatedComponent_isometry p i),
    mapPoint_range (separatedComponent i) (separatedComponent_isometry o i)]
  constructor
  · intro hx y hy
    have hmem : componentEmbedding e y ∈ (mapPoint (componentEmbedding e) he x).weight.support := by
      apply Finsupp.mem_support_iff.mpr
      rw [mapPoint_weight_self]
      exact Finsupp.mem_support_iff.mp hy
    obtain ⟨z, hz⟩ := hx hmem
    have hi : i = y.1 := congrArg Sigma.fst hz
    rcases y with ⟨j, y⟩
    dsimp only at hi
    subst j
    exact ⟨y, rfl⟩
  · intro hx y hy
    change y ∈ (x.weight.embDomain (componentEmbedding e)).support at hy
    rw [Finsupp.support_embDomain, Finset.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨a, ha⟩ := hx hz
    rw [← ha]
    exact ⟨e i a, rfl⟩

end CoarseAssembly.Rips

end

end OAI
