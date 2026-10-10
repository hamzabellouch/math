import OAI.Topology.CoarseAssembly.RipsFamilyRestriction
import OAI.Topology.CoarseAssembly.RoeInclusion

namespace OAI

/-! # Component-preserving inclusions of the separated graph unions -/

noncomputable section

namespace CoarseAssembly

variable {Q P : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)]

def componentEmbedding (e : ∀ i, Q i ↪ P i) : Sigma Q ↪ Sigma P where
  toFun x := ⟨x.1, e x.1 x.2⟩
  inj' := by
    rintro ⟨i, x⟩ ⟨j, y⟩ h
    have hij : i = j := congrArg Sigma.fst h
    subst j
    have hxy : e i x = e i y := by
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
    exact congrArg (Sigma.mk i) ((e i).injective hxy)

theorem componentEmbedding_nonexpanding (o : ∀ i, Q i) (p : ∀ i, P i)
    (e : ∀ i, Q i ↪ P i) (he : ∀ i x y, dist (e i x) (e i y) ≤ dist x y)
    (hroot : ∀ i, e i (o i) = p i) :
    letI := separatedMetric o
    letI := separatedMetric p
    ∀ x y, dist (componentEmbedding e x) (componentEmbedding e y) ≤ dist x y := by
  let := separatedMetric o
  let := separatedMetric p
  rintro ⟨i, x⟩ ⟨j, y⟩
  change separatedDist p ⟨i, e i x⟩ ⟨j, e j y⟩ ≤ separatedDist o ⟨i, x⟩ ⟨j, y⟩
  by_cases hij : i = j
  · subst j
    simpa only [separatedDist_same] using he i x y
  · rw [separatedDist_different p hij, separatedDist_different o hij]
    have hx := he i x (o i)
    have hy := he j (o j) y
    rw [hroot i] at hx
    rw [hroot j] at hy
    linarith

end CoarseAssembly

end

end OAI
