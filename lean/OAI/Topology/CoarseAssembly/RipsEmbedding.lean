import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.FiniteRips

namespace OAI

/-! # Simplicial embeddings and isolated Rips components

An injective nonexpanding vertex map induces the actual barycentric map.
For an isometric component separated from its complement at the Rips scale,
its realization is a clopen subspace. Finite components are compact, so the
inclusion is proper.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Topology

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  {r : ℝ}

@[simp] theorem mapPoint_weight_self (e : X ↪ Y) (he) (p : Point X r) (x : X) :
    (mapPoint e he p).weight (e x) = p.weight x :=
  Finsupp.embDomain_apply_self e p.weight x

theorem mapPoint_continuous (e : X ↪ Y) (he) : Continuous (mapPoint (r := r) e he) := by
  classical
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro y
  change Continuous (fun p : Point X r => coordinates (mapPoint e he p) y)
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    simpa only [coordinates, mapPoint, Finsupp.embDomain_apply_self] using
      coordinate_continuous (r := r) x
  · have hz : (fun p : Point X r => coordinates (mapPoint e he p) y) = fun _ => 0 := by
      funext p
      exact Finsupp.embDomain_of_notMem_range e p.weight y hy
    rw [hz]
    exact continuous_const

theorem mapPoint_injective (e : X ↪ Y) (he) : Function.Injective (mapPoint (r := r) e he) := by
  intro p q h
  apply Point.ext
  apply Finsupp.ext
  intro x
  have hx := congrArg (fun p : Point Y r => p.weight (e x)) h
  simpa only [mapPoint_weight_self] using hx

theorem coarsen_mapPoint {s : ℝ} (hrs : r ≤ s) (e : X ↪ Y) (he)
    (p : Point X r) : coarsen hrs (mapPoint e he p) = mapPoint e he (coarsen hrs p) := by
  apply Point.ext
  rfl

theorem mapPoint_range (e : X ↪ Y) (he : Isometry e) :
    Set.range (mapPoint (r := r) e (fun x y => (he.dist_eq x y).le)) =
      {q : Point Y r | ↑q.weight.support ⊆ Set.range e} := by
  classical
  ext q
  constructor
  · rintro ⟨p, rfl⟩ y hy
    rw [mapPoint, Finsupp.support_embDomain, Finset.mem_coe, Finset.mem_map] at hy
    obtain ⟨x, _, rfl⟩ := hy
    exact ⟨x, rfl⟩
  · intro hq
    refine ⟨unmapPoint e he q hq, ?_⟩
    apply Point.ext
    exact Finsupp.embDomain_comapDomain hq

theorem mapPoint_range_open (e : X ↪ Y) (he : Isometry e)
    (hsep : ∀ x y, y ∉ Set.range e → r < dist (e x) y) :
    IsOpen (Set.range (mapPoint (r := r) e (fun x y => (he.dist_eq x y).le))) := by
  rw [mapPoint_range e he]
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  obtain ⟨y, hy⟩ := q.exists_positive
  obtain ⟨x, rfl⟩ := hq (Finsupp.mem_support_iff.mpr (ne_of_gt hy))
  have hnhds : {p : Point Y r | 0 < p.weight (e x)} ∈ 𝓝 q :=
    (isOpen_lt continuous_const (coordinate_continuous (e x))).mem_nhds hy
  apply Filter.mem_of_superset hnhds
  intro p hp y hy
  by_contra hnot
  exact (not_le_of_gt (hsep x y hnot))
    (p.diameter (e x) (Finsupp.mem_support_iff.mpr (ne_of_gt hp)) y hy)

theorem mapPoint_closedEmbedding [Fintype X] (e : X ↪ Y) (he) :
    IsClosedEmbedding (mapPoint (r := r) e he) :=
  (mapPoint_continuous e he).isClosedEmbedding (mapPoint_injective e he)

def componentInclusion [Fintype X] (e : X ↪ Y)
    (he : ∀ x y, dist (e x) (e y) ≤ dist x y) :
    CocompactMap (Point X r) (Point Y r) where
  toFun := mapPoint e he
  continuous_toFun := mapPoint_continuous e he
  cocompact_tendsto' := (mapPoint_closedEmbedding e he).tendsto_cocompact

end CoarseAssembly.Rips

end

end OAI
