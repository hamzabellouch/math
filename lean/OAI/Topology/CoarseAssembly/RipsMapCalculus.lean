import OAI.Topology.CoarseAssembly.RipsProperEmbedding
import OAI.Topology.CoarseAssembly.CocyclePathLifting
import OAI.Topology.CoarseAssembly.LoopCircle

namespace OAI

/-! # Exact naturality of the parametrized Rips paths

Injective nonexpanding vertex maps commute with barycentric interpolation,
edge paths and concatenated graph walks, including their parametrizations.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Topology

variable {X Y Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
  {r : ℝ}

theorem mapPoint_weight (e : X ↪ Y) (he) (p : Point X r) :
    (mapPoint e he p).weight = p.weight.embDomain e := rfl

theorem mapPoint_comp (e : X ↪ Y) (f : Y ↪ Z) (he) (hf) (p : Point X r) :
    mapPoint f hf (mapPoint e he p) =
      mapPoint (e.trans f) (fun x y => (hf (e x) (e y)).trans (he x y)) p := by
  apply Point.ext
  exact (Finsupp.embDomain_trans_apply p.weight e f).symm

theorem mapPoint_vertex (e : X ↪ Y) (he) (x : X) (hr : 0 ≤ r) :
    mapPoint e he (vertex x hr) = vertex (e x) hr := by
  apply Point.ext
  exact Finsupp.embDomain_single e x 1

theorem mapPoint_interpolate (e : X ↪ Y) (he) (p q : Point X r) (hpq) (t : unitInterval) :
    mapPoint e he (interpolate p q hpq t) =
      interpolate (mapPoint e he p) (mapPoint e he q)
        (by
          intro x hx y hy
          change x ∈ (p.weight.embDomain e).support at hx
          change y ∈ (q.weight.embDomain e).support at hy
          rw [Finsupp.support_embDomain, Finset.mem_map] at hx hy
          obtain ⟨a, ha, rfl⟩ := hx
          obtain ⟨b, hb, rfl⟩ := hy
          exact (he a b).trans (hpq a ha b hb)) t := by
  classical
  apply Point.ext
  apply Finsupp.ext
  intro y
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    simp only [mapPoint, interpolate, Finsupp.embDomain_apply_self, Finsupp.coe_add,
      Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply]
  · simp only [mapPoint, interpolate, Finsupp.embDomain_of_notMem_range _ _ _ hy,
      Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_zero, add_zero]

theorem mapPoint_edgePath (e : X ↪ Y) (he) {x y : X} (hxy : dist x y ≤ r)
    (t : unitInterval) :
    mapPoint e he (edgePath hxy t) = edgePath ((he x y).trans hxy) t := by
  simp only [edgePath, simplexPath, Path.coe_mk_mk]
  rw [mapPoint_interpolate]
  apply Point.ext
  change (1 - (t : ℝ)) • (mapPoint e he (vertex x _)).weight +
    (t : ℝ) • (mapPoint e he (vertex y _)).weight = _
  rw [congrArg Point.weight (mapPoint_vertex e he x _),
    congrArg Point.weight (mapPoint_vertex e he y _)]
  rfl

theorem mapPoint_walkPath {G : SimpleGraph X} {H : SimpleGraph Y}
    (e : X ↪ Y) (he) (hgraph : ∀ x y, G.Adj x y → H.Adj (e x) (e y))
    (hr : 0 ≤ r) (hG : ∀ x y, G.Adj x y → dist x y ≤ r)
    (hH : ∀ x y, H.Adj x y → dist x y ≤ r)
    {x y : X} (p : G.Walk x y) (t : unitInterval) :
    mapPoint e he (walkPath hr hG p t) =
      walkPath hr hH (p.map ⟨e, fun h => hgraph _ _ h⟩) t := by
  induction p generalizing t with
  | nil =>
    change mapPoint e he (vertex _ hr) = vertex _ hr
    exact mapPoint_vertex e he _ hr
  | cons h p ih =>
    simp only [walkPath, SimpleGraph.Walk.map_cons, Path.trans_apply]
    split_ifs
    · exact mapPoint_edgePath e he (hG _ _ h) _
    · exact ih _

theorem mapPoint_loopCircle {G : SimpleGraph X} {H : SimpleGraph Y}
    (e : X ↪ Y) (he) (hgraph : ∀ x y, G.Adj x y → H.Adj (e x) (e y))
    (hr : 0 ≤ r) (hG : ∀ x y, G.Adj x y → dist x y ≤ r)
    (hH : ∀ x y, H.Adj x y → dist x y ≤ r)
    {x : X} (p : G.Walk x x) (z : WindingCircle) :
    mapPoint e he (loopCircle (walkPath hr hG p) z) =
      loopCircle (walkPath hr hH (p.map ⟨e, fun h => hgraph _ _ h⟩)) z := by
  obtain ⟨t, rfl⟩ := circle_parameter_surjective z
  simp only [loopCircle_apply]
  exact mapPoint_walkPath e he hgraph hr hG hH p t

end CoarseAssembly.Rips

end

end OAI
