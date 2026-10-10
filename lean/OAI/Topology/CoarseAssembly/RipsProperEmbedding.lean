import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.RipsEmbedding
import OAI.Topology.CoarseAssembly.Assembly

namespace OAI

/-! # Proper simplicial maps induced by injective nonexpanding maps

This construction applies to the actual boundary inclusions. The closed
range conditions record both the allowed vertices and all forbidden pairs
in the source metric, so no finiteness of the whole source is required.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Topology

universe u

variable {X Y : Type u} [PseudoMetricSpace X] [PseudoMetricSpace Y] {r : ℝ}

theorem mapPoint_embedding (e : X ↪ Y) (he : ∀ x y, dist (e x) (e y) ≤ dist x y) :
    IsEmbedding (mapPoint (r := r) e he) := by
  refine ⟨IsInducing.of_comp (mapPoint_continuous e he)
    (show Continuous (fun p : Point Y r => fun x : X => p.weight (e x)) from
      continuous_pi (fun x => coordinate_continuous (e x))) ?_, mapPoint_injective e he⟩
  have hcomp : (fun p : Point Y r => fun x : X => p.weight (e x)) ∘ mapPoint e he =
      coordinates (X := X) (r := r) := by
    funext p x
    exact mapPoint_weight_self e he p x
  rw [hcomp]
  exact ⟨rfl⟩

theorem range_mapPoint (e : X ↪ Y) (he : ∀ x y, dist (e x) (e y) ≤ dist x y) :
    Set.range (mapPoint (r := r) e he) =
      {q : Point Y r | (∀ y, y ∉ Set.range e → q.weight y = 0) ∧
        ∀ x z, r < dist x z → q.weight (e x) = 0 ∨ q.weight (e z) = 0} := by
  classical
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨fun y hy => Finsupp.embDomain_of_notMem_range e p.weight y hy, ?_⟩
    intro x z hxz
    simp only [mapPoint_weight_self]
    by_cases hx : p.weight x = 0
    · exact Or.inl hx
    by_cases hz : p.weight z = 0
    · exact Or.inr hz
    exact False.elim ((not_le_of_gt hxz)
      (p.diameter x (Finsupp.mem_support_iff.mpr hx) z (Finsupp.mem_support_iff.mpr hz)))
  · rintro ⟨hs, hd⟩
    have hsupport : ↑q.weight.support ⊆ Set.range e := by
      intro y hy
      by_contra hn
      exact Finsupp.mem_support_iff.mp hy (hs y hn)
    let p : Point X r :=
      { weight := q.weight.comapDomain e e.injective.injOn
        nonneg x := q.nonneg (e x)
        total := by
          have hm := Finsupp.embDomain_comapDomain (f := e) hsupport
          have ht := congrArg (fun f : Y →₀ ℝ => f.sum (fun _ t => t)) hm
          simpa only [Finsupp.sum_embDomain, q.total] using ht
        diameter := by
          intro x hx z hz
          by_contra hxz
          rcases hd x z (lt_of_not_ge hxz) with hx' | hz'
          · exact Finsupp.mem_support_iff.mp hx hx'
          · exact Finsupp.mem_support_iff.mp hz hz' }
    refine ⟨p, ?_⟩
    apply Point.ext
    exact Finsupp.embDomain_comapDomain (f := e) hsupport

theorem mapPoint_properEmbedding (e : X ↪ Y)
    (he : ∀ x y, dist (e x) (e y) ≤ dist x y) :
    IsClosedEmbedding (mapPoint (r := r) e he) := by
  refine ⟨mapPoint_embedding e he, ?_⟩
  rw [range_mapPoint e he]
  have hs : IsClosed {q : Point Y r | ∀ y, y ∉ Set.range e → q.weight y = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_eq (coordinate_continuous y) continuous_const
  have hd : IsClosed {q : Point Y r | ∀ x z, r < dist x z →
      q.weight (e x) = 0 ∨ q.weight (e z) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun z => isClosed_iInter fun _ =>
      (isClosed_eq (coordinate_continuous (e x)) continuous_const).union
        (isClosed_eq (coordinate_continuous (e z)) continuous_const)
  exact hs.inter hd

end CoarseAssembly.Rips

end

end OAI
