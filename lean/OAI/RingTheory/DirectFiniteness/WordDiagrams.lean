import OAI.RingTheory.DirectFiniteness.DiagramInsertion

namespace OAI

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
variable {V F A B : Type} [AddCommGroup A] [AddCommGroup B]
variable {Inc : V → F → Prop} {ι : V → F → (A →+ B)} {f₀ : F}

theorem OpenDiagram.deleteWordBlock (pre r post : List (F × A))
    (v : V) (hinc : ∀ t ∈ r, Inc v t.1)
    (hsum : (r.map (fun t => ι v t.1 t.2)).sum = 0)
    (D : OpenDiagram Inc ι f₀ (pre ++ r ++ post)) :
    Nonempty (OpenDiagram Inc ι f₀ (pre ++ post)) := by
  classical
  obtain ⟨p, q, hpq, hp, hq⟩ := List.map_eq_append_iff.mp
    (D.word.trans (List.append_assoc pre r post))
  obtain ⟨s, t, hst, hs, ht⟩ := List.map_eq_append_iff.mp hq
  have hboundary : D.boundary = p ++ s ++ t := by
    exact hpq.trans ((congrArg (p ++ ·) hst).trans (List.append_assoc p s t).symm)
  have hnd : s.Nodup := by
    have hh := D.nodup.tail
    rw [hboundary] at hh
    exact (List.nodup_append.mp (List.nodup_append.mp hh).1).2.1
  have hinc' : ∀ x ∈ s, Inc v (D.balanced.whiteLabel x) := by
    intro x hx
    apply hinc (D.balanced.whiteLabel x, D.balanced.weight x)
    simpa only [hs] using (List.mem_map_of_mem (f := fun x =>
      (D.balanced.whiteLabel x, D.balanced.weight x)) hx)
  have hsum' : (∑ x ∈ s.toFinset,
      ι v (D.balanced.whiteLabel x) (D.balanced.weight x)) = 0 := by
    rw [List.sum_toFinset _ hnd]
    have hh := hsum
    rw [← hs, List.map_map] at hh
    exact hh
  obtain ⟨E⟩ := D.deleteBlock p s t hboundary v hinc' hsum'
  have he : (p ++ t).map (fun x => (D.balanced.whiteLabel x, D.balanced.weight x)) =
      pre ++ post := by rw [List.map_append, hp, ht]
  exact ⟨he ▸ E⟩

theorem OpenDiagram.insertWordBlock (pre r post : List (F × A))
    (v : V) (hinc : ∀ t ∈ r, Inc v t.1)
    (hsum : (r.map (fun t => ι v t.1 t.2)).sum = 0)
    (D : OpenDiagram Inc ι f₀ (pre ++ post)) :
    Nonempty (OpenDiagram Inc ι f₀ (pre ++ r ++ post)) := by
  obtain ⟨p, q, hpq, hp, hq⟩ := List.map_eq_append_iff.mp D.word
  obtain ⟨E⟩ := D.insertBlock p q hpq r v hinc hsum
  rw [hp, hq] at E
  exact ⟨E⟩

end KaplanskyCounterexample.Planar

end

end OAI
