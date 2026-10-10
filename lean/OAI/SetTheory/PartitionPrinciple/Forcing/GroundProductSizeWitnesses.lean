import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStandardInaccessible

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem groundEmbeddable_product_targets
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B C D : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (first : M.groundEmbeddable A C) (second : M.groundEmbeddable B D) :
    M.groundEmbeddable (ZFSet.prod A B) (ZFSet.prod C D) := by
  obtain ⟨f, hf, first⟩ := first
  obtain ⟨g, hg, second⟩ := second
  exact ⟨relationProduct A B C D f g,
    M.relationProduct_mem pairing unions powers separation hA hB hC hD hf hg,
    relationProduct_injection first second⟩

theorem square_subset_groundPower_twice
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) :
    ZFSet.prod A A ⊆ M.groundPower (M.groundPower A) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
  have hxM := M.transitive hA hx
  have hyM := M.transitive hA hy
  apply (M.mem_groundPower _ _).2
  refine ⟨M.orderedPair_mem pairing hxM hyM, ?_⟩
  intro t ht
  rcases ZFSet.mem_pair.1 ht with rfl | rfl
  · apply (M.mem_groundPower _ _).2
    refine ⟨?_, ?_⟩
    · simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hxM hxM
    · intro w hw
      exact (ZFSet.mem_singleton.1 hw) ▸ hx
  · apply (M.mem_groundPower _ _).2
    refine ⟨M.unorderedPair_mem pairing hxM hyM, ?_⟩
    intro w hw
    rcases ZFSet.mem_pair.1 hw with rfl | rfl
    · exact hx
    · exact hy

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
