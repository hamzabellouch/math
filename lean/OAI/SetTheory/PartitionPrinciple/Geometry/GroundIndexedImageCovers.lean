import OAI.SetTheory.PartitionPrinciple.Definability.GroundPairCompositions
import OAI.SetTheory.PartitionPrinciple.Definability.MapFamilyApplicationGraphs

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def indexedImageCover (I U V maps : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose V (ZFSet.prod I U) I
    (relationConverse (ZFSet.prod I U) V (mapFamilyApplicationGraph I U V maps))
    (productFirst I U)

theorem pair_mem_indexedImageCover (I U V maps y i : ZFSet.{u}) :
    ZFSet.pair y i ∈ indexedImageCover I U V maps ↔
      y ∈ V ∧ i ∈ I ∧ ∃ x ∈ U, ∃ f,
        ZFSet.pair i f ∈ maps ∧ ZFSet.pair x y ∈ f := by
  rw [indexedImageCover, pair_mem_relationCompose]
  constructor
  · rintro ⟨hy, hi, z, _, converse, projection⟩
    obtain ⟨j, hj, x, hx, equal⟩ := (mem_productFirst I U _).1 projection
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    have flattened := (pair_mem_relationConverse _ _ _ _ _).1 converse
    obtain ⟨_, _, _, f, indexed, entry⟩ :=
      (pair_mem_mapFamilyApplicationGraph _ _ _ _ _ _ _).1 flattened.2.2
    exact ⟨hy, hi, x, hx, f, indexed, entry⟩
  · rintro ⟨hy, hi, x, hx, f, indexed, entry⟩
    refine ⟨hy, hi, ZFSet.pair i x, ZFSet.pair_mem_prod.2 ⟨hi, hx⟩, ?_, ?_⟩
    · exact (pair_mem_relationConverse _ _ _ _ _).2
        ⟨ZFSet.pair_mem_prod.2 ⟨hi, hx⟩, hy,
          (pair_mem_mapFamilyApplicationGraph _ _ _ _ _ _ _).2
            ⟨hi, hx, hy, f, indexed, entry⟩⟩
    · exact (mem_productFirst I U _).2 ⟨i, hi, x, hx, rfl⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem indexedImageCover_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I U V maps : ZFSet.{u}} (hI : I ∈ M.sets) (hU : U ∈ M.sets)
    (hV : V ∈ M.sets) (hMaps : maps ∈ M.sets) :
    indexedImageCover I U V maps ∈ M.sets := by
  have product := M.prod_mem pairing unions powers separation hI hU
  exact M.relationCompose_mem pairing unions powers separation hV product hI
    (M.relationConverse_mem pairing unions powers separation product hV
      (M.mapFamilyApplicationGraph_mem pairing unions powers separation hI hU hV hMaps))
    (M.productFirst_mem pairing unions powers separation hI hU)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
