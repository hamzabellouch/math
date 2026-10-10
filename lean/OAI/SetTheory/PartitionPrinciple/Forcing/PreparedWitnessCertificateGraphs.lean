import OAI.SetTheory.PartitionPrinciple.Geometry.GroundNaturalFamilyShift

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def preparedWitnessCertificateGraph (stages Q K E : ZFSet.{u}) : ZFSet.{u} :=
  let tail := ZFSet.prod K E
  let output := ZFSet.prod Q tail
  let L := ZFSet.prod stages output
  relationCompose L tail K
    (relationCompose L output tail (productSecond stages output) (productSecond Q tail))
    (productFirst K E)

theorem preparedWitnessCertificateGraph_function (stages Q K E : ZFSet.{u}) :
    ZFSet.IsFunc (ZFSet.prod stages (ZFSet.prod Q (ZFSet.prod K E))) K
      (preparedWitnessCertificateGraph stages Q K E) :=
  relationCompose_function_of_subset
    (relationCompose_function_of_subset (productSecond_function _ _) (productSecond_function _ _)
      (fun _ h => h)) (productFirst_function _ _) (fun _ h => h)

theorem pair_mem_preparedWitnessCertificateGraph (stages Q K E y k : ZFSet.{u}) :
    ZFSet.pair y k ∈ preparedWitnessCertificateGraph stages Q K E ↔
      k ∈ K ∧ ∃ alpha ∈ stages, ∃ source ∈ Q, ∃ enumerations ∈ E,
        y = ZFSet.pair alpha (ZFSet.pair source (ZFSet.pair k enumerations)) := by
  rw [preparedWitnessCertificateGraph, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, hk, tail, _, first, projected⟩
    obtain ⟨k', _, enums, he, equal⟩ := (mem_productFirst _ _ _).1 projected
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨_, _, output, _, first, second⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 first
    obtain ⟨source, hsource, tail', _, equal⟩ := (mem_productSecond _ _ _).1 second
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨alpha, ha, output', _, equal⟩ := (mem_productSecond _ _ _).1 first
    obtain ⟨value, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hk, alpha, ha, source, hsource, enums, he, value⟩
  · rintro ⟨hk, alpha, ha, source, hs, enums, he, rfl⟩
    have ht := ZFSet.pair_mem_prod.2 ⟨hk, he⟩
    have ho := ZFSet.pair_mem_prod.2 ⟨hs, ht⟩
    have hy := ZFSet.pair_mem_prod.2 ⟨ha, ho⟩
    exact ⟨hy, hk, _, ht,
      (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hy, ht, _, ho,
        (mem_productSecond _ _ _).2 ⟨alpha, ha, _, ho, rfl⟩,
        (mem_productSecond _ _ _).2 ⟨source, hs, _, ht, rfl⟩⟩,
      (mem_productFirst _ _ _).2 ⟨k, hk, enums, he, rfl⟩⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})
theorem preparedWitnessCertificateGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {stages Q K E : ZFSet.{u}} (hStages : stages ∈ M.sets) (hQ : Q ∈ M.sets)
    (hK : K ∈ M.sets) (hE : E ∈ M.sets) :
    preparedWitnessCertificateGraph stages Q K E ∈ M.sets := by
  have ht := M.prod_mem pairing unions powers separation hK hE
  have ho := M.prod_mem pairing unions powers separation hQ ht
  have hL := M.prod_mem pairing unions powers separation hStages ho
  exact M.relationCompose_mem pairing unions powers separation hL ht hK
    (M.relationCompose_mem pairing unions powers separation hL ho ht
      (M.productSecond_mem pairing unions powers separation hStages ho)
      (M.productSecond_mem pairing unions powers separation hQ ht))
    (M.productFirst_mem pairing unions powers separation hK hE)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
