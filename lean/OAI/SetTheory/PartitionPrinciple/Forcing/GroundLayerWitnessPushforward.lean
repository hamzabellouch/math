import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRawLayerPushforward

namespace OAI

section

namespace PartitionPilot.Forcing.GrowthLayerWitnessCode
open SetFormula
universe u

theorem ground_pushforward
    {M : TransitiveGround.{u}} {Qs rs μs A B rA rB μA μB old born t N z e : ZFSet.{u}}
    (code : GrowthLayerWitnessCode Qs rs μs A rA μA old t N z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (he : e ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hN : N ∈ M.sets) (hz : z ∈ M.sets)
    (source : MeetOrderCode A rA μA) (embedding : MeetEmbeddingCode A B rA rB μA μB e)
    (preserves : ∀ x y a, ZFSet.pair x y ∈ e →
      (ZFSet.pair y a ∈ born ↔ ZFSet.pair x a ∈ old))
    (noNew : ∀ y ∈ B, ZFSet.pair y t ∈ born → ∃ x ∈ A, ZFSet.pair x y ∈ e) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode Qs rs μs B rB μB born t N z' := by
  rcases code with ⟨D, injection, rfl, code⟩ |
    ⟨I, parts, Indices, Maps, W, injection, rfl, code⟩ |
    ⟨I, Indices, Maps, W, Components, F, rfl, code⟩
  · have fields := M.nonemptyTupleCode_field_mem 2 _ hz
    obtain ⟨D', hD', injection', hInjection', copied⟩ := code.ground_pushforward
      pairing unions powers separation hA hB hN he (fields 1) (fields 2)
      embedding.injection preserves noNew
    exact ⟨countableLayerWitness D' injection', M.countableLayerWitness_mem pairing hD' hInjection',
      Or.inl ⟨D', injection', rfl, copied⟩⟩
  · have fields := M.nonemptyTupleCode_field_mem 6 _ hz
    obtain ⟨hMaps', hW', hParts', copied⟩ := code.ground_pushforward
      pairing unions powers separation hA hB he hQs (fields 1) (fields 2) (fields 4)
      embedding preserves noNew
    exact ⟨copyLayerWitness I (relationCompose I A B parts e) Indices
        (M.mapFamilyPushforward I (familyPointBound Qs) A B Maps e)
        (M.groundRelations (familyPointBound Qs) B) injection,
      M.copyLayerWitness_mem pairing unions (fields 1) hParts' (fields 3) hMaps' hW' (fields 6),
      Or.inr (Or.inl ⟨I, _, Indices, _, _, injection, rfl, copied⟩)⟩
  · have fields := M.nonemptyTupleCode_field_mem 6 _ hz
    obtain ⟨hMaps', hW', hComponents', hF', copied⟩ := code.ground_pushforward
      pairing unions powers separation hA hB he hQs (fields 1) (fields 3) (fields 5) (fields 6)
      source embedding preserves noNew
    exact ⟨separatedLayerWitness I Indices
        (M.mapFamilyPushforward I (familyPointBound Qs) A B Maps e)
        (M.groundRelations (familyPointBound Qs) B)
        (pushedHeightGraph F B I (layerFiberEmbedding F B e) Components)
        (relationImage F B (layerFiberEmbedding F B e)),
      M.separatedLayerWitness_mem pairing unions (fields 1) (fields 2) hMaps' hW' hComponents' hF',
      Or.inr (Or.inr ⟨I, Indices, _, _, _, _, rfl, copied⟩)⟩

end PartitionPilot.Forcing.GrowthLayerWitnessCode

end

end OAI
