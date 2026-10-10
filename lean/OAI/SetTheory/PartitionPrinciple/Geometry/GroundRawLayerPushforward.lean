import OAI.SetTheory.PartitionPrinciple.Definability.GroundLiftedRowTupleProvenance
import OAI.SetTheory.PartitionPrinciple.Definability.TaggedGrowthLayerFormulas
import OAI.SetTheory.PartitionPrinciple.Forcing.OwnerBirthLayerTransport

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def mapFamilyDiagonal (I : ZFSet.{u}) : ZFSet.{u} :=
  pairedGraph I I I (identityFunctionGraph I) (identityFunctionGraph I)

theorem pair_mem_mapFamilyDiagonal (I i k : ZFSet.{u}) :
    ZFSet.pair i k ∈ mapFamilyDiagonal I ↔ i ∈ I ∧ k = ZFSet.pair i i := by
  constructor
  · intro entry
    obtain ⟨j, hj, a, _, b, _, equal, first, second⟩ := (mem_pairedGraph _ _ _ _ _ _).1 entry
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    have fa := (pair_mem_identityFunctionGraph I i a).1 first
    have fb := (pair_mem_identityFunctionGraph I i b).1 second
    exact ⟨hj, congrArg₂ ZFSet.pair fa.1.symm fb.1.symm⟩
  · rintro ⟨hi, rfl⟩
    exact (pair_mem_pairedGraph _ _ _ _ _ _ _ _).2 ⟨hi, hi, hi,
      (pair_mem_identityFunctionGraph I i i).2 ⟨rfl, hi⟩,
      (pair_mem_identityFunctionGraph I i i).2 ⟨rfl, hi⟩⟩

theorem mapFamilyDiagonal_function (I : ZFSet.{u}) :
    ZFSet.IsFunc I (ZFSet.prod I I) (mapFamilyDiagonal I) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi, a, ha, b, hb, rfl, _, _⟩ := (mem_pairedGraph _ _ _ _ _ _).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hi, ZFSet.pair_mem_prod.2 ⟨ha, hb⟩⟩
  intro i hi
  exact ⟨ZFSet.pair i i, (pair_mem_mapFamilyDiagonal I i _).2 ⟨hi, rfl⟩,
    fun k hk => ((pair_mem_mapFamilyDiagonal I i k).1 hk).2⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def mapFamilyPushforward (I U A B Maps e : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose I (ZFSet.prod I I) (M.groundRelations U B) (mapFamilyDiagonal I)
    (M.groundPairCompositions (ZFSet.prod I I) I I U A B Maps (constantFamilyGraph I e))

theorem mapFamilyPushforward_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I U A B Maps e : ZFSet.{u}}
    (hI : I ∈ M.sets) (hU : U ∈ M.sets) (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (hMaps : Maps ∈ M.sets) (he : e ∈ M.sets) (maps : FunctionGraphOn I Maps) :
    M.mapFamilyPushforward I U A B Maps e ∈ M.sets ∧
      ZFSet.IsFunc I (M.groundRelations U B) (M.mapFamilyPushforward I U A B Maps e) ∧
      ∀ i f c, ZFSet.pair i f ∈ Maps →
        (ZFSet.pair i c ∈ M.mapFamilyPushforward I U A B Maps e ↔
          c = relationCompose U A B f e) := by
  have hII := M.prod_mem pairing unions powers separation hI hI
  have hW := M.groundRelations_mem pairing unions powers separation hU hB
  have hConst := M.constantFamilyGraph_mem pairing unions powers separation hI he
  have composed := M.groundPairCompositions_spec pairing unions powers separation
    hII hI hI hU hA hB hMaps hConst maps
    ⟨{e}, constantFamilyGraph_function I e⟩ (fun _ hx => hx)
  have hId := M.identityFunctionGraph_mem pairing unions powers separation hI
  have hDelta := M.pairedGraph_mem pairing unions powers separation hI hI hI hId hId
  refine ⟨M.relationCompose_mem pairing unions powers separation hI hII hW hDelta composed.1,
    relationCompose_function_of_subset (mapFamilyDiagonal_function I) composed.2.1 (fun _ hx => hx), ?_⟩
  intro i f c entry
  have hi := maps.pair_source entry
  have constant := (pair_mem_constantFamilyGraph I e i e).2 ⟨hi, rfl⟩
  have atDiagonal := composed.2.2 i i f e c entry constant
  constructor
  · intro copied
    obtain ⟨_, _, k, _, diagonal, output⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 copied
    have equal := ((pair_mem_mapFamilyDiagonal I i k).1 diagonal).2
    rw [equal] at output
    exact (atDiagonal.1 output).2
  · intro equal
    have output := atDiagonal.2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hi⟩, equal⟩
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hi,
      (ZFSet.pair_mem_prod.1 (composed.2.1.1 output)).2,
      ZFSet.pair i i, ZFSet.pair_mem_prod.2 ⟨hi, hi⟩,
      (pair_mem_mapFamilyDiagonal I i _).2 ⟨hi, rfl⟩, output⟩

end TransitiveGround

theorem relationImage_compose_bound {P U A B f e x y : ZFSet.{u}}
    (subset : P ⊆ U) (image : x ∈ relationImage P A f)
    (hy : y ∈ B) (copied : ZFSet.pair x y ∈ e) :
    y ∈ relationImage P B (relationCompose U A B f e) := by
  obtain ⟨hx, p, hp, entry⟩ := (mem_relationImage _ _ _ _).1 image
  exact (mem_relationImage _ _ _ _).2 ⟨hy, p, hp,
    (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨subset hp, hy, x, hx, entry, copied⟩⟩

namespace CopyEmbeddingFamilyCode

theorem pushforward
    {Qs rs μs A B rA rB μA μB t I Indices Maps Maps' U e : ZFSet.{u}}
    (code : CopyEmbeddingFamilyCode Qs rs μs A rA μA t I Indices Maps)
    (maps : FunctionGraphOn I Maps)
    (entries : ∀ i f c, ZFSet.pair i f ∈ Maps →
      (ZFSet.pair i c ∈ Maps' ↔ c = relationCompose U A B f e))
    (bound : ∀ s P, ZFSet.pair s P ∈ Qs → P ⊆ U)
    (embedding : MeetEmbeddingCode A B rA rB μA μB e) :
    CopyEmbeddingFamilyCode Qs rs μs B rB μB t I Indices Maps' := by
  intro i hi s hs c P R V index map qField rField mField
  obtain ⟨f, oldMap⟩ := maps.total hi
  have original := code i hi s hs f P R V index oldMap qField rField mField
  rw [(entries i f c oldMap).1 map,
    relationCompose_domain_eq (bound s P qField) original.injection.function.1]
  exact original.compose embedding
end CopyEmbeddingFamilyCode

namespace CountableLayerCode

theorem ground_pushforward
    {M : TransitiveGround.{u}} {A B old born t D N injection e : ZFSet.{u}}
    (code : CountableLayerCode A old t D N injection)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hN : N ∈ M.sets) (he : e ∈ M.sets)
    (hD : D ∈ M.sets) (hInjection : injection ∈ M.sets)
    (embedding : InjectionCode A B e)
    (preserves : ∀ x y a, ZFSet.pair x y ∈ e →
      (ZFSet.pair y a ∈ born ↔ ZFSet.pair x a ∈ old))
    (noNew : ∀ y ∈ B, ZFSet.pair y t ∈ born → ∃ x ∈ A, ZFSet.pair x y ∈ e) :
    ∃ D' ∈ M.sets, ∃ injection' ∈ M.sets, CountableLayerCode B born t D' N injection' := by
  let D0 := ZFSet.sep (fun x => x ∈ A) D
  let f0 := ZFSet.sep (fun z => z ∈ ZFSet.prod D0 N) injection
  let e0 := ZFSet.sep (fun z => z ∈ ZFSet.prod D0 B) e
  have hD0 : D0 ∈ M.sets := M.bounded_separation_mem separation (.mem 0 1)
    (extend A Fin.elim0) (Fin.cases hA (fun i => Fin.elim0 i)) hD
  have hf0 : f0 ∈ M.sets := M.injection_restriction_mem separation hD0 hN hInjection
  have he0 : e0 ∈ M.sets := M.injection_restriction_mem separation hD0 hB he
  have fcode : InjectionCode D0 N f0 := code.small.restrict (fun _ hx => (ZFSet.mem_sep.1 hx).1)
  have ecode : InjectionCode D0 B e0 := embedding.restrict (fun _ hx => (ZFSet.mem_sep.1 hx).2)
  refine ⟨relationImage D0 B e0, M.relationImage_mem separation hD0 hB he0,
    pushedHeightGraph D0 B N e0 f0,
    M.pushedHeightGraph_mem pairing unions powers separation hD0 hB hN he0 hf0,
    ecode.converse_image.compose fcode, ?_⟩
  intro y hy yt
  obtain ⟨x, hx, copied⟩ := noNew y hy yt
  have hD0x : x ∈ D0 := ZFSet.mem_sep.2 ⟨code.cover x hx ((preserves x y t copied).1 yt), hx⟩
  exact (mem_relationImage _ _ _ _).2 ⟨hy, x, hD0x,
    ZFSet.mem_sep.2 ⟨copied, ZFSet.pair_mem_prod.2 ⟨hD0x, hy⟩⟩⟩
end CountableLayerCode

namespace CopyLayerCode

theorem ground_pushforward
    {M : TransitiveGround.{u}}
    {Qs rs μs A B rA rB μA μB old born t I parts Indices Maps W N injection e : ZFSet.{u}}
    (code : CopyLayerCode Qs rs μs A rA μA old t I parts Indices Maps W N injection)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (he : e ∈ M.sets) (hQs : Qs ∈ M.sets)
    (hI : I ∈ M.sets) (hParts : parts ∈ M.sets) (hMaps : Maps ∈ M.sets)
    (embedding : MeetEmbeddingCode A B rA rB μA μB e)
    (preserves : ∀ x y a, ZFSet.pair x y ∈ e →
      (ZFSet.pair y a ∈ born ↔ ZFSet.pair x a ∈ old))
    (noNew : ∀ y ∈ B, ZFSet.pair y t ∈ born → ∃ x ∈ A, ZFSet.pair x y ∈ e) :
    let U := familyPointBound Qs
    let Maps' := M.mapFamilyPushforward I U A B Maps e
    let W' := M.groundRelations U B
    let parts' := relationCompose I A B parts e
    Maps' ∈ M.sets ∧ W' ∈ M.sets ∧ parts' ∈ M.sets ∧
      CopyLayerCode Qs rs μs B rB μB born t I parts' Indices Maps' W' N injection := by
  dsimp only
  have hU := M.familyPointBound_mem unions hQs
  have maps : FunctionGraphOn I Maps := ⟨W, code.maps⟩
  have pushed := M.mapFamilyPushforward_spec pairing unions powers separation hI hU hA hB hMaps he maps
  have bound : ∀ s P, ZFSet.pair s P ∈ Qs → P ⊆ familyPointBound Qs :=
    fun _ _ entry _ hp => mem_familyPointBound_of_entry entry hp
  refine ⟨pushed.1, M.groundRelations_mem pairing unions powers separation hU hB,
    M.relationCompose_mem pairing unions powers separation hI hA hB hParts he,
    code.small, code.indices, pushed.2.1,
    code.embedding.pushforward maps pushed.2.2 bound embedding, ?_, ?_⟩
  · intro y hy yt
    obtain ⟨x, hx, copied⟩ := noNew y hy yt
    obtain ⟨i, hi, part⟩ := code.cover x hx ((preserves x y t copied).1 yt)
    exact ⟨i, hi, (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hi, hy, x, hx, part, copied⟩⟩
  · intro i hi s hs c P y hy index map qField part
    obtain ⟨f, oldMap⟩ := maps.total hi
    rw [(pushed.2.2 i f c oldMap).1 map]
    obtain ⟨_, _, x, hx, original, copied⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 part
    exact relationImage_compose_bound (bound s P qField)
      (code.inCopy i hi s hs f P x hx index oldMap qField original) hy copied
end CopyLayerCode

noncomputable def layerFiberEmbedding (F B e : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ ZFSet.prod F B) e

namespace SeparatedLayerCode

theorem ground_pushforward
    {M : TransitiveGround.{u}}
    {Qs rs μs A B rA rB μA μB old born t I Indices Maps W Components F e : ZFSet.{u}}
    (code : SeparatedLayerCode Qs rs μs A rA μA old t I Indices Maps W Components F)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (he : e ∈ M.sets) (hQs : Qs ∈ M.sets)
    (hI : I ∈ M.sets) (hMaps : Maps ∈ M.sets) (hComponents : Components ∈ M.sets) (hF : F ∈ M.sets)
    (source : MeetOrderCode A rA μA) (embedding : MeetEmbeddingCode A B rA rB μA μB e)
    (preserves : ∀ x y a, ZFSet.pair x y ∈ e →
      (ZFSet.pair y a ∈ born ↔ ZFSet.pair x a ∈ old))
    (noNew : ∀ y ∈ B, ZFSet.pair y t ∈ born → ∃ x ∈ A, ZFSet.pair x y ∈ e) :
    let U := familyPointBound Qs
    let Maps' := M.mapFamilyPushforward I U A B Maps e
    let W' := M.groundRelations U B
    let eF := layerFiberEmbedding F B e
    let F' := relationImage F B eF
    let Components' := pushedHeightGraph F B I eF Components
    Maps' ∈ M.sets ∧ W' ∈ M.sets ∧ Components' ∈ M.sets ∧ F' ∈ M.sets ∧
      SeparatedLayerCode Qs rs μs B rB μB born t I Indices Maps' W' Components' F' := by
  dsimp only
  have hU := M.familyPointBound_mem unions hQs
  have maps : FunctionGraphOn I Maps := ⟨W, code.maps⟩
  have pushed := M.mapFamilyPushforward_spec pairing unions powers separation hI hU hA hB hMaps he maps
  have bound : ∀ s P, ZFSet.pair s P ∈ Qs → P ⊆ familyPointBound Qs :=
    fun _ _ entry _ hp => mem_familyPointBound_of_entry entry hp
  have fiberPoint : ∀ x ∈ F, x ∈ A ∧ ZFSet.pair x t ∈ old := by
    intro x hx
    exact (mem_layerBirthFiber A old t x).1 (code.fiber ▸ hx)
  have ecode : InjectionCode F B (layerFiberEmbedding F B e) :=
    embedding.injection.restrict (fun x hx => (fiberPoint x hx).1)
  have heF : layerFiberEmbedding F B e ∈ M.sets := M.injection_restriction_mem separation hF hB he
  have fiberEq : relationImage F B (layerFiberEmbedding F B e) = layerBirthFiber B born t := by
    apply ZFSet.ext
    intro y
    rw [mem_relationImage, mem_layerBirthFiber]
    constructor
    · rintro ⟨hy, x, hx, copied⟩
      exact ⟨hy, (preserves x y t (ZFSet.mem_sep.1 copied).1).2 (fiberPoint x hx).2⟩
    · rintro ⟨hy, yt⟩
      obtain ⟨x, hx, copied⟩ := noNew y hy yt
      have hFx : x ∈ F := code.fiber.symm ▸
        (mem_layerBirthFiber A old t x).2 ⟨hx, (preserves x y t copied).1 yt⟩
      exact ⟨hy, x, hFx, ZFSet.mem_sep.2 ⟨copied, ZFSet.pair_mem_prod.2 ⟨hFx, hy⟩⟩⟩
  refine ⟨pushed.1, M.groundRelations_mem pairing unions powers separation hU hB,
    M.pushedHeightGraph_mem pairing unions powers separation hF hB hI heF hComponents,
    M.relationImage_mem separation hF hB heF,
    code.indices, pushed.2.1, fiberEq, pushedHeightGraph_function ecode code.components,
    code.embedding.pushforward maps pushed.2.2 bound embedding, ?_, ?_⟩
  · intro i hi s hs c P y hy index map qField component
    obtain ⟨f, oldMap⟩ := maps.total hi
    rw [(pushed.2.2 i f c oldMap).1 map]
    obtain ⟨_, _, x, hx, inverse, oldComponent⟩ :=
      (pair_mem_relationCompose _ _ _ _ _ _ _).1 component
    have copied := (pair_mem_relationConverse _ _ _ _ _).1 inverse
    exact relationImage_compose_bound (bound s P qField)
      (code.cover i hi s hs f P x (fiberPoint x hx).1 index oldMap qField oldComponent)
      hy (ZFSet.mem_sep.1 copied.2.2).1
  · intro y hy z hz i hi j hj yi zj different
    obtain ⟨_, x, hx, xy⟩ := (mem_relationImage _ _ _ _).1 hy
    obtain ⟨_, w, hw, wz⟩ := (mem_relationImage _ _ _ _).1 hz
    have xi := (pushedHeightGraph_entry ecode code.components xy).1 yi
    have wj := (pushedHeightGraph_entry ecode code.components wz).1 zj
    exact (code.separated x hx w hw i hi j hj xi wj different).map source embedding
      (fun a b s copied born => (preserves a b s copied).2 born)
      (ZFSet.mem_sep.1 xy).1 (ZFSet.mem_sep.1 wz).1
end SeparatedLayerCode

end PartitionPilot.Forcing

end OAI
