import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalGroupEmbeddings
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCountableLayerCodes
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundLayerBirthFibers

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def oldBridgeFormula {n} (L r μ birth t x y : Fin n) : BoundedFormula n :=
  disj
    (exMem L (exMem t.succ (.conj
      (tripleMembershipFormula x.succ.succ y.succ.succ 1 μ.succ.succ)
      (pairMembershipFormula 1 0 birth.succ.succ))))
    (exMem L (exMem t.succ (.conj (pairMembershipFormula 1 0 birth.succ.succ)
      (disj
        (.conj (pairMembershipFormula x.succ.succ 1 r.succ.succ)
          (pairMembershipFormula 1 y.succ.succ r.succ.succ))
        (.conj (pairMembershipFormula y.succ.succ 1 r.succ.succ)
          (pairMembershipFormula 1 x.succ.succ r.succ.succ))))))

theorem truth_oldBridgeFormula {n} (L r μ birth t x y : Fin n) (env : Fin n → ZFSet.{u})
    (meet : MeetOrderCode (env L) (env r) (env μ)) :
    Truth (oldBridgeFormula L r μ birth t x y) env ↔
      OldBridgeCode (env L) (env r) (env μ) (env birth) (env t) (env x) (env y) := by
  simp only [oldBridgeFormula, truth_disj, truth_exMem, Truth,
    truth_tripleMembershipFormula, truth_pairMembershipFormula, OldBridgeCode]
  constructor
  · rintro (⟨z, _, a, ha, entry, born⟩ | ⟨z, hz, a, ha, born, bridge⟩)
    · exact Or.inl ⟨z, a, entry, born, ha⟩
    · exact Or.inr ⟨z, hz, a, born, ha, bridge⟩
  · rintro (⟨z, a, entry, born, ha⟩ | ⟨z, hz, a, born, ha, bridge⟩)
    · exact Or.inl ⟨z, (ZFSet.pair_mem_prod.1 (meet.operation.1 entry)).2, a, ha, entry, born⟩
    · exact Or.inr ⟨z, hz, a, ha, born, bridge⟩

theorem realize_oldBridgeFormula (M : TransitiveGround.{u}) {n}
    (L r μ birth t x y : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meet : MeetOrderCode (env L) (env r) (env μ)) :
    Realize M.sets (oldBridgeFormula L r μ birth t x y).toFormula env ↔
      OldBridgeCode (env L) (env r) (env μ) (env birth) (env t) (env x) (env y) :=
  (realize_toFormula M _ env members).trans (truth_oldBridgeFormula L r μ birth t x y env meet)





def meetEmbeddingFormula {n} (P L rP rL μP μL e : Fin n) : BoundedFormula n :=
  let lift4 (i : Fin n) := i.succ.succ.succ.succ
  let lift6 (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  .conj (injectionFormula P L e)
    (.conj
      (.allMem P (.allMem P.succ (.allMem L.succ.succ (.allMem L.succ.succ.succ
        (imp (.conj (pairMembershipFormula 3 2 (lift4 rP))
          (.conj (pairMembershipFormula 3 1 (lift4 e))
            (pairMembershipFormula 2 0 (lift4 e))))
          (pairMembershipFormula 1 0 (lift4 rL)))))))
      (.allMem P (.allMem P.succ (.allMem P.succ.succ
        (.allMem L.succ.succ.succ (.allMem L.succ.succ.succ.succ
          (.allMem L.succ.succ.succ.succ.succ
            (imp (.conj (tripleMembershipFormula 5 4 3 (lift6 μP))
              (.conj (pairMembershipFormula 5 2 (lift6 e))
                (.conj (pairMembershipFormula 4 1 (lift6 e))
                  (pairMembershipFormula 3 0 (lift6 e)))))
              (tripleMembershipFormula 2 1 0 (lift6 μL))))))))))

theorem truth_meetEmbeddingFormula {n} (P L rP rL μP μL e : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (meetEmbeddingFormula P L rP rL μP μL e) env ↔
      MeetEmbeddingCode (env P) (env L) (env rP) (env rL) (env μP) (env μL) (env e) := by
  simp only [meetEmbeddingFormula, Truth, truth_injectionFormula, truth_imp,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  constructor
  · rintro ⟨injection, monotone, meet⟩
    have bounds {x y : ZFSet.{u}} (entry : ZFSet.pair x y ∈ env e) :
        x ∈ env P ∧ y ∈ env L := ZFSet.pair_mem_prod.1 (injection.function.1 entry)
    refine ⟨injection, ?_, ?_⟩
    · intro x y x' y' lower first second
      exact monotone x (bounds first).1 y (bounds second).1
        x' (bounds first).2 y' (bounds second).2 ⟨lower, first, second⟩
    · intro x y z x' y' z' output first second third
      exact meet x (bounds first).1 y (bounds second).1 z (bounds third).1
        x' (bounds first).2 y' (bounds second).2 z' (bounds third).2
        ⟨output, first, second, third⟩
  · intro code
    exact ⟨code.injection,
      fun x _ y _ x' _ y' _ h => code.monotone x y x' y' h.1 h.2.1 h.2.2,
      fun x _ y _ z _ x' _ y' _ z' _ h =>
        code.map_meet x y z x' y' z' h.1 h.2.1 h.2.2.1 h.2.2.2⟩

theorem realize_meetEmbeddingFormula (M : TransitiveGround.{u}) {n}
    (P L rP rL μP μL e : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (meetEmbeddingFormula P L rP rL μP μL e).toFormula env ↔
      MeetEmbeddingCode (env P) (env L) (env rP) (env rL) (env μP) (env μL) (env e) :=
  (realize_toFormula M _ env members).trans (truth_meetEmbeddingFormula P L rP rL μP μL e env)





def groupEmbeddingFormula {n} (G H mG mH oneG oneH e : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  .conj (injectionFormula G H e) (.conj (pairMembershipFormula oneG oneH e)
    (.allMem G (.allMem G.succ (.allMem G.succ.succ
      (.allMem H.succ.succ.succ (.allMem H.succ.succ.succ.succ
        (.allMem H.succ.succ.succ.succ.succ
          (imp (.conj (tripleMembershipFormula 5 4 3 (lift mG))
            (.conj (pairMembershipFormula 5 2 (lift e))
              (.conj (pairMembershipFormula 4 1 (lift e))
                (pairMembershipFormula 3 0 (lift e)))))
            (tripleMembershipFormula 2 1 0 (lift mH))))))))))

theorem truth_groupEmbeddingFormula {n} (G H mG mH oneG oneH e : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (groupEmbeddingFormula G H mG mH oneG oneH e) env ↔
      GroupEmbeddingCode (env G) (env H) (env mG) (env mH) (env oneG) (env oneH) (env e) := by
  simp only [groupEmbeddingFormula, Truth, truth_injectionFormula, truth_imp,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  constructor
  · rintro ⟨injection, one, mul⟩
    have bounds {x y : ZFSet.{u}} (entry : ZFSet.pair x y ∈ env e) :
        x ∈ env G ∧ y ∈ env H := ZFSet.pair_mem_prod.1 (injection.function.1 entry)
    refine ⟨injection, one, ?_⟩
    intro a b c a' b' c' product first second third
    exact mul a (bounds first).1 b (bounds second).1 c (bounds third).1
      a' (bounds first).2 b' (bounds second).2 c' (bounds third).2
      ⟨product, first, second, third⟩
  · intro code
    exact ⟨code.injection, code.one, fun a _ b _ c _ a' _ b' _ c' _ h =>
      code.mul a b c a' b' c' h.1 h.2.1 h.2.2.1 h.2.2.2⟩

theorem realize_groupEmbeddingFormula (M : TransitiveGround.{u}) {n}
    (G H mG mH oneG oneH e : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (groupEmbeddingFormula G H mG mH oneG oneH e).toFormula env ↔
      GroupEmbeddingCode (env G) (env H) (env mG) (env mH) (env oneG) (env oneH) (env e) :=
  (realize_toFormula M _ env members).trans
    (truth_groupEmbeddingFormula G H mG mH oneG oneH e env)

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing
open SetFormula
universe u

def CopyEmbeddingFamilyCode (Qs rs μs L r μ t I Indices Maps : ZFSet.{u}) : Prop :=
  ∀ i ∈ I, ∀ s ∈ t, ∀ e P R V,
    ZFSet.pair i s ∈ Indices → ZFSet.pair i e ∈ Maps →
    ZFSet.pair s P ∈ Qs → ZFSet.pair s R ∈ rs → ZFSet.pair s V ∈ μs →
    MeetEmbeddingCode P L R r V μ e

def CopyImageCoverCode (Qs L t I parts Indices Maps : ZFSet.{u}) : Prop :=
  ∀ i ∈ I, ∀ s ∈ t, ∀ e P, ∀ x ∈ L,
    ZFSet.pair i s ∈ Indices → ZFSet.pair i e ∈ Maps →
    ZFSet.pair s P ∈ Qs → ZFSet.pair i x ∈ parts → x ∈ relationImage P L e

namespace BoundedFormula

def doubleUnionMemberFormula {n} (x f : Fin n) : BoundedFormula n :=
  exMem f (exMem 0 (.mem x.succ.succ 0))

theorem truth_doubleUnionMemberFormula {n} (x f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (doubleUnionMemberFormula x f) env ↔ env x ∈ ⋃₀ ⋃₀ env f := by
  simp only [doubleUnionMemberFormula, truth_exMem, Truth]
  change (∃ a ∈ env f, ∃ b ∈ a, env x ∈ b) ↔ _
  constructor
  · rintro ⟨a, ha, b, hb, hx⟩
    exact ZFSet.mem_sUnion.2 ⟨b, ZFSet.mem_sUnion.2 ⟨a, ha, hb⟩, hx⟩
  · intro hx
    obtain ⟨b, hb, hx⟩ := ZFSet.mem_sUnion.1 hx
    obtain ⟨a, ha, hb⟩ := ZFSet.mem_sUnion.1 hb
    exact ⟨a, ha, b, hb, hx⟩

def doubleUnionEquationFormula {n} (B f : Fin n) : BoundedFormula n :=
  .conj (.allMem B (doubleUnionMemberFormula 0 f.succ))
    (.allMem f (.allMem 0 (.allMem 0 (.mem 0 B.succ.succ.succ))))

theorem truth_doubleUnionEquationFormula {n} (B f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (doubleUnionEquationFormula B f) env ↔ env B = ⋃₀ ⋃₀ env f := by
  simp only [doubleUnionEquationFormula, Truth, truth_doubleUnionMemberFormula]
  change ((∀ x ∈ env B, x ∈ ⋃₀ ⋃₀ env f) ∧
    ∀ a ∈ env f, ∀ b ∈ a, ∀ x ∈ b, x ∈ env B) ↔ _
  constructor
  · rintro ⟨subset, cover⟩
    apply ZFSet.ext
    intro x
    refine ⟨subset x, ?_⟩
    intro hx
    obtain ⟨b, hb, hx⟩ := ZFSet.mem_sUnion.1 hx
    obtain ⟨a, ha, hb⟩ := ZFSet.mem_sUnion.1 hb
    exact cover a ha b hb x hx
  · intro equal
    rw [equal]
    exact ⟨fun _ hx => hx, fun a ha b hb x hx =>
      ZFSet.mem_sUnion.2 ⟨b, ZFSet.mem_sUnion.2 ⟨a, ha, hb⟩, hx⟩⟩

def copyEmbeddingFamilyFormula {n}
    (Qs rs μs L r μ t I Indices Maps W QB RB MB : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  .allMem I (.allMem t.succ (.allMem W.succ.succ (.allMem QB.succ.succ.succ
    (.allMem RB.succ.succ.succ.succ (.allMem MB.succ.succ.succ.succ.succ
      (imp (.conj (pairMembershipFormula 5 4 (lift Indices))
        (.conj (pairMembershipFormula 5 3 (lift Maps))
          (.conj (pairMembershipFormula 4 2 (lift Qs))
            (.conj (pairMembershipFormula 4 1 (lift rs))
              (pairMembershipFormula 4 0 (lift μs))))))
        (meetEmbeddingFormula 2 (lift L) 1 (lift r) 0 (lift μ) 3)))))))

theorem truth_copyEmbeddingFamilyFormula {n}
    (Qs rs μs L r μ t I Indices Maps W QB RB MB : Fin n) (env : Fin n → ZFSet.{u})
    (maps : ZFSet.IsFunc (env I) (env W) (env Maps))
    (eqQ : env QB = ⋃₀ ⋃₀ env Qs) (eqR : env RB = ⋃₀ ⋃₀ env rs)
    (eqM : env MB = ⋃₀ ⋃₀ env μs) :
    Truth (copyEmbeddingFamilyFormula Qs rs μs L r μ t I Indices Maps W QB RB MB) env ↔
      CopyEmbeddingFamilyCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ)
        (env t) (env I) (env Indices) (env Maps) := by
  simp only [copyEmbeddingFamilyFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_meetEmbeddingFormula]
  constructor
  · intro property i hi s hs e P R V index map qField rField mField
    have hP : P ∈ env QB := eqQ.symm ▸ pair_second_mem_doubleUnion qField
    have hR : R ∈ env RB := eqR.symm ▸ pair_second_mem_doubleUnion rField
    have hV : V ∈ env MB := eqM.symm ▸ pair_second_mem_doubleUnion mField
    exact property i hi s hs e (ZFSet.pair_mem_prod.1 (maps.1 map)).2
      P hP R hR V hV ⟨index, map, qField, rField, mField⟩
  · intro code i hi s hs e _ P _ R _ V _ condition
    exact code i hi s hs e P R V condition.1 condition.2.1 condition.2.2.1
      condition.2.2.2.1 condition.2.2.2.2

def copyImageCoverFormula {n} (Qs L t I parts Indices Maps W QB : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ
  .allMem I (.allMem t.succ (.allMem W.succ.succ (.allMem QB.succ.succ.succ
    (.allMem L.succ.succ.succ.succ
      (imp (.conj (pairMembershipFormula 4 3 (lift Indices))
        (.conj (pairMembershipFormula 4 2 (lift Maps))
          (.conj (pairMembershipFormula 3 1 (lift Qs))
            (pairMembershipFormula 4 0 (lift parts)))))
        (imageMemberFormula 0 1 2))))))

theorem truth_copyImageCoverFormula {n} (Qs L t I parts Indices Maps W QB : Fin n)
    (env : Fin n → ZFSet.{u}) (maps : ZFSet.IsFunc (env I) (env W) (env Maps))
    (eqQ : env QB = ⋃₀ ⋃₀ env Qs) :
    Truth (copyImageCoverFormula Qs L t I parts Indices Maps W QB) env ↔
      CopyImageCoverCode (env Qs) (env L) (env t) (env I) (env parts) (env Indices) (env Maps) := by
  simp only [copyImageCoverFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_imageMemberFormula]
  constructor
  · intro property i hi s hs e P x hx index map qField part
    have hP : P ∈ env QB := eqQ.symm ▸ pair_second_mem_doubleUnion qField
    exact (mem_relationImage P (env L) e x).2 ⟨hx,
      property i hi s hs e (ZFSet.pair_mem_prod.1 (maps.1 map)).2
        P hP x hx ⟨index, map, qField, part⟩⟩
  · intro code i hi s hs e _ P _ x hx condition
    exact ((mem_relationImage P (env L) e x).1
      (code i hi s hs e P x hx condition.1 condition.2.1 condition.2.2.1 condition.2.2.2)).2

end BoundedFormula





structure CopyLayerCode
    (Qs rs μs L r μ birth t I parts Indices Maps W N injection : ZFSet.{u}) : Prop where
  small : InjectionCode I N injection
  indices : ZFSet.IsFunc I t Indices
  maps : ZFSet.IsFunc I W Maps
  embedding : CopyEmbeddingFamilyCode Qs rs μs L r μ t I Indices Maps
  cover : ∀ x ∈ L, ZFSet.pair x t ∈ birth → ∃ i ∈ I, ZFSet.pair i x ∈ parts
  inCopy : CopyImageCoverCode Qs L t I parts Indices Maps

namespace BoundedFormula

def copyLayerFormula {n}
    (Qs rs μs L r μ birth t I parts Indices Maps W N injection QB RB MB : Fin n) : BoundedFormula n :=
  .conj (doubleUnionEquationFormula QB Qs)
    (.conj (doubleUnionEquationFormula RB rs)
      (.conj (doubleUnionEquationFormula MB μs)
        (.conj (injectionFormula I N injection)
          (.conj (functionFormula I t Indices)
            (.conj (functionFormula I W Maps)
              (.conj (copyEmbeddingFamilyFormula Qs rs μs L r μ t I Indices Maps W QB RB MB)
                (.conj (.allMem L (imp (pairMembershipFormula 0 t.succ birth.succ)
                  (exMem I.succ (pairMembershipFormula 0 1 parts.succ.succ))))
                  (copyImageCoverFormula Qs L t I parts Indices Maps W QB))))))))

theorem truth_copyLayerFormula {n}
    (Qs rs μs L r μ birth t I parts Indices Maps W N injection QB RB MB : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (copyLayerFormula Qs rs μs L r μ birth t I parts Indices Maps W N injection QB RB MB) env ↔
      env QB = ⋃₀ ⋃₀ env Qs ∧ env RB = ⋃₀ ⋃₀ env rs ∧ env MB = ⋃₀ ⋃₀ env μs ∧
      CopyLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ) (env birth) (env t)
        (env I) (env parts) (env Indices) (env Maps) (env W) (env N) (env injection) := by
  simp only [copyLayerFormula, Truth, truth_doubleUnionEquationFormula, truth_injectionFormula,
    truth_functionFormula, truth_imp, truth_pairMembershipFormula, truth_exMem]
  constructor
  · rintro ⟨eqQ, eqR, eqM, small, indices, maps, embedding, cover, inCopy⟩
    exact ⟨eqQ, eqR, eqM, small, indices, maps,
      (truth_copyEmbeddingFamilyFormula Qs rs μs L r μ t I Indices Maps W QB RB MB
        env maps eqQ eqR eqM).1 embedding,
      cover, (truth_copyImageCoverFormula Qs L t I parts Indices Maps W QB env maps eqQ).1 inCopy⟩
  · rintro ⟨eqQ, eqR, eqM, code⟩
    exact ⟨eqQ, eqR, eqM, code.small, code.indices, code.maps,
      (truth_copyEmbeddingFamilyFormula Qs rs μs L r μ t I Indices Maps W QB RB MB
        env code.maps eqQ eqR eqM).2 code.embedding,
      code.cover, (truth_copyImageCoverFormula Qs L t I parts Indices Maps W QB env code.maps eqQ).2
        code.inCopy⟩

theorem realize_copyLayerFormula (M : TransitiveGround.{u}) {n}
    (Qs rs μs L r μ birth t I parts Indices Maps W N injection QB RB MB : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets
      (copyLayerFormula Qs rs μs L r μ birth t I parts Indices Maps W N injection QB RB MB).toFormula env ↔
      env QB = ⋃₀ ⋃₀ env Qs ∧ env RB = ⋃₀ ⋃₀ env rs ∧ env MB = ⋃₀ ⋃₀ env μs ∧
      CopyLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ) (env birth) (env t)
        (env I) (env parts) (env Indices) (env Maps) (env W) (env N) (env injection) :=
  (realize_toFormula M _ env members).trans
    (truth_copyLayerFormula Qs rs μs L r μ birth t I parts Indices Maps W N injection QB RB MB env)

end BoundedFormula

namespace CopyLayerCode

noncomputable def toLayer
    {M : TransitiveGround.{u}} {Qs rs μs L r μ birth t I parts Indices Maps W N injection : ZFSet.{u}}
    (code : CopyLayerCode Qs rs μs L r μ birth t I parts Indices Maps W N injection)
    (Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u})
    (hI : I ∈ M.sets) (hParts : parts ∈ M.sets) (hMaps : Maps ∈ M.sets)
    (hInjection : injection ∈ M.sets) (omega : N = ZFSet.omega)
    (history : ∀ s ∈ t, ZFSet.pair s (Space s) ∈ Qs ∧
      ZFSet.pair s (sourceOrder s) ∈ rs ∧ ZFSet.pair s (sourceMeet s) ∈ μs) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t := by
  classical
  let indexGraph : FunctionGraphOn I Indices := ⟨t, code.indices⟩
  let mapGraph : FunctionGraphOn I Maps := ⟨W, code.maps⟩
  let index (i : ZFSet.{u}) := if hi : i ∈ I then indexGraph.value ⟨i, hi⟩ else ∅
  let copy (i : ZFSet.{u}) := if hi : i ∈ I then mapGraph.value ⟨i, hi⟩ else ∅
  have indexEntry (i : ZFSet.{u}) (hi : i ∈ I) : ZFSet.pair i (index i) ∈ Indices := by
    simpa only [index, dite_eq_left hi] using indexGraph.value_entry ⟨i, hi⟩
  have copyEntry (i : ZFSet.{u}) (hi : i ∈ I) : ZFSet.pair i (copy i) ∈ Maps := by
    simpa only [copy, dite_eq_left hi] using mapGraph.value_entry ⟨i, hi⟩
  have earlier (i : ZFSet.{u}) (hi : i ∈ I) : index i ∈ t :=
    (ZFSet.pair_mem_prod.1 (code.indices.1 (indexEntry i hi))).2
  refine .copies I parts hI ⟨injection, hInjection, omega ▸ code.small⟩ hParts
    index copy earlier (fun i hi => M.pair_right (M.transitive hMaps (copyEntry i hi)))
    ?_ code.cover ?_
  · intro i hi
    have fields := history (index i) (earlier i hi)
    exact code.embedding i hi (index i) (earlier i hi) (copy i) (Space (index i))
      (sourceOrder (index i)) (sourceMeet (index i)) (indexEntry i hi) (copyEntry i hi)
      fields.1 fields.2.1 fields.2.2
  · intro i hi x hx part
    exact code.inCopy i hi (index i) (earlier i hi) (copy i) (Space (index i)) x hx
      (indexEntry i hi) (copyEntry i hi) (history (index i) (earlier i hi)).1 part

end CopyLayerCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization
universe u

def ComponentImageCoverCode (Qs L t I Components Indices Maps : ZFSet.{u}) : Prop :=
  ∀ i ∈ I, ∀ s ∈ t, ∀ e P, ∀ x ∈ L,
    ZFSet.pair i s ∈ Indices → ZFSet.pair i e ∈ Maps →
    ZFSet.pair s P ∈ Qs → ZFSet.pair x i ∈ Components → x ∈ relationImage P L e

def ComponentSeparationCode (L r μ birth t F I Components : ZFSet.{u}) : Prop :=
  ∀ x ∈ F, ∀ y ∈ F, ∀ i ∈ I, ∀ j ∈ I,
    ZFSet.pair x i ∈ Components → ZFSet.pair y j ∈ Components → i ≠ j →
      OldBridgeCode L r μ birth t x y

structure SeparatedLayerCode
    (Qs rs μs L r μ birth t I Indices Maps W Components F : ZFSet.{u}) : Prop where
  indices : ZFSet.IsFunc I t Indices
  maps : ZFSet.IsFunc I W Maps
  fiber : F = layerBirthFiber L birth t
  components : ZFSet.IsFunc F I Components
  embedding : CopyEmbeddingFamilyCode Qs rs μs L r μ t I Indices Maps
  cover : ComponentImageCoverCode Qs L t I Components Indices Maps
  separated : ComponentSeparationCode L r μ birth t F I Components

namespace SeparatedLayerCode
variable {M : TransitiveGround.{u}}
variable {Qs rs μs L r μ birth t I Indices Maps W Components F : ZFSet.{u}}
variable (code : SeparatedLayerCode Qs rs μs L r μ birth t I Indices Maps W Components F)

noncomputable def toGrowthLayer
    (hMaps : Maps ∈ M.sets) (Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u})
    (agree : ∀ s ∈ t, ZFSet.pair s (Space s) ∈ Qs ∧
      ZFSet.pair s (sourceOrder s) ∈ rs ∧ ZFSet.pair s (sourceMeet s) ∈ μs) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t := by
  classical
  let indices : FunctionGraphOn I Indices := ⟨t, code.indices⟩
  let maps : FunctionGraphOn I Maps := ⟨W, code.maps⟩
  let components : FunctionGraphOn F Components := ⟨I, code.components⟩
  let member (i : SetMembers I) : {i : ZFSet.{u} // i ∈ I} :=
    ⟨SetMembers.raw i, SetMembers.raw_mem i⟩
  let index (i : SetMembers I) := indices.value (member i)
  let e (i : SetMembers I) := maps.value (member i)
  have earlier (i : SetMembers I) : index i ∈ t :=
    (ZFSet.pair_mem_prod.1 (code.indices.1 (indices.value_entry (member i)))).2
  have embedding (i : SetMembers I) : MeetEmbeddingCode (Space (index i)) L
      (sourceOrder (index i)) r (sourceMeet (index i)) μ (e i) :=
    code.embedding _ (SetMembers.raw_mem i) _ (earlier i) _ _ _ _
      (indices.value_entry (member i)) (maps.value_entry (member i))
      (agree _ (earlier i)).1 (agree _ (earlier i)).2.1 (agree _ (earlier i)).2.2
  let Point := {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth}
  have inFiber (x : Point) : x.val ∈ F :=
    code.fiber.symm ▸ (mem_layerBirthFiber L birth t x.val).2 x.property
  let componentValue (x : Point) := components.value ⟨x.val, inFiber x⟩
  have componentMem (x : Point) : componentValue x ∈ I :=
    (ZFSet.pair_mem_prod.1 (code.components.1 (components.value_entry ⟨x.val, inFiber x⟩))).2
  let component (x : Point) : SetMembers I := SetMembers.ofMem (componentValue x) (componentMem x)
  have componentEntry (x : Point) : ZFSet.pair x.val (SetMembers.raw (component x)) ∈ Components := by
    change ZFSet.pair x.val (SetMembers.raw (SetMembers.ofMem _ _)) ∈ Components
    rw [SetMembers.raw_ofMem]
    exact components.value_entry ⟨x.val, inFiber x⟩
  refine CodedGrowthLayer.separated (SetMembers I) index e earlier
    (fun i => maps.value_mem M hMaps (member i)) embedding component ?_ ?_
  · intro x
    exact code.cover _ (SetMembers.raw_mem (component x)) _ (earlier (component x)) _ _ _
      x.property.1 (indices.value_entry (member (component x)))
      (maps.value_entry (member (component x))) (agree _ (earlier (component x))).1
      (componentEntry x)
  · intro x y different
    exact code.separated _ (inFiber x) _ (inFiber y)
      _ (SetMembers.raw_mem (component x)) _ (SetMembers.raw_mem (component y))
      (componentEntry x) (componentEntry y)
      (fun equal => different (SetMembers.raw_injective I equal))
end SeparatedLayerCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def componentImageCoverFormula {n} (Qs L t I Components Indices Maps W QB : Fin n) :
    BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ
  .allMem I (.allMem t.succ (.allMem W.succ.succ (.allMem QB.succ.succ.succ
    (.allMem L.succ.succ.succ.succ
      (imp (.conj (pairMembershipFormula 4 3 (lift Indices))
        (.conj (pairMembershipFormula 4 2 (lift Maps))
          (.conj (pairMembershipFormula 3 1 (lift Qs))
            (pairMembershipFormula 0 4 (lift Components)))))
        (imageMemberFormula 0 1 2))))))

theorem truth_componentImageCoverFormula {n}
    (Qs L t I Components Indices Maps W QB : Fin n) (env : Fin n → ZFSet.{u})
    (maps : ZFSet.IsFunc (env I) (env W) (env Maps)) (eqQ : env QB = ⋃₀ ⋃₀ env Qs) :
    Truth (componentImageCoverFormula Qs L t I Components Indices Maps W QB) env ↔
      ComponentImageCoverCode (env Qs) (env L) (env t) (env I)
        (env Components) (env Indices) (env Maps) := by
  simp only [componentImageCoverFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_imageMemberFormula]
  constructor
  · intro property i hi s hs e P x hx index map qField part
    have hP : P ∈ env QB := eqQ.symm ▸ pair_second_mem_doubleUnion qField
    exact (mem_relationImage P (env L) e x).2 ⟨hx,
      property i hi s hs e (ZFSet.pair_mem_prod.1 (maps.1 map)).2
        P hP x hx ⟨index, map, qField, part⟩⟩
  · intro code i hi s hs e _ P _ x hx condition
    exact ((mem_relationImage P (env L) e x).1
      (code i hi s hs e P x hx condition.1 condition.2.1 condition.2.2.1 condition.2.2.2)).2

def componentSeparationFormula {n} (L r μ birth t F I Components : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ
  .allMem F (.allMem F.succ (.allMem I.succ.succ (.allMem I.succ.succ.succ
    (imp (.conj (pairMembershipFormula 3 1 (lift Components))
      (.conj (pairMembershipFormula 2 0 (lift Components)) (.neg (.equal 1 0))))
      (oldBridgeFormula (lift L) (lift r) (lift μ) (lift birth) (lift t) 3 2)))))

theorem truth_componentSeparationFormula {n} (L r μ birth t F I Components : Fin n)
    (env : Fin n → ZFSet.{u}) (meet : MeetOrderCode (env L) (env r) (env μ)) :
    Truth (componentSeparationFormula L r μ birth t F I Components) env ↔
      ComponentSeparationCode (env L) (env r) (env μ) (env birth)
        (env t) (env F) (env I) (env Components) := by
  simp only [componentSeparationFormula, Truth, truth_imp, truth_pairMembershipFormula]
  constructor
  · intro property x hx y hy i hi j hj first second different
    exact (truth_oldBridgeFormula L.succ.succ.succ.succ r.succ.succ.succ.succ
      μ.succ.succ.succ.succ birth.succ.succ.succ.succ t.succ.succ.succ.succ 3 2
      (extend j (extend i (extend y (extend x env)))) meet).1
      (property x hx y hy i hi j hj ⟨first, second, different⟩)
  · intro code x hx y hy i hi j hj condition
    exact (truth_oldBridgeFormula L.succ.succ.succ.succ r.succ.succ.succ.succ
      μ.succ.succ.succ.succ birth.succ.succ.succ.succ t.succ.succ.succ.succ 3 2
      (extend j (extend i (extend y (extend x env)))) meet).2
      (code x hx y hy i hi j hj condition.1 condition.2.1 condition.2.2)

def separatedLayerFormula {n}
    (Qs rs μs L r μ birth t I Indices Maps W Components F QB RB MB : Fin n) :
    BoundedFormula n :=
  .conj (functionFormula I t Indices)
    (.conj (functionFormula I W Maps)
      (.conj (layerBirthFiberFormula F L birth t)
        (.conj (functionFormula F I Components)
          (.conj (copyEmbeddingFamilyFormula Qs rs μs L r μ t I Indices Maps W QB RB MB)
            (.conj (componentImageCoverFormula Qs L t I Components Indices Maps W QB)
              (componentSeparationFormula L r μ birth t F I Components))))))

theorem truth_separatedLayerFormula {n}
    (Qs rs μs L r μ birth t I Indices Maps W Components F QB RB MB : Fin n)
    (env : Fin n → ZFSet.{u})
    (meet : MeetOrderCode (env L) (env r) (env μ))
    (eqQ : env QB = ⋃₀ ⋃₀ env Qs) (eqR : env RB = ⋃₀ ⋃₀ env rs)
    (eqM : env MB = ⋃₀ ⋃₀ env μs) :
    Truth (separatedLayerFormula Qs rs μs L r μ birth t I Indices Maps W Components F QB RB MB) env ↔
      SeparatedLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ)
        (env birth) (env t) (env I) (env Indices) (env Maps) (env W) (env Components) (env F) := by
  simp only [separatedLayerFormula, Truth, truth_functionFormula, truth_layerBirthFiberFormula]
  constructor
  · rintro ⟨indices, maps, fiber, components, embeddings, cover, separated⟩
    exact ⟨indices, maps, fiber, components,
      (truth_copyEmbeddingFamilyFormula _ _ _ _ _ _ _ _ _ _ _ _ _ _ env maps eqQ eqR eqM).1 embeddings,
      (truth_componentImageCoverFormula _ _ _ _ _ _ _ _ _ env maps eqQ).1 cover,
      (truth_componentSeparationFormula _ _ _ _ _ _ _ _ env meet).1 separated⟩
  · intro code
    exact ⟨code.indices, code.maps, code.fiber, code.components,
      (truth_copyEmbeddingFamilyFormula _ _ _ _ _ _ _ _ _ _ _ _ _ _ env code.maps eqQ eqR eqM).2 code.embedding,
      (truth_componentImageCoverFormula _ _ _ _ _ _ _ _ _ env code.maps eqQ).2 code.cover,
      (truth_componentSeparationFormula _ _ _ _ _ _ _ _ env meet).2 code.separated⟩

theorem realize_separatedLayerFormula (M : TransitiveGround.{u}) {n}
    (Qs rs μs L r μ birth t I Indices Maps W Components F QB RB MB : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meet : MeetOrderCode (env L) (env r) (env μ))
    (eqQ : env QB = ⋃₀ ⋃₀ env Qs) (eqR : env RB = ⋃₀ ⋃₀ env rs)
    (eqM : env MB = ⋃₀ ⋃₀ env μs) :
    Realize M.sets
      (separatedLayerFormula Qs rs μs L r μ birth t I Indices Maps W Components F QB RB MB).toFormula env ↔
      SeparatedLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ)
        (env birth) (env t) (env I) (env Indices) (env Maps) (env W) (env Components) (env F) :=
  (realize_toFormula M _ env members).trans
    (truth_separatedLayerFormula Qs rs μs L r μ birth t I Indices Maps W Components F QB RB MB
      env meet eqQ eqR eqM)

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def countableLayerWitness (D injection : ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 2 (Fin.cases (natSetCode 0) (Fin.cases D (fun _ => injection)))

noncomputable def copyLayerWitness (I parts Indices Maps W injection : ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 6 (Fin.cases (natSetCode 1) (Fin.cases I (Fin.cases parts
    (Fin.cases Indices (Fin.cases Maps (Fin.cases W (fun _ => injection)))))))

noncomputable def separatedLayerWitness (I Indices Maps W Components F : ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 6 (Fin.cases (natSetCode 2) (Fin.cases I (Fin.cases Indices
    (Fin.cases Maps (Fin.cases W (Fin.cases Components (fun _ => F)))))))

def GrowthLayerWitnessCode (Qs rs μs L r μ birth t N z : ZFSet.{u}) : Prop :=
  (∃ D injection, z = countableLayerWitness D injection ∧ CountableLayerCode L birth t D N injection) ∨
  (∃ I parts Indices Maps W injection, z = copyLayerWitness I parts Indices Maps W injection ∧
    CopyLayerCode Qs rs μs L r μ birth t I parts Indices Maps W N injection) ∨
  (∃ I Indices Maps W Components F, z = separatedLayerWitness I Indices Maps W Components F ∧
    SeparatedLayerCode Qs rs μs L r μ birth t I Indices Maps W Components F)

namespace GrowthLayerWitnessCode

noncomputable def toLayer {M : TransitiveGround.{u}}
    {Qs rs μs L r μ birth t N z : ZFSet.{u}}
    (code : GrowthLayerWitnessCode Qs rs μs L r μ birth t N z) (ground : z ∈ M.sets)
    (Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}) (omega : N = ZFSet.omega)
    (history : ∀ s ∈ t, ZFSet.pair s (Space s) ∈ Qs ∧
      ZFSet.pair s (sourceOrder s) ∈ rs ∧ ZFSet.pair s (sourceMeet s) ∈ μs) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t := by
  apply Classical.choice
  rcases code with ⟨D, injection, rfl, code⟩ |
    ⟨I, parts, Indices, Maps, W, injection, rfl, code⟩ |
    ⟨I, Indices, Maps, W, Components, F, rfl, code⟩
  · have fields := M.nonemptyTupleCode_field_mem 2 _ ground
    exact ⟨code.toLayer Space sourceOrder sourceMeet (fields 1) (fields 2) omega⟩
  · have fields := M.nonemptyTupleCode_field_mem 6 _ ground
    exact ⟨code.toLayer Space sourceOrder sourceMeet (fields 1) (fields 2) (fields 4)
      (fields 6) omega history⟩
  · have fields := M.nonemptyTupleCode_field_mem 6 _ ground
    exact ⟨code.toGrowthLayer (fields 3) Space sourceOrder sourceMeet history⟩
end GrowthLayerWitnessCode

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem countableLayerWitness_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {D injection : ZFSet.{u}} (hD : D ∈ M.sets) (hInjection : injection ∈ M.sets) :
    countableLayerWitness D injection ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 2 _
    (Fin.cases (M.empty_mem ⟨D, hD⟩) (Fin.cases hD (fun _ => hInjection)))

theorem copyLayerWitness_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {I parts Indices Maps W injection : ZFSet.{u}}
    (hI : I ∈ M.sets) (hParts : parts ∈ M.sets) (hIndices : Indices ∈ M.sets)
    (hMaps : Maps ∈ M.sets) (hW : W ∈ M.sets) (hInjection : injection ∈ M.sets) :
    copyLayerWitness I parts Indices Maps W injection ∈ M.sets := by
  have zero := M.empty_mem ⟨I, hI⟩
  have one : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions zero zero
  exact M.nonemptyTupleCode_mem pairing 6 _
    (Fin.cases one (Fin.cases hI (Fin.cases hParts (Fin.cases hIndices
      (Fin.cases hMaps (Fin.cases hW (fun _ => hInjection)))))))

theorem separatedLayerWitness_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {I Indices Maps W Components F : ZFSet.{u}}
    (hI : I ∈ M.sets) (hIndices : Indices ∈ M.sets) (hMaps : Maps ∈ M.sets)
    (hW : W ∈ M.sets) (hComponents : Components ∈ M.sets) (hF : F ∈ M.sets) :
    separatedLayerWitness I Indices Maps W Components F ∈ M.sets := by
  have zero := M.empty_mem ⟨I, hI⟩
  have one : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions zero zero
  have two : natSetCode 2 ∈ M.sets := M.insert_mem pairing unions one one
  exact M.nonemptyTupleCode_mem pairing 6 _
    (Fin.cases two (Fin.cases hI (Fin.cases hIndices (Fin.cases hMaps
      (Fin.cases hW (Fin.cases hComponents (fun _ => hF)))))))
end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def growthTagFormula : (k : Nat) → {n : Nat} → Fin n → BoundedFormula n
  | 0, _, z => emptyFormula z
  | k + 1, _, z => exMem z (.conj (successorFormula z.succ 0) (growthTagFormula k 0))

theorem truth_growthTagFormula (k : Nat) {n} (z : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (growthTagFormula k z) env ↔ env z = natSetCode k := by
  induction k generalizing n with
  | zero => exact truth_emptyFormula z env
  | succ k ih =>
    simp only [growthTagFormula, truth_exMem, Truth, truth_successorFormula, ih]
    change (∃ x ∈ env z, env z = insert x x ∧ x = natSetCode k) ↔ _
    constructor
    · rintro ⟨x, _, equal, rfl⟩
      exact equal
    · intro equal
      exact ⟨natSetCode k, equal.symm ▸ (show natSetCode k ∈ natSetCode (k + 1) from by
        rw [natSetCode_succ]; exact ZFSet.mem_insert _ _), equal, rfl⟩

def countableTaggedLayerFormula {n} (z tag D injection L birth t N : Fin n) : BoundedFormula n :=
  .conj (growthTagFormula 0 tag)
    (.conj (nonemptyTupleFormula 2 z (Fin.cases tag (Fin.cases D (fun _ => injection))))
      (countableLayerFormula L birth t D N injection))

theorem truth_countableTaggedLayerFormula {n} (z tag D injection L birth t N : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (countableTaggedLayerFormula z tag D injection L birth t N) env ↔
      env tag = natSetCode 0 ∧ env z = countableLayerWitness (env D) (env injection) ∧
        CountableLayerCode (env L) (env birth) (env t) (env D) (env N) (env injection) := by
  simp only [countableTaggedLayerFormula, Truth, truth_growthTagFormula,
    truth_nonemptyTupleFormula, truth_countableLayerFormula]
  constructor
  · rintro ⟨tagged, tuple, code⟩
    refine ⟨tagged, ?_, code⟩
    simpa only [countableLayerWitness, nonemptyTupleCode, Fin.cases_zero, Fin.cases_succ, tagged] using tuple
  · rintro ⟨tagged, tuple, code⟩
    refine ⟨tagged, ?_, code⟩
    simpa only [countableLayerWitness, nonemptyTupleCode, Fin.cases_zero, Fin.cases_succ, tagged] using tuple

def copyTaggedLayerFormula {n}
    (z tag I parts Indices Maps W injection Qs rs μs L r μ birth t N QB RB MB : Fin n) :
    BoundedFormula n :=
  .conj (growthTagFormula 1 tag)
    (.conj (nonemptyTupleFormula 6 z (Fin.cases tag (Fin.cases I (Fin.cases parts
      (Fin.cases Indices (Fin.cases Maps (Fin.cases W (fun _ => injection))))))))
      (copyLayerFormula Qs rs μs L r μ birth t I parts Indices Maps W N injection QB RB MB))

theorem truth_copyTaggedLayerFormula {n}
    (z tag I parts Indices Maps W injection Qs rs μs L r μ birth t N QB RB MB : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (copyTaggedLayerFormula z tag I parts Indices Maps W injection Qs rs μs L r μ birth t N QB RB MB) env ↔
      env tag = natSetCode 1 ∧ env z = copyLayerWitness (env I) (env parts) (env Indices)
        (env Maps) (env W) (env injection) ∧
      env QB = ⋃₀ ⋃₀ env Qs ∧ env RB = ⋃₀ ⋃₀ env rs ∧ env MB = ⋃₀ ⋃₀ env μs ∧
      CopyLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ) (env birth)
        (env t) (env I) (env parts) (env Indices) (env Maps) (env W) (env N) (env injection) := by
  simp only [copyTaggedLayerFormula, Truth, truth_growthTagFormula,
    truth_nonemptyTupleFormula, truth_copyLayerFormula]
  constructor
  · rintro ⟨tagged, tuple, rest⟩
    refine ⟨tagged, ?_, rest⟩
    simpa only [copyLayerWitness, nonemptyTupleCode, Fin.cases_zero, Fin.cases_succ, tagged] using tuple
  · rintro ⟨tagged, tuple, rest⟩
    refine ⟨tagged, ?_, rest⟩
    simpa only [copyLayerWitness, nonemptyTupleCode, Fin.cases_zero, Fin.cases_succ, tagged] using tuple

def separatedTaggedLayerFormula {n}
    (z tag I Indices Maps W Components F Qs rs μs L r μ birth t QB RB MB : Fin n) :
    BoundedFormula n :=
  .conj (growthTagFormula 2 tag)
    (.conj (nonemptyTupleFormula 6 z (Fin.cases tag (Fin.cases I (Fin.cases Indices
      (Fin.cases Maps (Fin.cases W (Fin.cases Components (fun _ => F))))))))
      (.conj (doubleUnionEquationFormula QB Qs)
        (.conj (doubleUnionEquationFormula RB rs)
          (.conj (doubleUnionEquationFormula MB μs)
            (separatedLayerFormula Qs rs μs L r μ birth t I Indices Maps W Components F QB RB MB)))))

theorem truth_separatedTaggedLayerFormula {n}
    (z tag I Indices Maps W Components F Qs rs μs L r μ birth t QB RB MB : Fin n)
    (env : Fin n → ZFSet.{u}) (meet : MeetOrderCode (env L) (env r) (env μ)) :
    Truth (separatedTaggedLayerFormula z tag I Indices Maps W Components F Qs rs μs L r μ birth t QB RB MB) env ↔
      env tag = natSetCode 2 ∧ env z = separatedLayerWitness (env I) (env Indices)
        (env Maps) (env W) (env Components) (env F) ∧
      env QB = ⋃₀ ⋃₀ env Qs ∧ env RB = ⋃₀ ⋃₀ env rs ∧ env MB = ⋃₀ ⋃₀ env μs ∧
      SeparatedLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ) (env birth)
        (env t) (env I) (env Indices) (env Maps) (env W) (env Components) (env F) := by
  simp only [separatedTaggedLayerFormula, Truth, truth_growthTagFormula,
    truth_nonemptyTupleFormula, truth_doubleUnionEquationFormula]
  constructor
  · rintro ⟨tagged, tuple, eqQ, eqR, eqM, recognized⟩
    refine ⟨tagged, ?_, eqQ, eqR, eqM, ?_⟩
    · simpa only [separatedLayerWitness, nonemptyTupleCode, Fin.cases_zero, Fin.cases_succ, tagged] using tuple
    · exact (truth_separatedLayerFormula Qs rs μs L r μ birth t I Indices Maps W Components F QB RB MB
        env meet eqQ eqR eqM).1 recognized
  · rintro ⟨tagged, tuple, eqQ, eqR, eqM, code⟩
    refine ⟨tagged, ?_, eqQ, eqR, eqM, ?_⟩
    · simpa only [separatedLayerWitness, nonemptyTupleCode, Fin.cases_zero, Fin.cases_succ, tagged] using tuple
    · exact (truth_separatedLayerFormula Qs rs μs L r μ birth t I Indices Maps W Components F QB RB MB
        env meet eqQ eqR eqM).2 code

end PartitionPilot.Forcing.BoundedFormula

end OAI
