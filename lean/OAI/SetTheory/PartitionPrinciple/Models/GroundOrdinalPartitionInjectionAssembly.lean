import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCountableFunctionClosure

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula
def definableRelationEntryFormula {n} (φ : SetFormula (n + 2)) : SetFormula (n + 3) :=
  ex (.conj (.mem 0 2) (ex (.conj (.mem 0 4)
    (.conj (BoundedFormula.orderedPairFormula 2 1 0).toFormula
      (binaryApplication φ (fun i => i.succ.succ.succ.succ.succ) 1 0)))))
end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def definableRelation {n} (φ : SetFormula (n + 2))
    (params : Fin n → ZFSet.{u}) (A B : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ A, ∃ y ∈ B, z = ZFSet.pair x y ∧
    Realize M.sets φ (extend x (extend y params))) (ZFSet.prod A B)

theorem pair_mem_definableRelation {n} (φ : SetFormula (n + 2))
    (params : Fin n → ZFSet.{u}) (A B x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ M.definableRelation φ params A B ↔
      x ∈ A ∧ y ∈ B ∧ Realize M.sets φ (extend x (extend y params)) := by
  rw [definableRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, a, ha, b, hb, equal, relation⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ha, hb, relation⟩
  · rintro ⟨hx, hy, relation⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, x, hx, y, hy, rfl, relation⟩

theorem realize_definableRelationEntryFormula {n} (φ : SetFormula (n + 2))
    (params : Fin n → ZFSet.{u}) (members : ∀ i, params i ∈ M.sets)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets (definableRelationEntryFormula φ) (extend z (extend A (extend B params))) ↔
      ∃ x ∈ A, ∃ y ∈ B, z = ZFSet.pair x y ∧ Realize M.sets φ (extend x (extend y params)) := by
  simp only [definableRelationEntryFormula, realize_ex, Realize]
  constructor
  · rintro ⟨x, hx, inA, y, hy, inB, pair, relation⟩
    have ground : ∀ i, (extend y (extend x (extend z (extend A (extend B params))))) i ∈ M.sets :=
      Fin.cases hy (Fin.cases hx (Fin.cases hz (Fin.cases hA (Fin.cases hB members))))
    have exactPair := (BoundedFormula.truth_orderedPairFormula 2 1 0 _).1
      ((BoundedFormula.realize_toFormula M _ _ ground).1 pair)
    exact ⟨x, inA, y, inB, exactPair, (realize_binaryApplication M.sets φ _ _ _ _).1 relation⟩
  · rintro ⟨x, hx, y, hy, pair, relation⟩
    have hxM := M.transitive hA hx
    have hyM := M.transitive hB hy
    have ground : ∀ i, (extend y (extend x (extend z (extend A (extend B params))))) i ∈ M.sets :=
      Fin.cases hyM (Fin.cases hxM (Fin.cases hz (Fin.cases hA (Fin.cases hB members))))
    exact ⟨x, hxM, hx, y, hyM, hy,
      (BoundedFormula.realize_toFormula M _ _ ground).2
        ((BoundedFormula.truth_orderedPairFormula 2 1 0 _).2 pair),
      (realize_binaryApplication M.sets φ _ _ _ _).2 relation⟩

theorem definableRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {n} (φ : SetFormula (n + 2)) (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) :
    M.definableRelation φ params A B ∈ M.sets := by
  have hProd := M.prod_mem pairing unions powers separation hA hB
  have selected := M.separation_mem separation (definableRelationEntryFormula φ)
    (extend A (extend B params)) (Fin.cases hA (Fin.cases hB members)) hProd
  have equal : ZFSet.sep (fun z => Realize M.sets (definableRelationEntryFormula φ)
      (extend z (extend A (extend B params)))) (ZFSet.prod A B) = M.definableRelation φ params A B := by
    apply ZFSet.ext
    intro z
    rw [definableRelation, ZFSet.mem_sep, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    exact M.realize_definableRelationEntryFormula φ params members hA hB z (M.transitive hProd hz)
  exact equal ▸ selected

theorem choose_definable_relation
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {n} (φ : SetFormula (n + 2)) (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {A : ZFSet.{u}} (hA : A ∈ M.sets)
    (total : ∀ x ∈ A, ∃ y ∈ M.sets, Realize M.sets φ (extend x (extend y params))) :
    ∃ B ∈ M.sets, ∃ f ∈ M.sets, ZFSet.IsFunc A B f ∧
      ∀ x y, ZFSet.pair x y ∈ f → Realize M.sets φ (extend x (extend y params)) := by
  obtain ⟨B, hB, bounded⟩ := M.collection_witness collection φ params members hA total
  obtain ⟨f, hf, function, subset⟩ := M.uniformize_relation pairing unions powers separation choice
    hA hB (M.definableRelation_mem pairing unions powers separation φ params members hA hB) (by
      intro x hx
      obtain ⟨y, hy, recognized⟩ := bounded x hx
      exact ⟨y, hy, (M.pair_mem_definableRelation φ params A B x y).2 ⟨hx, hy, recognized⟩⟩)
  exact ⟨B, hB, f, hf, function, fun x y entry =>
    ((M.pair_mem_definableRelation φ params A B x y).1 (subset entry)).2.2⟩

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem exists_groundNameSupportChoice
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (W : ZFSet.{u}) (hW : W ∈ M.sets) (valid : ∀ z ∈ W, IsName s z)
    (symmetric : ∀ tau : Name s, tau.val ∈ W →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) tau) :
    ∃ f ∈ M.sets, ZFSet.IsFunc W b.carrier f ∧
      ∀ (tau : Name s) (D : L), ZFSet.pair tau.val (b.encode D) ∈ f →
        tau.val ∈ W ∧ d.principalFix D ≤ a.stabilizer s tau := by
  let params := extend s.carrier (extend t.carrier (extend (supportBasisCode b t d.principalFix)
    (extend (a.conditionMapFamily s t) Fin.elim0)))
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases carrier (Fin.cases group (Fin.cases supports (Fin.cases maps (fun j => Fin.elim0 j))))
  let relation := M.definableRelation nameSupportFormula params W b.carrier
  have ground : relation ∈ M.sets :=
    M.definableRelation_mem pairing unions powers separation nameSupportFormula params members hW nodes
  have meaning (tau : Name s) (member : tau.val ∈ W) (D : L) :
      Realize M.sets nameSupportFormula (extend tau.val (extend (b.encode D) params)) ↔
        d.principalFix D ≤ a.stabilizer s tau :=
    M.realize_nameSupportFormula a s t b d.principalFix pairing unions powers separation collection
      carrier group supports maps D (M.transitive nodes (b.encode_mem D)) tau (M.transitive hW member)
  have total : ∀ z ∈ W, ∃ v ∈ b.carrier, ZFSet.pair z v ∈ relation := by
    intro z member
    let tau : Name s := ⟨z, valid z member⟩
    obtain ⟨D, supported⟩ := (symmetric tau member).symmetric
    exact ⟨b.encode D, b.encode_mem D,
      (M.pair_mem_definableRelation nameSupportFormula params W b.carrier z (b.encode D)).2
        ⟨member, b.encode_mem D, (meaning tau member D).2 supported⟩⟩
  obtain ⟨f, hf, function, selected⟩ := M.uniformize_relation pairing unions powers separation choice
    hW nodes ground total
  refine ⟨f, hf, function, ?_⟩
  intro tau D entry
  have chosen := (M.pair_mem_definableRelation nameSupportFormula params W b.carrier
    tau.val (b.encode D)).1 (selected entry)
  exact ⟨chosen.1, (meaning tau chosen.1 D).1 chosen.2.2⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace BoundedFormula
private def coveringPositionFormula : BoundedFormula 5 :=
  disj (.conj (emptyFormula 1) (.allMem 2 (.neg (pairMembershipFormula 0 1 4))))
    (.conj (functionFormula 4 2 1)
      (.conj (.allMem 4 (.allMem 3
        (imp (pairMembershipFormula 1 0 3) (pairMembershipFormula 0 2 5))))
        (.allMem 2 (imp (pairMembershipFormula 0 1 4)
          (exMem 5 (pairMembershipFormula 0 1 3))))))

private theorem coveringPosition_meaning (D f I r mu : ZFSet.{u}) :
    Truth coveringPositionFormula ![D, f, I, r, mu] ↔
      (f = ∅ ∧ ∀ v ∈ I, ¬ ZFSet.pair v D ∈ r) ∨
      (ZFSet.IsFunc mu I f ∧ (∀ i v, ZFSet.pair i v ∈ f → ZFSet.pair v D ∈ r) ∧
        ∀ v ∈ I, ZFSet.pair v D ∈ r → ∃ i ∈ mu, ZFSet.pair i v ∈ f) := by
  simp only [coveringPositionFormula, truth_disj, Truth, truth_emptyFormula,
    truth_functionFormula, truth_imp, truth_pairMembershipFormula, truth_exMem]
  change (f = ∅ ∧ ∀ v ∈ I, ¬ ZFSet.pair v D ∈ r) ∨
    (ZFSet.IsFunc mu I f ∧ (∀ i ∈ mu, ∀ v ∈ I, ZFSet.pair i v ∈ f → ZFSet.pair v D ∈ r) ∧
      ∀ v ∈ I, ZFSet.pair v D ∈ r → ∃ i ∈ mu, ZFSet.pair i v ∈ f) ↔ _
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨function, bounds, onto⟩
    exact ⟨function, fun i v entry => bounds i (ZFSet.pair_mem_prod.1 (function.1 entry)).1
      v (ZFSet.pair_mem_prod.1 (function.1 entry)).2 entry, onto⟩
  · rintro ⟨function, bounds, onto⟩
    exact ⟨function, fun i _ v _ entry => bounds i v entry, onto⟩
end BoundedFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u}) {L : Type u} [PartialOrder L] [OrderBot L]
variable (b : Presentation L)

theorem exists_groundCoveringRowPositions
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (nodes : b.carrier ∈ M.sets) (order : b.conditionOrder ∈ M.sets)
    (mu : ZFSet.{u}) (hmu : mu ∈ M.sets) (ordinal : ordinalSetProperty mu)
    (small : M.groundEmbeddable b.nonbottom.carrier mu) :
    let S := M.rowPositionSequences b.carrier b.conditionOrder b.nonbottom.carrier mu
    ∃ selected ∈ M.sets, ZFSet.IsFunc b.carrier S selected ∧
      ∀ (D : L) f, ZFSet.pair (b.encode D) f ∈ selected →
        f ∈ S ∧ ∃ delta, (delta = ∅ ∨ delta = mu) ∧ FunctionGraphOn delta f ∧
          (∀ i v, ZFSet.pair i v ∈ f → v ∈ b.nonbottom.carrier ∧ ZFSet.pair v (b.encode D) ∈ b.conditionOrder) ∧
          ∀ v : L, v ≠ ⊥ → v ≤ D → ∃ i ∈ delta, ZFSet.pair i (b.encode v) ∈ f := by
  intro S
  have hI := M.nonbottom_carrier_mem b separation nodes
  have hS := M.rowPositionSequences_mem pairing unions powers separation nodes order hI hmu
  let params := extend b.nonbottom.carrier (extend b.conditionOrder (extend mu Fin.elim0))
  have members : ∀ j, params j ∈ M.sets := Fin.cases hI (Fin.cases order (Fin.cases hmu (fun j => Fin.elim0 j)))
  let formula := BoundedFormula.coveringPositionFormula.toFormula
  let relation := M.definableRelation formula params b.carrier S
  have hRelation := M.definableRelation_mem pairing unions powers separation formula params members nodes hS
  have meaning (D f : ZFSet.{u}) (hD : D ∈ M.sets) (hf : f ∈ M.sets) :
      Realize M.sets formula (extend D (extend f params)) ↔
      (f = ∅ ∧ ∀ v ∈ b.nonbottom.carrier, ¬ ZFSet.pair v D ∈ b.conditionOrder) ∨
      (ZFSet.IsFunc mu b.nonbottom.carrier f ∧
        (∀ i v, ZFSet.pair i v ∈ f → ZFSet.pair v D ∈ b.conditionOrder) ∧
        ∀ v ∈ b.nonbottom.carrier, ZFSet.pair v D ∈ b.conditionOrder →
          ∃ i ∈ mu, ZFSet.pair i v ∈ f) := by
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hD (Fin.cases hf members))]
    exact BoundedFormula.coveringPosition_meaning D f b.nonbottom.carrier b.conditionOrder mu
  have total : ∀ D ∈ b.carrier, ∃ f ∈ S, ZFSet.pair D f ∈ relation := by
    intro D hD
    let ideal := ZFSet.sep (fun v => ZFSet.pair v D ∈ b.conditionOrder) b.nonbottom.carrier
    have hDM := M.transitive nodes hD
    have hIdeal : ideal ∈ M.sets := by
      have selected := M.bounded_separation_mem separation
        (BoundedFormula.pairMembershipFormula 0 1 2) (extend D (extend b.conditionOrder Fin.elim0))
        (Fin.cases hDM (Fin.cases order (fun j => Fin.elim0 j))) hI
      simp only [BoundedFormula.truth_pairMembershipFormula] at selected
      exact selected
    by_cases inhabited : ideal.Nonempty
    · have idealSmall : M.groundEmbeddable ideal mu := by
        obtain ⟨f, hf, inject⟩ := small
        exact ⟨ZFSet.sep (fun z => z ∈ ZFSet.prod ideal mu) f,
          M.injection_restriction_mem separation hIdeal hmu hf,
          inject.restrict (fun _ h => (ZFSet.mem_sep.1 h).1)⟩
      obtain ⟨f, hf, function, onto⟩ := M.groundEmbeddable_enumeration pairing unions powers separation hIdeal hmu inhabited idealSmall
      have retarget : ZFSet.IsFunc mu b.nonbottom.carrier f :=
        ⟨fun z hz => by
          obtain ⟨i, hi, v, hv, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
          exact ZFSet.pair_mem_prod.2 ⟨hi, (ZFSet.mem_sep.1 hv).1⟩, function.2⟩
      have bounds : ∀ i v, ZFSet.pair i v ∈ f → ZFSet.pair v D ∈ b.conditionOrder :=
        fun _ _ h => (ZFSet.mem_sep.1 (ZFSet.pair_mem_prod.1 (function.1 h)).2).2
      have code : RowPositionSequenceCode b.carrier b.conditionOrder b.nonbottom.carrier mu f :=
        ⟨mu, ZFSet.mem_insert _ _, retarget, D, hD, bounds⟩
      have inS := (M.mem_rowPositionSequences ordinal).2 ⟨hf, code⟩
      exact ⟨f, inS, (M.pair_mem_definableRelation formula params b.carrier S D f).2
        ⟨hD, inS, (meaning D f hDM hf).2 (Or.inr ⟨retarget, bounds,
          fun v hv below => onto v (ZFSet.mem_sep.2 ⟨hv, below⟩)⟩)⟩⟩
    · have empty := M.empty_mem ⟨b.carrier, nodes⟩
      have inS : (∅ : ZFSet.{u}) ∈ S := M.empty_mem_rowPositionSequences hmu ordinal ⟨D, hD⟩
      exact ⟨∅, inS, (M.pair_mem_definableRelation formula params b.carrier S D ∅).2
        ⟨hD, inS, (meaning D ∅ hDM empty).2 (Or.inl ⟨rfl,
          fun v hv below => inhabited ⟨v, ZFSet.mem_sep.2 ⟨hv, below⟩⟩⟩)⟩⟩
  obtain ⟨selected, hSelected, function, included⟩ := M.uniformize_relation pairing unions powers separation choice
    nodes hS hRelation total
  refine ⟨selected, hSelected, function, ?_⟩
  intro D f entry
  have chosen := (M.pair_mem_definableRelation formula params b.carrier S (b.encode D) f).1 (included entry)
  refine ⟨chosen.2.1, ?_⟩
  have truth := (meaning (b.encode D) f (M.transitive nodes (b.encode_mem D))
    (M.transitive hS chosen.2.1)).1 chosen.2.2
  have nonbottom (v : L) (h : v ≠ ⊥) : b.encode v ∈ b.nonbottom.carrier :=
    (b.nonbottom.mem_carrier _).2 ⟨⟨v, h⟩, rfl⟩
  rcases truth with ⟨rfl, none⟩ | ⟨func, bounds, onto⟩
  · exact ⟨∅, Or.inl rfl, FunctionGraphOn.empty,
      fun i v entry => (ZFSet.notMem_empty _ entry).elim,
      fun v hv below => (none _ (nonbottom v hv) ((b.pair_mem_conditionOrder v D).2 below)).elim⟩
  · exact ⟨mu, Or.inr rfl, ⟨b.nonbottom.carrier, func⟩,
      fun i v entry => ⟨(ZFSet.pair_mem_prod.1 (func.1 entry)).2, bounds i v entry⟩,
      fun v hv below => onto _ (nonbottom v hv) ((b.pair_mem_conditionOrder v D).2 below)⟩

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (N : TransitiveGround.{u})

theorem indexedInjectionCandidates
    (zf : ZFRealization N.sets) {delta Y X p q : ZFSet.{u}}
    (hDelta : delta ∈ N.sets) (hY : Y ∈ N.sets) (hX : X ∈ N.sets)
    (hp : p ∈ N.sets) (hq : q ∈ N.sets)
    (pFunction : FunctionGraphOn delta p) (qFunction : FunctionGraphOn delta q)
    (bounds : ∀ i U V, ZFSet.pair i U ∈ p → ZFSet.pair i V ∈ q → U ⊆ Y ∧ V ⊆ X)
    (possible : ∀ i ∈ delta, ∀ U V, ZFSet.pair i U ∈ p → ZFSet.pair i V ∈ q →
      N.groundEmbeddable U V) :
    ∃ J ∈ N.sets, FunctionGraphOn delta J ∧
      (∀ i S, ZFSet.pair i S ∈ J → S.Nonempty) ∧
      ∀ i S U V f, ZFSet.pair i S ∈ J → ZFSet.pair i U ∈ p →
        ZFSet.pair i V ∈ q → (f ∈ S ↔ f ∈ N.sets ∧ InjectionCode U V f) := by
  have pairing : Realize N.sets SetFormula.pairing Fin.elim0 := zf.1.2.2.2.1
  have unions : Realize N.sets SetFormula.union Fin.elim0 := zf.1.2.2.2.2.1
  have powers : Realize N.sets powerSet Fin.elim0 := zf.1.2.2.2.2.2.1
  have separation : SeparationSchema N.sets := zf.2.1
  let PB := ⋃₀ ⋃₀ p
  let QB := ⋃₀ ⋃₀ q
  let W := N.groundRelations Y X
  have hPB : PB ∈ N.sets := N.union_mem unions (N.union_mem unions hp)
  have hQB : QB ∈ N.sets := N.union_mem unions (N.union_mem unions hq)
  have hW : W ∈ N.sets := N.groundRelations_mem pairing unions powers separation hY hX
  let params := extend p (extend q (extend PB (extend QB Fin.elim0)))
  have members : ∀ j, params j ∈ N.sets :=
    Fin.cases hp (Fin.cases hq (Fin.cases hPB (Fin.cases hQB (fun j => Fin.elim0 j))))
  let phi : BoundedFormula 6 := BoundedFormula.exMem 4 (BoundedFormula.exMem 6
    (.conj (BoundedFormula.pairMembershipFormula 2 1 4)
      (.conj (BoundedFormula.pairMembershipFormula 2 0 5)
        (BoundedFormula.injectionFormula 1 0 3))))
  let R := N.definableRelation phi.toFormula params delta W
  have hR : R ∈ N.sets := N.definableRelation_mem pairing unions powers separation
    phi.toFormula params members hDelta hW
  have meaning (i f : ZFSet.{u}) (hi : i ∈ N.sets) (hf : f ∈ N.sets) :
      Realize N.sets phi.toFormula (extend i (extend f params)) ↔
        ∃ U ∈ PB, ∃ V ∈ QB, ZFSet.pair i U ∈ p ∧ ZFSet.pair i V ∈ q ∧ InjectionCode U V f := by
    rw [BoundedFormula.realize_toFormula N phi _ (Fin.cases hi (Fin.cases hf members))]
    simp only [phi, BoundedFormula.truth_exMem, BoundedFormula.Truth,
      BoundedFormula.truth_pairMembershipFormula, BoundedFormula.truth_injectionFormula]
    rfl
  have entry (i U V f : ZFSet.{u}) (ip : ZFSet.pair i U ∈ p) (iq : ZFSet.pair i V ∈ q) :
      ZFSet.pair i f ∈ R ↔ f ∈ N.sets ∧ InjectionCode U V f := by
    rw [N.pair_mem_definableRelation]
    constructor
    · rintro ⟨hi, hf, raw⟩
      have hfN := N.transitive hW hf
      obtain ⟨U', _hU, V', _hV, ip', iq', code⟩ := (meaning i f (N.transitive hDelta hi) hfN).1 raw
      have sameU := pFunction.unique ip' ip
      have sameV := qFunction.unique iq' iq
      exact ⟨hfN, sameU ▸ sameV ▸ code⟩
    · rintro ⟨hf, code⟩
      have hi := pFunction.pair_source ip
      have bound : f ⊆ ZFSet.prod Y X := by
        intro z hz
        obtain ⟨u, hu, v, hv, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 hz)
        exact ZFSet.pair_mem_prod.2 ⟨(bounds i U V ip iq).1 hu, (bounds i U V ip iq).2 hv⟩
      refine ⟨hi, (N.mem_groundRelations Y X f).2 ⟨hf, bound⟩,
        (meaning i f (N.transitive hDelta hi) hf).2 ?_⟩
      exact ⟨U, pair_second_mem_doubleUnion ip, V, pair_second_mem_doubleUnion iq, ip, iq, code⟩
  let J := N.relationFiberFamily delta W R
  have hJ : J ∈ N.sets := N.relationFiberFamily_mem pairing unions powers separation hDelta hW hR
  have jFunction : FunctionGraphOn delta J :=
    ⟨_, N.relationFiberFamily_function separation hDelta hW hR⟩
  have exactCandidate (i S U V f : ZFSet.{u}) (j : ZFSet.pair i S ∈ J)
      (ip : ZFSet.pair i U ∈ p) (iq : ZFSet.pair i V ∈ q) :
      f ∈ S ↔ f ∈ N.sets ∧ InjectionCode U V f := by
    have same := ((N.pair_mem_relationFiberFamily delta W R i S).1 j).2.2
    rw [same, mem_relationFiber]
    constructor
    · intro member
      exact (entry i U V f ip iq).1 member.2
    · intro code
      have edge := (entry i U V f ip iq).2 code
      exact ⟨((N.pair_mem_definableRelation phi.toFormula params delta W i f).1 edge).2.1, edge⟩
  refine ⟨J, hJ, jFunction, ?_, exactCandidate⟩
  intro i S j
  have hi := jFunction.pair_source j
  obtain ⟨U, ip⟩ := pFunction.total hi
  obtain ⟨V, iq⟩ := qFunction.total hi
  obtain ⟨f, hf, code⟩ := possible i hi U V ip iq
  exact ⟨f, (exactCandidate i S U V f j ip iq).2 ⟨hf, code⟩⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (N : TransitiveGround.{u})

theorem ordinalPartition_injection_assembly
    (zf : ZFRealization N.sets)
    (acwo : ∀ delta ∈ N.sets, ordinalSetProperty delta →
      ∀ z ∈ N.sets, FunctionGraphOn delta z →
        (∀ beta A, ZFSet.pair beta A ∈ z → A.Nonempty) →
        ∃ c ∈ N.sets, FunctionGraphOn delta c ∧
          ∀ beta A x, ZFSet.pair beta A ∈ z → ZFSet.pair beta x ∈ c → x ∈ A)
    {delta Y X p q : ZFSet.{u}}
    (hDelta : delta ∈ N.sets) (ordinal : ordinalSetProperty delta)
    (hY : Y ∈ N.sets) (hX : X ∈ N.sets) (hp : p ∈ N.sets) (hq : q ∈ N.sets)
    (pFunction : FunctionGraphOn delta p) (qFunction : FunctionGraphOn delta q)
    (bounds : ∀ i U V, ZFSet.pair i U ∈ p → ZFSet.pair i V ∈ q → U ⊆ Y ∧ V ⊆ X)
    (cover : ∀ y ∈ Y, ∃ i ∈ delta, ∃ U, ZFSet.pair i U ∈ p ∧ y ∈ U)
    (domainDisjoint : ∀ i k U V y, ZFSet.pair i U ∈ p → ZFSet.pair k V ∈ p →
      y ∈ U → y ∈ V → i = k)
    (targetDisjoint : ∀ i k U V x, ZFSet.pair i U ∈ q → ZFSet.pair k V ∈ q →
      x ∈ U → x ∈ V → i = k)
    (possible : ∀ i ∈ delta, ∀ U V, ZFSet.pair i U ∈ p → ZFSet.pair i V ∈ q →
      N.groundEmbeddable U V) :
    N.groundEmbeddable Y X := by
  have unions : Realize N.sets SetFormula.union Fin.elim0 := zf.1.2.2.2.2.1
  obtain ⟨J, hJ, jFunction, nonempty, candidates⟩ :=
    N.indexedInjectionCandidates zf hDelta hY hX hp hq pFunction qFunction bounds possible
  obtain ⟨c, hc, cFunction, chosen⟩ := acwo delta hDelta ordinal J hJ jFunction nonempty
  have codes (i U V f : ZFSet.{u}) (ip : ZFSet.pair i U ∈ p)
      (iq : ZFSet.pair i V ∈ q) (entry : ZFSet.pair i f ∈ c) : InjectionCode U V f := by
    obtain ⟨S, indexed⟩ := jFunction.total (cFunction.pair_source entry)
    exact ((candidates i S U V f indexed ip iq).1 (chosen i S f indexed entry)).2
  let family := relationImage delta (⋃₀ ⋃₀ c) c
  let j := ⋃₀ family
  have hFamily : family ∈ N.sets := N.relationImage_mem zf.2.1 hDelta
    (N.union_mem unions (N.union_mem unions hc)) hc
  have hj : j ∈ N.sets := N.union_mem unions hFamily
  have entries (z : ZFSet.{u}) : z ∈ j ↔
      ∃ i ∈ delta, ∃ f, ZFSet.pair i f ∈ c ∧ z ∈ f := by
    rw [ZFSet.mem_sUnion]
    constructor
    · rintro ⟨f, member, zf⟩
      obtain ⟨_bound, i, hi, edge⟩ := (mem_relationImage delta (⋃₀ ⋃₀ c) c f).1 member
      exact ⟨i, hi, f, edge, zf⟩
    · rintro ⟨i, hi, f, edge, zf⟩
      exact ⟨f, (mem_relationImage delta (⋃₀ ⋃₀ c) c f).2
        ⟨pair_second_mem_doubleUnion edge, i, hi, edge⟩, zf⟩
  have localCode (i : ZFSet.{u}) (hi : i ∈ delta) (f : ZFSet.{u}) (edge : ZFSet.pair i f ∈ c) :
      ∃ U V, ZFSet.pair i U ∈ p ∧ ZFSet.pair i V ∈ q ∧ InjectionCode U V f := by
    obtain ⟨U, ip⟩ := pFunction.total hi
    obtain ⟨V, iq⟩ := qFunction.total hi
    exact ⟨U, V, ip, iq, codes i U V f ip iq edge⟩
  refine ⟨j, hj, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · intro z member
    obtain ⟨i, hi, f, edge, zf⟩ := (entries z).1 member
    obtain ⟨U, V, ip, iq, code⟩ := localCode i hi f edge
    obtain ⟨y, hy, x, hx, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 zf)
    exact ZFSet.pair_mem_prod.2 ⟨(bounds i U V ip iq).1 hy, (bounds i U V ip iq).2 hx⟩
  · intro y hy
    obtain ⟨i, hi, U, ip, yu⟩ := cover y hy
    obtain ⟨V, iq⟩ := qFunction.total hi
    obtain ⟨f, edge⟩ := cFunction.total hi
    have code := codes i U V f ip iq edge
    obtain ⟨x, picked, unique⟩ := code.function.2 y yu
    refine ⟨x, (entries _).2 ⟨i, hi, f, edge, picked⟩, ?_⟩
    intro x' other
    obtain ⟨k, hk, g, otherEdge, otherPicked⟩ := (entries _).1 other
    obtain ⟨U', V', kp, kq, otherCode⟩ := localCode k hk g otherEdge
    have inU' := (ZFSet.pair_mem_prod.1 (otherCode.function.1 otherPicked)).1
    have equalIndex : i = k := domainDisjoint i k U U' y ip kp yu inU'
    subst k
    have equalFunction : g = f := cFunction.unique otherEdge edge
    exact unique x' (equalFunction ▸ otherPicked)
  · intro y y' x first second
    obtain ⟨i, hi, f, edge, picked⟩ := (entries _).1 first
    obtain ⟨k, hk, g, otherEdge, otherPicked⟩ := (entries _).1 second
    obtain ⟨U, V, ip, iq, code⟩ := localCode i hi f edge
    obtain ⟨U', V', kp, kq, otherCode⟩ := localCode k hk g otherEdge
    have inV := (ZFSet.pair_mem_prod.1 (code.function.1 picked)).2
    have inV' := (ZFSet.pair_mem_prod.1 (otherCode.function.1 otherPicked)).2
    have equalIndex : i = k := targetDisjoint i k V V' x iq kq inV inV'
    subst k
    have equalFunction : g = f := cFunction.unique otherEdge edge
    exact code.injective y y' x picked (equalFunction ▸ otherPicked)

end PartitionPilot.Forcing.TransitiveGround

end OAI
