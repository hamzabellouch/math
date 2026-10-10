import OAI.SetTheory.PartitionPrinciple.Definability.GroundLiftedRowTupleProvenance

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.TransitiveGround

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L]

theorem rowPositionSequence_decode (s : Presentation L)
    (hL : s.carrier ∈ M.sets) {mu f : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (ordinal : ordinalSetProperty mu)
    (member : f ∈ M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu) :
    f ∈ M.sets ∧ ∃ δ ∈ M.sets, ordinalSetProperty δ ∧ δ ⊆ mu ∧
      ∃ function : FunctionGraphOn δ f, ∃ positions : δ.toSet → {i : L // i ≠ ⊥},
        ∃ D : L, (∀ i, function.value i = s.encode (positions i).val) ∧
          ∀ i, (positions i).val ≤ D := by
  obtain ⟨hf, δ, hδ, ordδ, subδ, fn, d, hd, _, bounds⟩ :=
    M.rowPositionSequence_data hL hmu ordinal member
  let function : FunctionGraphOn δ f := ⟨s.nonbottom.carrier, fn⟩
  have range (i : δ.toSet) : function.value i ∈ s.nonbottom.carrier :=
    (ZFSet.pair_mem_prod.1 (fn.1 (function.value_entry i))).2
  have each (i : δ.toSet) : ∃ x : {i : L // i ≠ ⊥}, s.encode x.val = function.value i :=
    (s.nonbottom.mem_carrier (function.value i)).1 (range i)
  let positions (i : δ.toSet) : {i : L // i ≠ ⊥} := Classical.choose (each i)
  have values (i : δ.toSet) : function.value i = s.encode (positions i).val :=
    (Classical.choose_spec (each i)).symm
  obtain ⟨D, rfl⟩ := (s.mem_carrier d).1 hd
  refine ⟨hf, δ, hδ, ordδ, subδ, function, positions, D, values, ?_⟩
  intro i
  have bound := bounds i.val (function.value i) (function.value_entry i)
  rw [values i] at bound
  exact (s.pair_mem_conditionOrder (positions i).val D).1 bound

variable [Group G] (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem binaryRowTupleTerms_hs (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (ordinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    ∀ z ∈ rowTupleTerms (SetMembers.raw (⊤ : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))) mu s.nonbottom.carrier
      (⋃₀ ⋃₀ rows) rows S,
      ∃ τ : Name c, τ.val = z ∧ HereditarilySymmetric act c (a.principalSupportFamily ⊥ directed) τ := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  dsimp only
  intro z hz
  obtain ⟨f, hf, rfl⟩ := (mem_rowTupleTerms _ _ _ _ _ _ z).1 hz
  obtain ⟨_, δ, _, _, subset, function, positions, D, values, bounded⟩ :=
    M.rowPositionSequence_decode s hL hmu ordinal hf
  refine ⟨M.internalRowTupleName s C hL δ positions, ?_, ?_⟩
  · exact (M.internalRowTupleCode_eq s C hL function subset positions values).symm
  · exact M.internalRowTupleName_hs a s b C pairing unions powers separation infinite
      hL hC hG graph directed δ positions D bounded

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem binaryRowTupleTerms_action {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (ordinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (SetMembers.raw (⊤ : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))) mu s.nonbottom.carrier
      (⋃₀ ⋃₀ rows) rows S
    ∀ (g : G) (τ : Name c), τ.val ∈ T → (act.act c g τ).val ∈ T := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  dsimp only
  intro g τ member
  obtain ⟨f, hf, equal⟩ := (mem_rowTupleTerms _ _ _ _ _ _ τ.val).1 member
  obtain ⟨_, δ, _, _, subset, function, positions, _, values, _⟩ :=
    M.rowPositionSequence_decode s hL hmu ordinal hf
  have original : ZFSet.IsFunc δ s.nonbottom.carrier f := by
    refine ⟨?_, function.to_isFunc.2⟩
    intro z hz
    obtain ⟨i, hi, y, rfl⟩ := function.shape z hz
    have value := (function.value_eq_of_entry ⟨i, hi⟩ hz).symm.trans (values ⟨i, hi⟩)
    exact ZFSet.pair_mem_prod.2 ⟨hi, value.symm ▸ s.nonbottom.encode_mem (positions ⟨i, hi⟩)⟩
  let moved := rowPositionSequenceAction a s g mu f
  have hmoved := M.rowPositionSequenceAction_mem a s b pairing unions powers separation
    hL hG graph hmu ordinal g hf
  let movedFunction : FunctionGraphOn δ moved :=
    ⟨s.nonbottom.carrier, rowPositionSequenceAction_function a s g subset original⟩
  have movedValues (i : δ.toSet) :
      movedFunction.value i = s.encode (a.nonbottom.iso g (positions i)).val := by
    apply movedFunction.value_eq_of_entry
    apply (pair_mem_rowPositionSequenceAction a s g mu f i.val (positions i)).2
    refine ⟨subset i.property, ?_⟩
    rw [← values i]
    exact function.value_entry i
  have actual : τ = M.internalRowTupleName s C hL δ positions :=
    Subtype.ext (equal.trans (M.internalRowTupleCode_eq s C hL function subset positions values))
  rw [actual, M.internalRowTupleName_action a s b C pairing unions powers separation infinite
    hL hC hG graph]
  apply (mem_rowTupleTerms _ _ _ _ _ _ _).2
  exact ⟨moved, hmoved,
    (M.internalRowTupleCode_eq s C hL movedFunction subset
      (fun i => a.nonbottom.iso g (positions i)) movedValues).symm⟩

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include collection order
theorem binaryRowTermSetName_exists (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (ordinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    T ∈ M.sets ∧ ∃ τ : Name c, τ.val ∈ M.sets ∧ τ.val = ZFSet.prod T {c.encode ⊤} ∧
      HereditarilySymmetric act c (a.principalSupportFamily ⊥ directed) τ ∧
      (∀ g : G, act.act c g τ = τ) ∧
      ∀ (H : Set (SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))), ⊤ ∈ H →
        ∀ x, x ∈ Name.eval H τ ↔ ∃ σ : Name c, σ.val ∈ T ∧ Name.eval H σ = x := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  have hI := M.nonbottom_carrier_mem s separation hL
  have hS : S ∈ M.sets := M.rowPositionSequences_mem pairing unions powers separation hL order hI hmu
  have hfamily := M.binaryRowTupleFamily_mem pairing unions powers separation collection infinite hL order hI hC hmu ⊤
  have hT : T ∈ M.sets := M.rowTupleTerms_mem unions separation hS hfamily
  have each := M.binaryRowTupleTerms_hs a s b C pairing unions powers separation infinite
    hL hC hG graph directed hmu ordinal
  have valid (z : ZFSet.{u}) (hz : z ∈ T) : IsName c z := by
    obtain ⟨σ, eq, _⟩ := each z hz
    exact eq ▸ σ.property
  have children (σ : Name c) (hσ : σ.val ∈ T) :
      HereditarilySymmetric act c (a.principalSupportFamily ⊥ directed) σ := by
    obtain ⟨ν, eq, hs⟩ := each σ.val hσ
    have same : ν = σ := Subtype.ext eq
    exact same ▸ hs
  have closed := M.binaryRowTupleTerms_action a s b C pairing unions powers separation infinite
    hL hC hG graph hmu ordinal
  have hQ := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  refine ⟨hT, Name.familySet ⊤ T valid,
    M.familySet_mem c ⊤ pairing unions powers separation hT (M.transitive hQ (c.encode_mem ⊤)) valid,
    Name.familySet_code ⊤ T valid,
    Name.familySet_hs act (a.principalSupportFamily ⊥ directed) T valid closed children,
    Name.act_familySet act T valid closed, ?_⟩
  intro H hone x
  exact Name.mem_eval_familySet H ⊤ hone T valid x

end

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem binaryRowLiftedTermFamilies_hs (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (ordinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
      let lifted := Name.renamedFamily c.pairEmpty id T valid
      (∀ τ : Name c.pairEmpty, τ.val ∈ lifted →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) τ) ∧
      (∀ τ : Name c.pairEmpty,
        τ.val ∈ orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) τ) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted
  have original : ∀ σ : Name c, σ.val ∈ T →
      HereditarilySymmetric act c (a.principalSupportFamily ⊥ directed) σ := by
    intro σ member
    obtain ⟨τ, equal, hs⟩ := M.binaryRowTupleTerms_hs a s b C pairing unions powers separation
      infinite hL hC hG graph directed hmu ordinal σ.val member
    have same : τ = σ := Subtype.ext equal
    exact same ▸ hs
  have liftedHS := Name.renamedFamily_hs act c.pairEmpty
    (a.principalSupportFamily ⊥ directed) T valid original
  have liftedValid := Name.renamedFamily_valid c.pairEmpty id T valid
  exact ⟨liftedHS, orderedPairNameFamily_hs act (a.principalSupportFamily ⊥ directed)
    liftedValid liftedValid liftedHS liftedHS⟩

theorem binaryRowTupleCode_action {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (ordinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    ∀ (g : G) (f : ZFSet.{u}) (τ : Name c), f ∈ S →
      τ.val = rowTupleCode (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows f →
      rowPositionSequenceAction a s g mu f ∈ S ∧
        (act.act c g τ).val = rowTupleCode (c.encode ⊤) mu s.nonbottom.carrier
          (⋃₀ ⋃₀ rows) rows (rowPositionSequenceAction a s g mu f) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  dsimp only
  intro g f τ hf equal
  obtain ⟨_, δ, _, _, subset, function, positions, _, values, _⟩ :=
    M.rowPositionSequence_decode s hL hmu ordinal hf
  have original : ZFSet.IsFunc δ s.nonbottom.carrier f := by
    refine ⟨?_, function.to_isFunc.2⟩
    intro z hz
    obtain ⟨i, hi, y, rfl⟩ := function.shape z hz
    have value := (function.value_eq_of_entry ⟨i, hi⟩ hz).symm.trans (values ⟨i, hi⟩)
    exact ZFSet.pair_mem_prod.2 ⟨hi, value.symm ▸ s.nonbottom.encode_mem (positions ⟨i, hi⟩)⟩
  let moved := rowPositionSequenceAction a s g mu f
  have hmoved := M.rowPositionSequenceAction_mem a s b pairing unions powers separation
    hL hG graph hmu ordinal g hf
  let movedFunction : FunctionGraphOn δ moved :=
    ⟨s.nonbottom.carrier, rowPositionSequenceAction_function a s g subset original⟩
  have movedValues (i : δ.toSet) :
      movedFunction.value i = s.encode (a.nonbottom.iso g (positions i)).val := by
    apply movedFunction.value_eq_of_entry
    apply (pair_mem_rowPositionSequenceAction a s g mu f i.val (positions i)).2
    refine ⟨subset i.property, ?_⟩
    rw [← values i]
    exact function.value_entry i
  have actual : τ = M.internalRowTupleName s C hL δ positions :=
    Subtype.ext (equal.trans (M.internalRowTupleCode_eq s C hL function subset positions values))
  refine ⟨hmoved, ?_⟩
  rw [actual, M.internalRowTupleName_action a s b C pairing unions powers separation infinite
    hL hC hG graph]
  exact (M.internalRowTupleCode_eq s C hL movedFunction subset
    (fun i => a.nonbottom.iso g (positions i)) movedValues).symm

theorem binaryLiftedRowTupleFamily_action {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (ordinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ (valid : ∀ z ∈ T, IsName c z) (g : G) (f : ZFSet.{u}) (τ : Name c.pairEmpty),
      ZFSet.pair f τ.val ∈ liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier
        (⋃₀ ⋃₀ rows) rows S valid →
      ZFSet.pair (rowPositionSequenceAction a s g mu f) (act.act c.pairEmpty g τ).val ∈
        liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier
          (⋃₀ ⋃₀ rows) rows S valid := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid g f τ entry
  obtain ⟨hf, σ, source, lifted⟩ := (pair_mem_liftedRowTupleFamily c (c.encode ⊤) mu
    s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid f τ.val).1 entry
  have moved := M.binaryRowTupleCode_action a s b C pairing unions powers separation infinite
    hL hC hG graph hmu ordinal g f σ hf source
  have same : τ = Name.presentationEquiv c c.pairEmpty σ := Subtype.ext lifted
  apply (pair_mem_liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier
    (⋃₀ ⋃₀ rows) rows S valid _ _).2
  refine ⟨moved.1, act.act c g σ, moved.2, ?_⟩
  rw [same, act.act_presentationEquiv]
  rfl

end PartitionPilot.Forcing.TransitiveGround

end OAI
