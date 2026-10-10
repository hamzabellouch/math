import OAI.SetTheory.PartitionPrinciple.Forcing.GroundInvariantNamePowers
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRowTermSetNames
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalFulfillmentConstruction
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCountableFunctionOrdinaryZFC
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCountableFunctionSequences

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainFinalGeometry
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (geometry : GroundMainFinalGeometry M C D rD)

theorem decoded_directed
    (directed : ∀ x ∈ geometry.carrier, ∀ y ∈ geometry.carrier,
      ∃ z ∈ geometry.carrier, ZFSet.pair x z ∈ geometry.order ∧
        ZFSet.pair y z ∈ geometry.order) :
    letI := geometry.meet.order.toPartialOrder
    ∀ x y : SetMembers geometry.carrier, ∃ z, x ≤ z ∧ y ≤ z := by
  let := geometry.meet.order.toPartialOrder
  intro x y
  obtain ⟨z, hz, xz, yz⟩ := directed _ (SetMembers.raw_mem x) _ (SetMembers.raw_mem y)
  refine ⟨SetMembers.ofMem z hz, ?_, ?_⟩
  · change ZFSet.pair (SetMembers.raw x) (SetMembers.raw (SetMembers.ofMem z hz)) ∈ geometry.order
    simpa only [SetMembers.raw_ofMem] using xz
  · change ZFSet.pair (SetMembers.raw y) (SetMembers.raw (SetMembers.ofMem z hz)) ∈ geometry.order
    simpa only [SetMembers.raw_ofMem] using yz

theorem decoded_separating
    (separate : ∀ B ∈ geometry.carrier, ∀ d ∈ geometry.carrier,
      ZFSet.pair B d ∈ geometry.order →
      ∃ k ∈ geometry.actors,
        (∀ z ∈ geometry.carrier, ZFSet.pair z B ∈ geometry.order →
          ZFSet.pair (ZFSet.pair k z) z ∈ geometry.action) ∧
        ∃ y ∈ geometry.carrier, ZFSet.pair (ZFSet.pair k d) y ∈ geometry.action ∧
          ZFSet.pair (ZFSet.pair y d) B ∈ geometry.meetGraph) :
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    ∀ B d : SetMembers geometry.carrier, B ≤ d →
      ∃ k : SetMembers geometry.actors, k ∈ geometry.decodedAction.principalFix B ∧
        ∀ x, x ≤ d → x ≤ geometry.decodedAction.iso k d → x ≤ B := by
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  intro B d bd
  obtain ⟨k, hk, fixes, y, hy, action, meet⟩ :=
    separate _ (SetMembers.raw_mem B) _ (SetMembers.raw_mem d) bd
  let actor := SetMembers.ofMem k hk
  have acted : geometry.action_code.act actor d = SetMembers.ofMem y hy := by
    apply (geometry.action_code.act_eq_iff _ _ _).2
    simpa only [actor, SetMembers.raw_ofMem] using action
  refine ⟨actor, ?_, ?_⟩
  · intro z lower
    change geometry.action_code.act actor z = z
    apply (geometry.action_code.act_eq_iff _ _ _).2
    simpa only [actor, SetMembers.raw_ofMem] using fixes _ (SetMembers.raw_mem z) lower
  · intro x xd xacted
    change ZFSet.pair (SetMembers.raw x) (SetMembers.raw (geometry.action_code.act actor d))
      ∈ geometry.order at xacted
    rw [acted, SetMembers.raw_ofMem] at xacted
    exact geometry.meet.greatest y (SetMembers.raw d) (SetMembers.raw B)
      (SetMembers.raw x) (SetMembers.raw_mem x) meet xacted xd

end GroundMainFinalGeometry

namespace GroundMainPrefix.FinalFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalFulfillment level i₀)
include fulfilled

theorem internalRow_bounds_with
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets) :
    let geometry := run.finalGeometry i₀
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    ∀ (p : SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega))
      (X₁ X₂ : SetMembers geometry.carrier),
      ∃ d : SetMembers geometry.carrier, X₁ ≤ d ∧ X₂ ≤ d ∧
        ∀ i : {i : SetMembers geometry.carrier // i ≠ ⊥}, s.encode i.val ∈
          rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw p) → i.val ≤ d := by
  let geometry := run.finalGeometry i₀
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  dsimp only
  intro p X₁ X₂
  have rows := M.countablePartialFunctions_rowSupport pairing unions powers separation infinite choice
    (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
    (M.natSetCode_mem separation infinite 2) (SetMembers.raw_mem p)
  have subset : rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw p) ⊆
      geometry.carrier := by
    intro z hz
    exact ((s.mem_nonbottom_carrier z).1
      (rowUsedRows_subset s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw p) hz)).1
  obtain ⟨d, hd, bound⟩ := (fulfilled.countable_localization _ rows.1 subset rows.2).2
  let first := SetMembers.ofMem d hd
  obtain ⟨e, de, xe⟩ := geometry.decoded_directed fulfilled.directed first X₁
  obtain ⟨f, ef, yf⟩ := geometry.decoded_directed fulfilled.directed e X₂
  refine ⟨f, le_trans xe ef, yf, ?_⟩
  intro i hi
  have lower : i.val ≤ first := by
    change ZFSet.pair (SetMembers.raw i.val) (SetMembers.raw first) ∈ geometry.order
    simpa only [s, SetMembers.presentation, first, SetMembers.raw_ofMem] using
      bound (s.encode i.val) hi
  exact le_trans lower (le_trans de ef)

end GroundMainPrefix.FinalFulfillment

namespace GroundMainPrefix.FinalFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalFulfillment level i₀)

theorem exists_rowModel
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (groundChoice : Realize M.sets SetFormula.choice Fin.elim0) (small : M.sets.Countable) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    let b := SetMembers.presentation geometry.actors
    let a := geometry.decodedAction
    let columns := M.groundOmegaOne pairing unions powers separation collection infinite
    let hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    let F := a.principalSupportFamily (⊥ : SetMembers geometry.carrier)
      (geometry.decoded_directed fulfilled.directed)
    ∀ p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega),
    ∃ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)),
      H.mem p ∧ H.GenericFor (M.codedFamily c) ∧
      H.GenericFor (formulaFamily (M.nameDomain c)) ∧
      H.GenericFor (formulaFamily (act.symmetricDomain c (M.nameDomain c) F)) ∧
      M.sets ⊆ (act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q} ∧
      ZFRealization ((act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q}) ∧
      ¬ Realize ((act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q})
        SetFormula.choice Fin.elim0 := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  dsimp only
  intro p
  have order : s.conditionOrder ∈ M.sets :=
    geometry.decoded_order_eq.symm ▸ geometry.order_ground
  have graph : a.actionGraph s b ∈ M.sets :=
    geometry.decoded_action_eq.symm ▸ geometry.action_ground
  exact M.exists_internalRow_ZF_not_choice_groundOmegaOne a s b
    (geometry.decoded_directed fulfilled.directed)
    (geometry.decoded_unbounded fulfilled.growth)
    (geometry.decoded_countable_bound
      (fun X hX subset countable => (fulfilled.countable_localization X hX subset countable).2))
    (geometry.decoded_separating
      (fun B hB d hd lower => fulfilled.separates B hB d hd d hd lower lower))
    small pairing unions powers separation collection infinite groundChoice
    geometry.carrier_ground geometry.actors_ground order graph p

theorem exists_rowTermSystem
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    let b := SetMembers.presentation geometry.actors
    let a := geometry.decodedAction
    let columns := M.groundOmegaOne pairing unions powers separation collection infinite
    let hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, geometry.carrier_ground⟩
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    let supports := a.principalSupportFamily (⊥ : SetMembers geometry.carrier)
      (geometry.decoded_directed fulfilled.directed)
    ∃ mu ∈ M.sets, mu ∈ K ∧ GroundCardinal M mu ∧ ZFSet.omega ⊆ mu ∧
      M.groundEmbeddable s.nonbottom.carrier mu ∧
      let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
      let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
      let family := rowTupleFamily (c.encode ⊤) mu s.nonbottom.carrier
        (ZFSet.sUnion (ZFSet.sUnion rows)) rows S
      let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier
        (ZFSet.sUnion (ZFSet.sUnion rows)) rows S
      S ∈ M.sets ∧ GroundBelow M S K ∧ (∅ : ZFSet.{u}) ∈ S ∧
      family ∈ M.sets ∧ ZFSet.IsFunc S T family ∧ T ∈ M.sets ∧ GroundBelow M T K ∧
      ∀ n : Nat, let terms := iteratedPairNameFamily (c.encode ⊤) T n
        terms ∈ M.sets ∧ GroundBelow M terms K ∧
        (∀ z ∈ terms, IsName c z) ∧
        (∀ σ : Name c, σ.val ∈ terms → HereditarilySymmetric act c supports σ) ∧
        ∃ τ : Name c, τ.val ∈ M.sets ∧ τ.val = ZFSet.prod terms {c.encode ⊤} ∧
          HereditarilySymmetric act c supports τ ∧ (∀ g, act.act c g τ = τ) ∧
          ∀ H : Set (SetMembers (M.smallPartialFunctions
            (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)), ⊤ ∈ H → ∀ x,
            x ∈ Name.eval H τ ↔ ∃ σ : Name c, σ.val ∈ terms ∧ Name.eval H σ = x := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let columns := M.groundOmegaOne pairing unions powers separation collection infinite
  have hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, geometry.carrier_ground⟩
  have action : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  have order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  have directed := geometry.decoded_directed fulfilled.directed
  let supports := a.principalSupportFamily (⊥ : SetMembers geometry.carrier) directed
  obtain ⟨mu, hmu, hmuK, cardinal, omega, positions, hS, smallS, empty⟩ :=
    run.exists_finalRowPositionSequences i₀ collection infinite choice hK standard indices
  have sequenceEqual := congrArg
    (fun r => M.rowPositionSequences s.carrier r s.nonbottom.carrier mu) geometry.decoded_order_eq
  have groundS := (congrArg (fun A => A ∈ M.sets) sequenceEqual).mpr hS
  have belowS := (congrArg (fun A => GroundBelow M A K) sequenceEqual).mpr smallS
  have emptyS := (congrArg (fun A => (∅ : ZFSet.{u}) ∈ A) sequenceEqual).mpr empty
  dsimp only
  refine ⟨mu, hmu, hmuK, cardinal, omega, positions, groundS, belowS, emptyS, ?_⟩
  have hI := M.nonbottom_carrier_mem s separation geometry.carrier_ground
  obtain ⟨family, _, function, smallT⟩ :=
    M.binaryRowTupleTerms_mem_below pairing unions powers separation collection infinite choice
      geometry.carrier_ground order hI hColumns hmu hK belowS ⊤
  have base := M.binaryRowTermSetName_exists a s b columns pairing unions powers separation collection infinite
    geometry.carrier_ground hColumns geometry.actors_ground action order directed hmu cardinal.1
  have hT := base.1
  have each := M.binaryRowTupleTerms_hs a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action directed hmu cardinal.1
  have closed := M.binaryRowTupleTerms_action a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action hmu cardinal.1
  have hQ := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hColumns) (M.natSetCode_mem separation infinite 2)
  refine ⟨family, function, hT, smallT, ?_⟩
  apply M.invariantNamePowers act c supports pairing unions powers separation infinite choice
    (M.transitive hQ (c.encode_mem ⊤)) hT hK standard smallT
  · intro z hz
    obtain ⟨τ, equal, _⟩ := each z hz
    exact equal ▸ τ.property
  · exact closed
  · intro σ hσ
    obtain ⟨τ, equal, hs⟩ := each σ.val hσ
    have same : τ = σ := Subtype.ext equal
    exact same ▸ hs

include fulfilled

theorem decoded_strict_growth :
    let geometry := run.finalGeometry i₀
    letI := geometry.meet.order.toPartialOrder
    ∀ x : SetMembers geometry.carrier, ∃ y : SetMembers geometry.carrier, x < y := by
  let geometry := run.finalGeometry i₀
  let := geometry.meet.order.toPartialOrder
  dsimp only
  intro x
  obtain ⟨y, hy, lower, strict⟩ := fulfilled.growth _ (SetMembers.raw_mem x)
  refine ⟨SetMembers.ofMem y hy, lt_iff_le_not_ge.2 ⟨?_, ?_⟩⟩
  · change ZFSet.pair (SetMembers.raw x) (SetMembers.raw (SetMembers.ofMem y hy))
      ∈ geometry.order
    simpa only [SetMembers.raw_ofMem] using lower
  · change ¬ ZFSet.pair (SetMembers.raw (SetMembers.ofMem y hy)) (SetMembers.raw x)
      ∈ geometry.order
    simpa only [SetMembers.raw_ofMem] using strict

theorem exists_commonPrincipalSupport_strict_extension :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let directed := geometry.decoded_directed fulfilled.directed
    ∀ {P : Type u} [PartialOrder P] (a : PosetAction (SetMembers geometry.actors) P)
      (s : Presentation P) {n : Nat} (tau : Fin n → Name s),
      (∀ i, HereditarilySymmetric a s
        (geometry.decodedAction.principalSupportFamily ⊥ directed) (tau i)) →
      ∃ C E : SetMembers geometry.carrier, ⊥ ≤ C ∧ C < E ∧
        ∀ i, geometry.decodedAction.principalFix C ≤ a.stabilizer s (tau i) := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro P inst a s n tau symmetric
  obtain ⟨C, hC, fixed⟩ := Name.exists_commonPrincipalNameSupport a s geometry.decodedAction
    ⊥ directed tau (fun i => (symmetric i).symmetric)
  obtain ⟨E, strict⟩ := fulfilled.decoded_strict_growth C
  exact ⟨C, E, hC, strict, fixed⟩

end GroundMainPrefix.FinalFulfillment

namespace GroundMainPrefix.FinalFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalFulfillment level i₀)

theorem exists_rowModel_sequenceReflection
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (groundChoice : Realize M.sets SetFormula.choice Fin.elim0) (small : M.sets.Countable) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    let b := SetMembers.presentation geometry.actors
    let a := geometry.decodedAction
    let columns := M.groundOmegaOne pairing unions powers separation collection infinite
    let hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    let F := a.principalSupportFamily (⊥ : SetMembers geometry.carrier)
      (geometry.decoded_directed fulfilled.directed)
    ∀ p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega),
    ∃ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)),
      H.mem p ∧ H.GenericFor (M.codedFamily c) ∧
      H.GenericFor (formulaFamily (M.nameDomain c)) ∧
      H.GenericFor (formulaFamily (act.symmetricDomain c (M.nameDomain c) F)) ∧
      M.sets ⊆ (act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q} ∧
      ZFRealization ((act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q}) ∧
      ¬ Realize ((act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q})
        SetFormula.choice Fin.elim0 ∧
      ∀ U ∈ M.sets, GroundSequenceReflection M (M.ordinaryExtension c H) U := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let columns := M.groundOmegaOne pairing unions powers separation collection infinite
  have hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  dsimp only
  intro p
  obtain ⟨H, hp, coded, ordinary, symmetric, includes, zf, noChoice⟩ :=
    fulfilled.exists_rowModel collection infinite groundChoice small p
  refine ⟨H, hp, coded, ordinary, symmetric, includes, zf, noChoice, ?_⟩
  intro U hU
  exact M.countableFunction_sequenceReflection pairing unions powers separation collection infinite
    groundChoice small
    (M.prod_mem pairing unions powers separation
      (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns)
    (M.natSetCode_mem separation infinite 2) hU H coded ordinary

theorem exists_rowModel_ordinaryZF
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (groundChoice : Realize M.sets SetFormula.choice Fin.elim0) (small : M.sets.Countable) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    let b := SetMembers.presentation geometry.actors
    let a := geometry.decodedAction
    let columns := M.groundOmegaOne pairing unions powers separation collection infinite
    let hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    let F := a.principalSupportFamily (⊥ : SetMembers geometry.carrier)
      (geometry.decoded_directed fulfilled.directed)
    ∀ p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega),
    ∃ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)),
      H.mem p ∧ H.GenericFor (M.codedFamily c) ∧
      H.GenericFor (formulaFamily (M.nameDomain c)) ∧
      H.GenericFor (formulaFamily (act.symmetricDomain c (M.nameDomain c) F)) ∧
      M.sets ⊆ (act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q} ∧
      ZFRealization ((act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q}) ∧
      ¬ Realize ((act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q})
        SetFormula.choice Fin.elim0 ∧
      ZFRealization (M.ordinaryExtension c H).sets ∧
      CollectionSchema (M.ordinaryExtension c H).sets ∧
      ∀ U ∈ M.sets, GroundSequenceReflection M (M.ordinaryExtension c H) U := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let columns := M.groundOmegaOne pairing unions powers separation collection infinite
  have hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  dsimp only
  intro p
  obtain ⟨H, hp, coded, ordinary, symmetric, includes, zf, noChoice, reflection⟩ :=
    fulfilled.exists_rowModel_sequenceReflection collection infinite groundChoice small p
  have axioms := M.countableFunction_ordinaryZF pairing unions powers separation collection infinite
    (M.prod_mem pairing unions powers separation
      (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns)
    (M.natSetCode_mem separation infinite 2) H ordinary
  exact ⟨H, hp, coded, ordinary, symmetric, includes, zf, noChoice, axioms.1, axioms.2, reflection⟩

end GroundMainPrefix.FinalFulfillment

end PartitionPilot.Forcing

end OAI
