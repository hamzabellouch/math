import OAI.SetTheory.PartitionPrinciple.Geometry.GroundContainmentOrders

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

@[instance_reducible]
noncomputable def smallFunctionOrder (X Y N : ZFSet.{u}) :
    PartialOrder (SetMembers (M.smallPartialFunctions X Y N)) :=
  (reverseInclusion_partialOrder (M.smallPartialFunctions X Y N)).toPartialOrder

@[instance_reducible]
noncomputable def smallFunctionTop (X Y N : ZFSet.{u}) (nonempty : M.sets.Nonempty) :
    letI _smallOrder := M.smallFunctionOrder X Y N
    OrderTop (SetMembers (M.smallPartialFunctions X Y N)) :=
  (reverseInclusion_partialOrder (M.smallPartialFunctions X Y N)).toOrderTop ∅
    (M.empty_mem_smallPartialFunctions X Y N nonempty)
    (reverseInclusion_empty_top (M.empty_mem_smallPartialFunctions X Y N nonempty))

theorem smallFunction_le_iff (X Y N : ZFSet.{u})
    (p q : SetMembers (M.smallPartialFunctions X Y N)) :
    letI _smallOrder := M.smallFunctionOrder X Y N
    p ≤ q ↔ SetMembers.raw q ⊆ SetMembers.raw p := by
  let smallOrder := M.smallFunctionOrder X Y N
  change ZFSet.pair (SetMembers.raw p) (SetMembers.raw q) ∈
    reverseInclusionCode (M.smallPartialFunctions X Y N) ↔ _
  rw [pair_mem_reverseInclusionCode]
  exact ⟨fun h => h.2.2, fun h => ⟨SetMembers.raw_mem p, SetMembers.raw_mem q, h⟩⟩

theorem smallFunction_raw_properties (X Y N : ZFSet.{u})
    (p : SetMembers (M.smallPartialFunctions X Y N)) :
    SetMembers.raw p ∈ M.sets ∧ PartialFunctionCode X Y (SetMembers.raw p) ∧
      M.groundEmbeddable (SetMembers.raw p) N :=
  (M.mem_smallPartialFunctions X Y N _).1 (SetMembers.raw_mem p)

theorem smallFunctionOrder_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {X Y N : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) (hN : N ∈ M.sets) :
    letI _smallOrder := M.smallFunctionOrder X Y N
    (SetMembers.presentation (M.smallPartialFunctions X Y N)).conditionOrder ∈ M.sets := by
  let smallOrder := M.smallFunctionOrder X Y N
  rw [(reverseInclusion_partialOrder (M.smallPartialFunctions X Y N)).conditionOrder_eq]
  exact M.reverseInclusionCode_mem pairing unions powers separation
    (M.smallPartialFunctions_mem pairing unions powers separation hX hY hN)

theorem exists_smallFunction_generic
    (small : M.sets.Countable)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {X Y N : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) (hN : N ∈ M.sets)
    (p : SetMembers (M.smallPartialFunctions X Y N)) :
    letI _smallOrder := M.smallFunctionOrder X Y N
    ∃ H : ConditionFilter (SetMembers (M.smallPartialFunctions X Y N)), H.mem p ∧
      H.GenericFor (M.codedFamily (SetMembers.presentation (M.smallPartialFunctions X Y N))) ∧
      H.GenericFor (formulaFamily (M.nameDomain (SetMembers.presentation (M.smallPartialFunctions X Y N)))) := by
  let smallOrder := M.smallFunctionOrder X Y N
  have carrier := M.smallPartialFunctions_mem pairing unions powers separation hX hY hN
  have order := M.reverseInclusionCode_mem pairing unions powers separation carrier
  have laws := (M.realize_partialOrderCode carrier order).2 (reverseInclusion_partialOrder (M.smallPartialFunctions X Y N))
  exact M.exists_decoded_generic small carrier order laws p

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.SetRealization.Presentation

open Forcing
universe u
variable {A B : Type u} (s : Presentation A) (t : Presentation B)

theorem relation_ext {p q : ZFSet.{u}} (hp : p ⊆ ZFSet.prod s.carrier t.carrier)
    (hq : q ⊆ ZFSet.prod s.carrier t.carrier)
    (entries : ∀ a b, ZFSet.pair (s.encode a) (t.encode b) ∈ p ↔
      ZFSet.pair (s.encode a) (t.encode b) ∈ q) : p = q := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (hp hz)
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (t.mem_carrier y).1 hy
    exact (entries a b).1 hz
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (hq hz)
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (t.mem_carrier y).1 hy
    exact (entries a b).2 hz

theorem graph_injection (f : A → B) (injective : Function.Injective f) :
    InjectionCode s.carrier t.carrier (s.graph t f) := by
  have function := s.graph_isFunc t f
  refine ⟨function, ?_⟩
  intro x y z hx hy
  obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 (ZFSet.pair_mem_prod.1 (function.1 hx)).1
  obtain ⟨b, rfl⟩ := (s.mem_carrier y).1 (ZFSet.pair_mem_prod.1 (function.1 hy)).1
  obtain ⟨c, rfl⟩ := (t.mem_carrier z).1 (ZFSet.pair_mem_prod.1 (function.1 hx)).2
  exact congrArg s.encode (injective
    (((s.pair_mem_graph t f a c).1 hx).trans ((s.pair_mem_graph t f b c).1 hy).symm))

theorem converse_graph (e : A ≃ B) :
    relationConverse s.carrier t.carrier (s.graph t e) = t.graph s e.symm := by
  apply t.relation_ext s (fun _ hz => (ZFSet.mem_sep.1 hz).1) (t.graph_isFunc s e.symm).1
  intro b a
  change ZFSet.pair (t.encode b) (s.encode a) ∈ relationConverse s.carrier t.carrier (s.graph t e) ↔ _
  rw [pair_mem_relationConverse, s.pair_mem_graph, t.pair_mem_graph]
  exact ⟨fun h => (congrArg e.symm h.2.2).symm.trans (e.symm_apply_apply a),
    fun eq => ⟨s.encode_mem a, t.encode_mem b, by rw [← eq, e.apply_symm_apply]⟩⟩

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing

open SetRealization
universe u
variable {X Y : Type u} (s : Presentation X) (t : Presentation Y)

noncomputable def graphRename (e : X ≃ X) (p : ZFSet.{u}) : ZFSet.{u} :=
  (s.product t).subset (fun xy => ZFSet.pair (s.encode (e.symm xy.1)) (t.encode xy.2) ∈ p)

theorem pair_mem_graphRename (e : X ≃ X) (p : ZFSet.{u}) (x : X) (y : Y) :
    ZFSet.pair (s.encode x) (t.encode y) ∈ graphRename s t e p ↔
      ZFSet.pair (s.encode (e.symm x)) (t.encode y) ∈ p :=
  (s.product t).encode_mem_subset _ (x, y)

theorem graphRename_shape (e : X ≃ X) (p : ZFSet.{u}) :
    graphRename s t e p ⊆ ZFSet.prod s.carrier t.carrier := (s.product t).subset_carrier _

theorem graphRename_partial (e : X ≃ X) {p : ZFSet.{u}} (h : PartialFunctionCode s.carrier t.carrier p) :
    PartialFunctionCode s.carrier t.carrier (graphRename s t e p) := by
  refine ⟨graphRename_shape s t e p, ?_⟩
  intro x y z hy hz
  have xy := ZFSet.pair_mem_prod.1 (graphRename_shape s t e p hy)
  have xz := ZFSet.pair_mem_prod.1 (graphRename_shape s t e p hz)
  obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 xy.1
  obtain ⟨b, rfl⟩ := (t.mem_carrier y).1 xy.2
  obtain ⟨c, rfl⟩ := (t.mem_carrier z).1 xz.2
  exact h.unique _ _ _ ((pair_mem_graphRename s t e p a b).1 hy)
    ((pair_mem_graphRename s t e p a c).1 hz)

theorem graphRename_refl {p : ZFSet.{u}} (shape : p ⊆ ZFSet.prod s.carrier t.carrier) :
    graphRename s t (Equiv.refl X) p = p := by
  apply s.relation_ext t (graphRename_shape s t _ p) shape
  intro x y
  exact pair_mem_graphRename s t _ p x y

theorem graphRename_comp (e f : X ≃ X) (p : ZFSet.{u}) :
    graphRename s t f (graphRename s t e p) = graphRename s t (e.trans f) p := by
  apply s.relation_ext t (graphRename_shape s t _ _) (graphRename_shape s t _ _)
  intro x y
  rw [pair_mem_graphRename, pair_mem_graphRename, pair_mem_graphRename]
  rfl

theorem graphRename_inverse (e : X ≃ X) {p : ZFSet.{u}}
    (shape : p ⊆ ZFSet.prod s.carrier t.carrier) :
    graphRename s t e.symm (graphRename s t e p) = p := by
  apply s.relation_ext t (graphRename_shape s t _ _) shape
  intro x y
  rw [pair_mem_graphRename, pair_mem_graphRename]
  change ZFSet.pair (s.encode (e.symm (e x))) (t.encode y) ∈ p ↔ _
  rw [e.symm_apply_apply]

theorem graphRename_mono (e : X ≃ X) {p q : ZFSet.{u}} (subset : p ⊆ q) :
    graphRename s t e p ⊆ graphRename s t e q := by
  intro z hz
  obtain ⟨⟨x, y⟩, rel, rfl⟩ := ((s.product t).mem_subset _ z).1 hz
  exact (pair_mem_graphRename s t e q x y).2 (subset rel)

noncomputable def entryPermutationGraph (e : X ≃ X) : ZFSet.{u} :=
  (s.product t).graph (s.product t) (fun xy => (e xy.1, xy.2))

theorem entryPermutation_injection (e : X ≃ X) :
    InjectionCode (ZFSet.prod s.carrier t.carrier) (ZFSet.prod s.carrier t.carrier)
      (entryPermutationGraph s t e) := by
  apply (s.product t).graph_injection (s.product t)
  intro a b eq
  apply Prod.ext
  · exact e.injective (congrArg (fun z : X × Y => z.1) eq)
  · have same := congrArg (fun z : X × Y => z.2) eq
    exact same

theorem graphRename_eq_image (e : X ≃ X) (p : ZFSet.{u}) :
    graphRename s t e p = relationImage p (ZFSet.prod s.carrier t.carrier) (entryPermutationGraph s t e) := by
  apply s.relation_ext t (graphRename_shape s t _ _) (fun _ hz => (ZFSet.mem_sep.1 hz).1)
  intro x y
  rw [pair_mem_graphRename, ZFSet.mem_sep]
  constructor
  · intro rel
    refine ⟨ZFSet.pair_mem_prod.2 ⟨s.encode_mem x, t.encode_mem y⟩,
      ZFSet.pair (s.encode (e.symm x)) (t.encode y), rel, ?_⟩
    apply ((s.product t).pair_mem_graph (s.product t) _ (e.symm x, y) (x, y)).2
    exact Prod.ext (e.apply_symm_apply x) rfl
  · rintro ⟨_, z, hz, rel⟩
    have hzC := (ZFSet.pair_mem_prod.1 ((entryPermutation_injection s t e).function.1 rel)).1
    obtain ⟨⟨a, b⟩, rfl⟩ := ((s.product t).mem_carrier z).1 hzC
    have eq := ((s.product t).pair_mem_graph (s.product t) _ (a, b) (x, y)).1 rel
    have ax : a = e.symm x := (e.symm_apply_apply a).symm.trans (congrArg e.symm (congrArg Prod.fst eq))
    have by' : b = y := congrArg Prod.snd eq
    change ZFSet.pair (s.encode a) (t.encode b) ∈ p at hz
    simpa only [ax, by'] using hz

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula SetRealization
universe u

def entryTransportFormula {n} (a b r x y : Fin n) : BoundedFormula n :=
  exMem x (exMem x.succ (exMem y.succ.succ
    (.conj (orderedPairFormula a.succ.succ.succ 2 0)
      (.conj (orderedPairFormula b.succ.succ.succ 1 0)
        (pairMembershipFormula 2 1 r.succ.succ.succ)))))

def entryPermutationFormula {n} (z r x y c : Fin n) : BoundedFormula n :=
  exMem c (exMem c.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (entryTransportFormula 1 0 r.succ.succ x.succ.succ y.succ.succ)))

theorem truth_entryTransportFormula {n} (a b r x y : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (entryTransportFormula a b r x y) env ↔
      ∃ i ∈ env x, ∃ j ∈ env x, ∃ v ∈ env y,
        env a = ZFSet.pair i v ∧ env b = ZFSet.pair j v ∧ ZFSet.pair i j ∈ env r := by
  simp only [entryTransportFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

theorem truth_entryPermutationFormula {n} (z r x y c : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (entryPermutationFormula z r x y c) env ↔
      ∃ a ∈ env c, ∃ b ∈ env c, env z = ZFSet.pair a b ∧
        ∃ i ∈ env x, ∃ j ∈ env x, ∃ v ∈ env y,
          a = ZFSet.pair i v ∧ b = ZFSet.pair j v ∧ ZFSet.pair i j ∈ env r := by
  simp only [entryPermutationFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_entryTransportFormula]
  rfl

theorem entryPermutation_correct {X Y : Type u} (s : Presentation X) (t : Presentation Y)
    (e : X ≃ X) (z : ZFSet.{u}) :
    Truth (entryPermutationFormula 0 1 2 3 4)
      (extend z (extend (s.graph s e) (extend s.carrier (extend t.carrier
        (extend (ZFSet.prod s.carrier t.carrier) Fin.elim0))))) ↔ z ∈ entryPermutationGraph s t e := by
  rw [truth_entryPermutationFormula]
  change (∃ a ∈ ZFSet.prod s.carrier t.carrier, ∃ b ∈ ZFSet.prod s.carrier t.carrier,
    z = ZFSet.pair a b ∧ ∃ i ∈ s.carrier, ∃ j ∈ s.carrier, ∃ v ∈ t.carrier,
      a = ZFSet.pair i v ∧ b = ZFSet.pair j v ∧ ZFSet.pair i j ∈ s.graph s e) ↔ _
  constructor
  · rintro ⟨a, _, b, _, rfl, i, hi, j, hj, v, hv, rfl, rfl, rel⟩
    obtain ⟨x, rfl⟩ := (s.mem_carrier i).1 hi
    obtain ⟨x', rfl⟩ := (s.mem_carrier j).1 hj
    obtain ⟨y, rfl⟩ := (t.mem_carrier v).1 hv
    exact ((s.product t).pair_mem_graph (s.product t) _ (x, y) (x', y)).2
      (Prod.ext ((s.pair_mem_graph s e x x').1 rel) rfl)
  · intro hz
    obtain ⟨⟨x, y⟩, eq⟩ := ((s.product t).mem_graph (s.product t) _ z).1 hz
    exact ⟨ZFSet.pair (s.encode x) (t.encode y), (s.product t).encode_mem (x, y),
      ZFSet.pair (s.encode (e x)) (t.encode y), (s.product t).encode_mem (e x, y), eq.symm,
      s.encode x, s.encode_mem x, s.encode (e x), s.encode_mem (e x), t.encode y, t.encode_mem y,
      rfl, rfl, (s.pair_mem_graph s e x (e x)).2 rfl⟩

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {X Y : Type u} (s : Presentation X) (t : Presentation Y)

theorem inverse_function_graph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (e : X ≃ Y) (hX : s.carrier ∈ M.sets) (hY : t.carrier ∈ M.sets)
    (graph : s.graph t e ∈ M.sets) : t.graph s e.symm ∈ M.sets := by
  rw [← s.converse_graph t e]
  exact M.relationConverse_mem pairing unions powers separation hX hY graph

theorem entryPermutationGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (e : X ≃ X) (hX : s.carrier ∈ M.sets) (hY : t.carrier ∈ M.sets)
    (graph : s.graph s e ∈ M.sets) : entryPermutationGraph s t e ∈ M.sets := by
  have product := M.prod_mem pairing unions powers separation hX hY
  have bound := M.prod_mem pairing unions powers separation product product
  let params := extend (s.graph s e) (extend s.carrier (extend t.carrier
    (extend (ZFSet.prod s.carrier t.carrier) Fin.elim0)))
  have selected := M.bounded_separation_mem separation (BoundedFormula.entryPermutationFormula 0 1 2 3 4)
    params (Fin.cases graph (Fin.cases hX (Fin.cases hY (Fin.cases product (fun i => Fin.elim0 i))))) bound
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.entryPermutationFormula 0 1 2 3 4)
      (extend z params)) (ZFSet.prod (ZFSet.prod s.carrier t.carrier) (ZFSet.prod s.carrier t.carrier)) =
        entryPermutationGraph s t e := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    exact ⟨fun h => (BoundedFormula.entryPermutation_correct s t e z).1 h.2,
      fun hz => ⟨(entryPermutation_injection s t e).function.1 hz,
        (BoundedFormula.entryPermutation_correct s t e z).2 hz⟩⟩
  exact eq ▸ selected

theorem graphRename_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (e : X ≃ X) (hX : s.carrier ∈ M.sets) (hY : t.carrier ∈ M.sets)
    (graph : s.graph s e ∈ M.sets) {p : ZFSet.{u}} (hp : p ∈ M.sets) : graphRename s t e p ∈ M.sets := by
  rw [graphRename_eq_image]
  exact M.relationImage_mem separation hp (M.prod_mem pairing unions powers separation hX hY)
    (M.entryPermutationGraph_mem s t pairing unions powers separation e hX hY graph)

theorem smallPartialFunctions_rename
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (e : X ≃ X) (hX : s.carrier ∈ M.sets) (hY : t.carrier ∈ M.sets)
    (graph : s.graph s e ∈ M.sets) {N p : ZFSet.{u}} (hN : N ∈ M.sets)
    (hp : p ∈ M.smallPartialFunctions s.carrier t.carrier N) :
    graphRename s t e p ∈ M.smallPartialFunctions s.carrier t.carrier N := by
  obtain ⟨hpM, code, small⟩ := (M.mem_smallPartialFunctions s.carrier t.carrier N p).1 hp
  refine (M.mem_smallPartialFunctions s.carrier t.carrier N _).2
    ⟨M.graphRename_mem s t pairing unions powers separation e hX hY graph hpM,
      graphRename_partial s t e code, ?_⟩
  rw [graphRename_eq_image]
  exact M.groundEmbeddable_image pairing unions powers separation hpM
    (M.prod_mem pairing unions powers separation hX hY) hN
    (M.entryPermutationGraph_mem s t pairing unions powers separation e hX hY graph)
    (entryPermutation_injection s t e) code.shape small

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {X Y : Type u} (s : Presentation X) (t : Presentation Y)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {N : ZFSet.{u}} (hX : s.carrier ∈ M.sets) (hY : t.carrier ∈ M.sets) (hN : N ∈ M.sets)

noncomputable def renameSmallCondition (e : X ≃ X) (graph : s.graph s e ∈ M.sets)
    (p : SetMembers (M.smallPartialFunctions s.carrier t.carrier N)) :
    SetMembers (M.smallPartialFunctions s.carrier t.carrier N) :=
  SetMembers.ofMem (graphRename s t e (SetMembers.raw p))
    (M.smallPartialFunctions_rename s t pairing unions powers separation e hX hY graph hN (SetMembers.raw_mem p))

theorem raw_renameSmallCondition (e : X ≃ X) (graph : s.graph s e ∈ M.sets)
    (p : SetMembers (M.smallPartialFunctions s.carrier t.carrier N)) :
    SetMembers.raw (M.renameSmallCondition s t pairing unions powers separation hX hY hN e graph p) =
      graphRename s t e (SetMembers.raw p) := SetMembers.raw_ofMem _ _

theorem renameSmallCondition_inverse (e : X ≃ X)
    (graph : s.graph s e ∈ M.sets) (inverse : s.graph s e.symm ∈ M.sets)
    (p : SetMembers (M.smallPartialFunctions s.carrier t.carrier N)) :
    M.renameSmallCondition s t pairing unions powers separation hX hY hN e.symm inverse
      (M.renameSmallCondition s t pairing unions powers separation hX hY hN e graph p) = p := by
  apply SetMembers.raw_injective
  rw [raw_renameSmallCondition, raw_renameSmallCondition]
  exact graphRename_inverse s t e
    (M.smallFunction_raw_properties s.carrier t.carrier N p).2.1.shape

theorem renameSmallCondition_le_iff (e : X ≃ X) (graph : s.graph s e ∈ M.sets)
    (p q : SetMembers (M.smallPartialFunctions s.carrier t.carrier N)) :
    letI _smallOrder := M.smallFunctionOrder s.carrier t.carrier N
    M.renameSmallCondition s t pairing unions powers separation hX hY hN e graph p ≤
      M.renameSmallCondition s t pairing unions powers separation hX hY hN e graph q ↔ p ≤ q := by
  let smallOrder := M.smallFunctionOrder s.carrier t.carrier N
  rw [M.smallFunction_le_iff, M.smallFunction_le_iff, raw_renameSmallCondition, raw_renameSmallCondition]
  constructor
  · intro subset
    have back := graphRename_mono s t e.symm subset
    rw [graphRename_inverse s t e (M.smallFunction_raw_properties s.carrier t.carrier N q).2.1.shape,
      graphRename_inverse s t e (M.smallFunction_raw_properties s.carrier t.carrier N p).2.1.shape] at back
    exact back
  · exact graphRename_mono s t e

noncomputable def renameSmallOrderIso (e : X ≃ X) (graph : s.graph s e ∈ M.sets) :
    letI _smallOrder := M.smallFunctionOrder s.carrier t.carrier N
    SetMembers (M.smallPartialFunctions s.carrier t.carrier N) ≃o
      SetMembers (M.smallPartialFunctions s.carrier t.carrier N) := by
  letI smallOrder := M.smallFunctionOrder s.carrier t.carrier N
  have inverse := M.inverse_function_graph_mem s s pairing unions powers separation e hX hX graph
  exact {
    toFun := M.renameSmallCondition s t pairing unions powers separation hX hY hN e graph
    invFun := M.renameSmallCondition s t pairing unions powers separation hX hY hN e.symm inverse
    left_inv := M.renameSmallCondition_inverse s t pairing unions powers separation hX hY hN e graph inverse
    right_inv := M.renameSmallCondition_inverse s t pairing unions powers separation hX hY hN e.symm inverse graph
    map_rel_iff' := fun {p q} => M.renameSmallCondition_le_iff s t pairing unions powers separation hX hY hN e graph p q }

theorem raw_renameSmallOrderIso (e : X ≃ X) (graph : s.graph s e ∈ M.sets)
    (p : SetMembers (M.smallPartialFunctions s.carrier t.carrier N)) :
    letI _smallOrder := M.smallFunctionOrder s.carrier t.carrier N
    SetMembers.raw (M.renameSmallOrderIso s t pairing unions powers separation hX hY hN e graph p) =
      graphRename s t e (SetMembers.raw p) := SetMembers.raw_ofMem _ _

end PartitionPilot.Forcing.TransitiveGround

end OAI
