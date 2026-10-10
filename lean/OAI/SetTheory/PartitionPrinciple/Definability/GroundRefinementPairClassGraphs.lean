import OAI.SetTheory.PartitionPrinciple.Forcing.GroundPairNameFamilies
import OAI.SetTheory.PartitionPrinciple.Forcing.RefinementAssignmentLabelNames
import OAI.SetTheory.PartitionPrinciple.Transfinite.FiniteFamilyRankBounds

namespace OAI


namespace PartitionPilot.Forcing

namespace TransitiveGround

open SetRealization SetFormula
universe u v
variable (M : TransitiveGround.{u})

theorem finite_set_code
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (nonempty : M.sets.Nonempty)
    {S : Set ZFSet.{u}} (finite : S.Finite) :
    S ⊆ M.sets → ∃ D ∈ M.sets, D.toSet = S := by
  induction S, finite using Set.Finite.induction_on with
  | empty =>
    intro _
    exact ⟨∅, M.empty_mem nonempty, ZFSet.coe_empty⟩
  | @insert a S fresh finite ih =>
    intro members
    obtain ⟨D, hD, eq⟩ := ih (fun _ hx => members (Set.mem_insert_of_mem _ hx))
    refine ⟨insert a D, M.insert_mem pairing unions (members (Set.mem_insert a S)) hD, ?_⟩
    exact (ZFSet.coe_insert a D).trans (congrArg (insert a) eq)

theorem finite_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (nonempty : M.sets.Nonempty)
    {D : ZFSet.{u}} (finite : D.toSet.Finite) (members : ∀ x ∈ D, x ∈ M.sets) : D ∈ M.sets := by
  obtain ⟨E, hE, eq⟩ := M.finite_set_code pairing unions nonempty finite (fun x hx => members x hx)
  exact SetLike.coe_injective (show (E : Set ZFSet) = (D : Set ZFSet) from eq) ▸ hE

theorem finite_range_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (nonempty : M.sets.Nonempty)
    {A : Type v} [Finite A] [Small.{u} A] (f : A → ZFSet.{u}) (members : ∀ a, f a ∈ M.sets) :
    ZFSet.range f ∈ M.sets := by
  apply M.finite_mem pairing unions nonempty
  · change (ZFSet.range f : Set ZFSet).Finite
    rw [ZFSet.coe_range]
    simpa only [Set.image_univ] using Set.finite_univ.image f
  · intro x hx
    obtain ⟨a, rfl⟩ := ZFSet.mem_range.1 hx
    exact members a

theorem finite_function_graph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {A B : Type u} [Finite A] (s : Presentation A) (t : Presentation B) (f : A → B)
    (hA : s.carrier ∈ M.sets) (hB : t.carrier ∈ M.sets) : s.graph t f ∈ M.sets := by
  have ground := M.finite_range_mem pairing unions ⟨s.carrier, hA⟩
    (fun a => ZFSet.pair (s.encode a) (t.encode (f a)))
    (fun a => M.orderedPair_mem pairing (M.transitive hA (s.encode_mem a))
      (M.transitive hB (t.encode_mem (f a))))
  have eq : ZFSet.range (fun a => ZFSet.pair (s.encode a) (t.encode (f a))) = s.graph t f := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_range, s.mem_graph]
  exact eq ▸ ground

end TransitiveGround



section
open SetFormula SetRealization
universe u v

noncomputable def familyCodeGraph {I : Type v} [Small.{u} I]
    (key value : I → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun i => ZFSet.pair (key i) (value i))

theorem mem_familyCodeGraph {I : Type v} [Small.{u} I]
    (key value : I → ZFSet.{u}) (z : ZFSet.{u}) :
    z ∈ familyCodeGraph key value ↔ ∃ i, ZFSet.pair (key i) (value i) = z :=
  ZFSet.mem_range

theorem pair_mem_familyCodeGraph {I : Type v} [Small.{u} I]
    (key value : I → ZFSet.{u}) (injective : Function.Injective key)
    (i : I) (y : ZFSet.{u}) :
    ZFSet.pair (key i) y ∈ familyCodeGraph key value ↔ y = value i := by
  rw [mem_familyCodeGraph]
  constructor
  · rintro ⟨j, equal⟩
    obtain ⟨keys, values⟩ := ZFSet.pair_inj.1 equal
    have equalIndex := injective keys
    simpa only [equalIndex] using values.symm
  · intro equal
    exact ⟨i, congrArg (ZFSet.pair (key i)) equal.symm⟩

theorem familyCodeGraph_isFunc {I : Type v} [Small.{u} I]
    (key value : I → ZFSet.{u}) (injective : Function.Injective key) :
    ZFSet.IsFunc (ZFSet.range key) (ZFSet.range value) (familyCodeGraph key value) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨i, rfl⟩ := (mem_familyCodeGraph key value z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_range.2 ⟨i, rfl⟩, ZFSet.mem_range.2 ⟨i, rfl⟩⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
    exact ⟨value i, (pair_mem_familyCodeGraph key value injective i _).2 rfl,
      fun y hy => (pair_mem_familyCodeGraph key value injective i y).1 hy⟩

theorem familyCodeGraph_function {I : Type v} [Small.{u} I]
    (key value : I → ZFSet.{u}) (injective : Function.Injective key) :
    FunctionGraphOn (ZFSet.range key) (familyCodeGraph key value) :=
  ⟨ZFSet.range value, familyCodeGraph_isFunc key value injective⟩

theorem familyCodeGraph_restrict {I : Type v} [Small.{u} I]
    (key value : I → ZFSet.{u}) (injective : Function.Injective key) (p : I → Prop) :
    graphRestriction (ZFSet.range (fun i : {i // p i} => key i.val))
      (familyCodeGraph key value) =
        familyCodeGraph (fun i : {i // p i} => key i.val) (fun i => value i.val) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, rfl, entry⟩ := mem_graphRestriction.1 hz
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
    have valueEqual := (pair_mem_familyCodeGraph key value injective i.val y).1 entry
    exact (mem_familyCodeGraph _ _ _).2 ⟨i, congrArg (ZFSet.pair (key i.val)) valueEqual.symm⟩
  · intro hz
    obtain ⟨i, rfl⟩ := (mem_familyCodeGraph _ _ z).1 hz
    exact pair_mem_graphRestriction.2
      ⟨(pair_mem_familyCodeGraph key value injective i.val _).2 rfl,
        ZFSet.mem_range.2 ⟨i, rfl⟩⟩

theorem familyCodeGraph_finite_ground {M : TransitiveGround.{u}} {I : Type v}
    [Small.{u} I] [Finite I]
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (nonempty : M.sets.Nonempty)
    (key value : I → ZFSet.{u})
    (keys : ∀ i, key i ∈ M.sets) (values : ∀ i, value i ∈ M.sets) :
    familyCodeGraph key value ∈ M.sets :=
  M.finite_range_mem pairing unions nonempty _
    (fun i => M.orderedPair_mem pairing (keys i) (values i))

theorem rank_finiteCodeRange_lt {I : Type v} [Small.{u} I] [Finite I]
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (value : I → ZFSet.{u})
    (bounds : ∀ i, ZFSet.rank (value i) < o) :
    ZFSet.rank (ZFSet.range value) < o := by
  classical
  let := Fintype.ofFinite I
  let e := Fintype.equivFin I
  have equal : ZFSet.range value = ZFSet.range (fun i => value (e.symm i)) := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_range]
    exact ⟨fun ⟨i, hi⟩ => ⟨e i, by simpa only [e.symm_apply_apply] using hi⟩,
      fun ⟨i, hi⟩ => ⟨e.symm i, hi⟩⟩
  rw [equal]
  exact rank_finiteRange_lt limit _ _ (fun i => bounds (e.symm i))

theorem familyCodeGraph_finite_rank_lt {I : Type v} [Small.{u} I] [Finite I]
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (key value : I → ZFSet.{u})
    (keys : ∀ i, ZFSet.rank (key i) < o) (values : ∀ i, ZFSet.rank (value i) < o) :
    ZFSet.rank (familyCodeGraph key value) < o :=
  rank_finiteCodeRange_lt limit _
    (fun i => rank_orderedPair_lt limit (keys i) (values i))

end



section
open SetFormula SetRealization
universe u
namespace GroundDefinableFunction
variable {M : TransitiveGround.{u}} {n : Nat}
variable {f : (Fin (n + 1) → ZFSet.{u}) → ZFSet.{u}}

noncomputable def graph (_defined : GroundDefinableFunction M f)
    (params : Fin n → ZFSet.{u}) (A : ZFSet.{u}) : ZFSet.{u} :=
  familyCodeGraph (fun x : A => x.val) (fun x => f (extend x.val params))

theorem mem_graph (defined : GroundDefinableFunction M f)
    (params : Fin n → ZFSet.{u}) (A z : ZFSet.{u}) :
    z ∈ defined.graph params A ↔ ∃ x ∈ A, z = ZFSet.pair x (f (extend x params)) := by
  rw [graph, mem_familyCodeGraph]
  constructor
  · rintro ⟨x, equal⟩
    exact ⟨x.val, x.property, equal.symm⟩
  · rintro ⟨x, hx, equal⟩
    exact ⟨⟨x, hx⟩, equal.symm⟩

theorem pair_mem_graph (defined : GroundDefinableFunction M f)
    (params : Fin n → ZFSet.{u}) (A x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ defined.graph params A ↔ x ∈ A ∧ y = f (extend x params) := by
  rw [mem_graph]
  constructor
  · rintro ⟨w, hw, equal⟩
    obtain ⟨rfl, value⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hw, value⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem graph_function (defined : GroundDefinableFunction M f)
    (params : Fin n → ZFSet.{u}) (A : ZFSet.{u}) :
    FunctionGraphOn A (defined.graph params A) := by
  have equal : ZFSet.range (fun x : A => x.val) = A := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨w, equal⟩
      exact equal ▸ w.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  simpa only [graph, equal] using familyCodeGraph_function (fun x : A => x.val)
    (fun x => f (extend x.val params)) Subtype.val_injective

def graphPairFormula (formula : SetFormula ((n + 1) + 1)) : SetFormula (n + 2) :=
  .ex (.conj (SetFormula.reindex (extend 0 (extend 1 (fun j : Fin n => j.succ.succ.succ))) formula)
    (orderedPairFormula 2 1 0))

theorem realize_graphPairFormula (defined : GroundDefinableFunction M f)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (params : Fin n → ZFSet.{u}) (members : ∀ j, params j ∈ M.sets)
    {x z : ZFSet.{u}} (hx : x ∈ M.sets) (hz : z ∈ M.sets) :
    Realize M.sets (graphPairFormula defined.formula) (extend x (extend z params)) ↔
      z = ZFSet.pair x (f (extend x params)) := by
  rw [graphPairFormula, realize_ex]
  constructor
  · rintro ⟨y, hy, formula, pair⟩
    rw [realize_reindex, map_extend, map_extend] at formula
    have value := (defined.correct (extend x params) (Fin.cases hx members) y hy).1 formula
    have output := (M.realize_orderedPairFormula pairing 2 1 0 _ hz hx hy).1 pair
    exact value ▸ output
  · intro equal
    have hy := defined.closed (extend x params) (Fin.cases hx members)
    refine ⟨f (extend x params), hy, ?_,
      (M.realize_orderedPairFormula pairing 2 1 0 _ hz hx hy).2 equal⟩
    rw [realize_reindex, map_extend, map_extend]
    exact (defined.correct (extend x params) (Fin.cases hx members) _ hy).2 rfl

theorem graph_mem (defined : GroundDefinableFunction M f)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (params : Fin n → ZFSet.{u}) (members : ∀ j, params j ∈ M.sets)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) : defined.graph params A ∈ M.sets := by
  apply M.definable_image_mem separation collection (graphPairFormula defined.formula) params members hA
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := (defined.mem_graph params A z).1 hz
    exact M.orderedPair_mem pairing (M.transitive hA hx)
      (defined.closed (extend x params) (Fin.cases (M.transitive hA hx) members))
  · intro z hz
    rw [mem_graph]
    exact exists_congr (fun x => and_congr_right (fun hx =>
      (defined.realize_graphPairFormula pairing params members (M.transitive hA hx) hz).symm))
  · intro x hx y hy z hz first second
    exact ((defined.realize_graphPairFormula pairing params members (M.transitive hA hx) hy).1 first).trans
      ((defined.realize_graphPairFormula pairing params members (M.transitive hA hx) hz).1 second).symm

end GroundDefinableFunction
end




section
open SetRealization SetFormula
universe u

namespace SetFormula
private def orbitCodeEntryFormula : SetFormula 6 :=
  ex (binaryApplication orbitImageFormula
    (extend 2 (extend 4 (extend 5 (extend 6 Fin.elim0)))) 0 1)

private def orbitCodeEqualityFormula : SetFormula 5 :=
  exactSetFormula 1 orbitCodeEntryFormula

private def orbitCodeFamilyPairFormula : SetFormula 5 :=
  ex (.conj (binaryApplication orbitCodeEqualityFormula
    (extend 3 (extend 4 (extend 5 Fin.elim0))) 1 0) (orderedPairFormula 2 1 0))
end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
include pairing unions powers separation collection carrier group maps

private theorem orbitCodeEntry_meaning (W O y : ZFSet.{u}) (hy : y ∈ M.sets) :
    Realize M.sets orbitCodeEntryFormula
      (extend y (extend W (extend O (extend s.carrier (extend t.carrier
        (extend (a.conditionMapFamily s t) Fin.elim0)))))) ↔
      y ∈ a.orbitCodes s (M.nameDomain s) W := by
  rw [orbitCodeEntryFormula, realize_ex]
  constructor
  · rintro ⟨z, hz, relation⟩
    simp only [realize_binaryApplication, map_extend, map_empty] at relation
    change Realize M.sets orbitImageFormula (extend z (extend y (orbitParameters a s t W))) at relation
    obtain ⟨g, sigma, member, _shape, value⟩ :=
      (M.realize_orbitImageFormula a s t pairing unions powers separation collection carrier group maps
        W z y hz hy).1 relation
    exact (a.mem_orbitCodes s (M.nameDomain s) W y).2 ⟨g, sigma.val, sigma.property, member, value⟩
  · intro member
    obtain ⟨g, sigma, ground, inW, value⟩ := (a.mem_orbitCodes s (M.nameDomain s) W y).1 member
    let z := ZFSet.pair (t.encode g) sigma.val
    have hz : z ∈ M.sets := M.orderedPair_mem pairing (M.transitive group (t.encode_mem g)) ground
    refine ⟨z, hz, ?_⟩
    simp only [realize_binaryApplication, map_extend, map_empty]
    change Realize M.sets orbitImageFormula (extend z (extend y (orbitParameters a s t W)))
    exact (M.realize_orbitImageFormula a s t pairing unions powers separation collection carrier group maps
      W z y hz hy).2 ⟨g, ⟨sigma, ground⟩, inW, rfl, value⟩

private theorem orbitCodeEquality_meaning (W O : ZFSet.{u}) (hW : W ∈ M.sets) (hO : O ∈ M.sets) :
    Realize M.sets orbitCodeEqualityFormula
      (extend W (extend O (extend s.carrier (extend t.carrier
        (extend (a.conditionMapFamily s t) Fin.elim0))))) ↔
      O = a.orbitCodes s (M.nameDomain s) W := by
  have ground := M.orbitCodes_mem a s t pairing unions powers separation collection carrier group maps W hW
  exact M.realize_exactSetFormula 1 orbitCodeEntryFormula _ hO
    (fun z member => M.transitive ground member)
    (fun z hz => orbitCodeEntry_meaning M a s t pairing unions powers separation collection carrier group maps W O z hz)

private theorem orbitCodeFamilyPair_meaning (W z : ZFSet.{u}) (hW : W ∈ M.sets) (hz : z ∈ M.sets) :
    Realize M.sets orbitCodeFamilyPairFormula
      (extend W (extend z (extend s.carrier (extend t.carrier
        (extend (a.conditionMapFamily s t) Fin.elim0))))) ↔
      z = ZFSet.pair W (a.orbitCodes s (M.nameDomain s) W) := by
  rw [orbitCodeFamilyPairFormula, realize_ex]
  constructor
  · rintro ⟨O, hO, equality, pair⟩
    simp only [realize_binaryApplication, map_extend, map_empty] at equality
    change Realize M.sets orbitCodeEqualityFormula
      (extend W (extend O (extend s.carrier (extend t.carrier
        (extend (a.conditionMapFamily s t) Fin.elim0))))) at equality
    have value := (orbitCodeEquality_meaning M a s t pairing unions powers separation collection
      carrier group maps W O hW hO).1 equality
    have shape := (M.realize_orderedPairFormula pairing 2 1 0 _ hz hW hO).1 pair
    exact shape.trans (congrArg (ZFSet.pair W) value)
  · intro equal
    have hO := M.orbitCodes_mem a s t pairing unions powers separation collection carrier group maps W hW
    refine ⟨a.orbitCodes s (M.nameDomain s) W, hO, ?_, ?_⟩
    · simp only [realize_binaryApplication, map_extend, map_empty]
      change Realize M.sets orbitCodeEqualityFormula
        (extend W (extend (a.orbitCodes s (M.nameDomain s) W) (extend s.carrier
          (extend t.carrier (extend (a.conditionMapFamily s t) Fin.elim0)))))
      exact (orbitCodeEquality_meaning M a s t pairing unions powers separation collection
        carrier group maps W _ hW hO).2 rfl
    · exact (M.realize_orderedPairFormula pairing 2 1 0 _ hz hW hO).2 equal

omit pairing unions powers separation collection carrier group maps in
noncomputable def orbitCodeFamily (F : ZFSet.{u}) : ZFSet.{u} :=
  familyCodeGraph (fun W : F => W.val) (fun W => a.orbitCodes s (M.nameDomain s) W.val)

omit pairing unions powers separation collection carrier group maps in
theorem mem_orbitCodeFamily (F z : ZFSet.{u}) :
    z ∈ M.orbitCodeFamily a s F ↔ ∃ W ∈ F, z = ZFSet.pair W (a.orbitCodes s (M.nameDomain s) W) := by
  rw [orbitCodeFamily, mem_familyCodeGraph]
  constructor
  · rintro ⟨W, equal⟩
    exact ⟨W.val, W.property, equal.symm⟩
  · rintro ⟨W, member, equal⟩
    exact ⟨⟨W, member⟩, equal.symm⟩

omit pairing unions powers separation collection carrier group maps in
theorem orbitCodeFamily_function (F : ZFSet.{u}) : FunctionGraphOn F (M.orbitCodeFamily a s F) := by
  have domain : ZFSet.range (fun W : F => W.val) = F := by
    apply ZFSet.ext
    intro W
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨V, rfl⟩
      exact V.property
    · intro member
      exact ⟨⟨W, member⟩, rfl⟩
  simpa only [orbitCodeFamily, domain] using familyCodeGraph_function (fun W : F => W.val)
    (fun W => a.orbitCodes s (M.nameDomain s) W.val) Subtype.val_injective

theorem orbitCodeFamily_mem {F : ZFSet.{u}} (hF : F ∈ M.sets) : M.orbitCodeFamily a s F ∈ M.sets := by
  let params := extend s.carrier (extend t.carrier (extend (a.conditionMapFamily s t) Fin.elim0))
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases carrier (Fin.cases group (Fin.cases maps (fun j => Fin.elim0 j)))
  apply M.definable_image_mem separation collection orbitCodeFamilyPairFormula params members hF
  · intro z member
    obtain ⟨W, inF, rfl⟩ := (M.mem_orbitCodeFamily a s F z).1 member
    have hW := M.transitive hF inF
    exact M.orderedPair_mem pairing hW
      (M.orbitCodes_mem a s t pairing unions powers separation collection carrier group maps W hW)
  · intro z hz
    rw [M.mem_orbitCodeFamily]
    exact exists_congr (fun W => and_congr_right (fun inF =>
      (orbitCodeFamilyPair_meaning M a s t pairing unions powers separation collection
        carrier group maps W z (M.transitive hF inF) hz).symm))
  · intro W inF y hy z hz first second
    exact ((orbitCodeFamilyPair_meaning M a s t pairing unions powers separation collection
      carrier group maps W y (M.transitive hF inF) hy).1 first).trans
      ((orbitCodeFamilyPair_meaning M a s t pairing unions powers separation collection
        carrier group maps W z (M.transitive hF inF) hz).1 second).symm

end TransitiveGround
end



section
open SetFormula
universe u
namespace GroundDefinableFunction

def graphCodeFormula {n : Nat} (formula : SetFormula (n + 2)) : SetFormula (n + 2) :=
  exactSetFormula 0 (.ex (.conj (.mem 0 3)
    (SetFormula.reindex (extend 0 (extend 1 (fun j : Fin n => j.succ.succ.succ.succ)))
      (graphPairFormula formula))))

variable {M : TransitiveGround.{u}} {n : Nat}
variable {f : (Fin (n + 1) → ZFSet.{u}) → ZFSet.{u}}

noncomputable def definable_graph (defined : GroundDefinableFunction M f)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin (n + 1) → ZFSet.{u} =>
      defined.graph (fun j => env j.succ) (env 0)) where
  formula := graphCodeFormula defined.formula
  closed := fun env members => defined.graph_mem pairing separation collection
    (fun j => env j.succ) (fun j => members j.succ) (members 0)
  correct := by
    intro env members z hz
    apply M.realize_exactSetFormula 0 _ (extend z env) hz
    · intro w hw
      exact M.transitive (defined.graph_mem pairing separation collection
        (fun j => env j.succ) (fun j => members j.succ) (members 0)) hw
    · intro w hw
      rw [realize_ex]
      change (∃ x ∈ M.sets, x ∈ env 0 ∧ Realize M.sets
        (SetFormula.reindex (extend 0 (extend 1 (fun j : Fin n => j.succ.succ.succ.succ)))
          (graphPairFormula defined.formula)) (extend x (extend w (extend z env)))) ↔ _
      rw [defined.mem_graph]
      constructor
      · rintro ⟨x, hx, member, formula⟩
        rw [realize_reindex, map_extend, map_extend] at formula
        exact ⟨x, member, (defined.realize_graphPairFormula pairing (fun j => env j.succ)
          (fun j => members j.succ) hx hw).1 formula⟩
      · rintro ⟨x, member, equal⟩
        have hx := M.transitive (members 0) member
        refine ⟨x, hx, member, ?_⟩
        rw [realize_reindex, map_extend, map_extend]
        exact (defined.realize_graphPairFormula pairing (fun j => env j.succ)
          (fun j => members j.succ) hx hw).2 equal

end GroundDefinableFunction
end



open SetRealization SetFormula
universe u
namespace Name
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

noncomputable def refinementClassGraph (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (R : Name s)
    (W : ZFSet.{u}) (validW : ∀ z ∈ W, IsName s z) : ZFSet.{u} :=
  familyCodeGraph (fun w : W => w.val)
    (fun w => (refinementClass T valid R ⟨w.val, validW w.val w.property⟩).val)

theorem mem_refinementClassGraph (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (R : Name s)
    (W : ZFSet.{u}) (validW : ∀ z ∈ W, IsName s z) (x : ZFSet.{u}) :
    x ∈ refinementClassGraph T valid R W validW ↔
      ∃ w : Name s, w.val ∈ W ∧ x = ZFSet.pair w.val (refinementClass T valid R w).val := by
  rw [refinementClassGraph, mem_familyCodeGraph]
  constructor
  · rintro ⟨w, equal⟩
    exact ⟨⟨w.val, validW w.val w.property⟩, w.property, equal.symm⟩
  · rintro ⟨w, member, equal⟩
    exact ⟨⟨w.val, member⟩, equal.symm⟩

theorem pair_mem_refinementClassGraph (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (R : Name s)
    (W : ZFSet.{u}) (validW : ∀ z ∈ W, IsName s z) (w : Name s) (y : ZFSet.{u}) :
    ZFSet.pair w.val y ∈ refinementClassGraph T valid R W validW ↔
      w.val ∈ W ∧ y = (refinementClass T valid R w).val := by
  rw [mem_refinementClassGraph]
  constructor
  · rintro ⟨z, member, equal⟩
    obtain ⟨same, value⟩ := ZFSet.pair_inj.1 equal
    have named : w = z := Subtype.ext same
    cases named
    exact ⟨member, value⟩
  · rintro ⟨member, equal⟩
    exact ⟨w, member, congrArg (ZFSet.pair w.val) equal⟩

theorem refinementClassGraph_function (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (R : Name s)
    (W : ZFSet.{u}) (validW : ∀ z ∈ W, IsName s z) :
    FunctionGraphOn W (refinementClassGraph T valid R W validW) := by
  have domain : ZFSet.range (fun w : W => w.val) = W := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨w, equal⟩
      exact equal ▸ w.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  simpa only [refinementClassGraph, domain] using
    familyCodeGraph_function (fun w : W => w.val)
      (fun w => (refinementClass T valid R ⟨w.val, validW w.val w.property⟩).val)
      Subtype.val_injective

end Name

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)

theorem refinementClassGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {T W : ZFSet.{u}} (hT : T ∈ M.sets) (hW : W ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (validW : ∀ z ∈ W, IsName s z)
    (R : Name s) (hR : R.val ∈ M.sets) :
    Name.refinementClassGraph T valid R W validW ∈ M.sets := by
  let B := ZFSet.prod T s.carrier
  have hB := M.prod_mem pairing unions powers separation hT carrier
  let slots : Fin 7 → Fin 7 := ![1, 2, 3, 0, 4, 5, 6]
  let defined := (M.definable_separation separation refinementClassEntryFormula).reindex slots
  let params := extend B (extend T (extend R.val
    (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))
  have whole := defined.graph_mem pairing separation collection params
    (Fin.cases hB (Fin.cases hT (Fin.cases hR (Fin.cases carrier
      (Fin.cases order (Fin.cases (M.transitive carrier (s.encode_mem ⊤))
        (fun j => Fin.elim0 j))))))) hW
  have value (w : Name s) (hw : w.val ∈ W) :
      ZFSet.sep (fun x => Realize M.sets refinementClassEntryFormula
        (extend x (fun j => (extend w.val params) (slots j.succ))))
        ((extend w.val params) (slots 0)) = (Name.refinementClass T valid R w).val := by
    have args : (fun j : Fin 6 => (extend w.val params) (slots j.succ)) =
        extend T (extend R.val (extend w.val
          (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0))))) := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) j
    rw [args]
    exact (M.refinementClass_eq_selection s pairing unions powers separation collection
      carrier order hT valid R w hR (M.transitive hW hw)).symm
  have equal : defined.graph params W = Name.refinementClassGraph T valid R W validW := by
    apply ZFSet.ext
    intro x
    rw [defined.mem_graph, Name.mem_refinementClassGraph]
    constructor
    · rintro ⟨z, hz, equal⟩
      let w : Name s := ⟨z, validW z hz⟩
      exact ⟨w, hz, equal.trans (congrArg (ZFSet.pair z) (value w hz))⟩
    · rintro ⟨w, hw, equal⟩
      exact ⟨w.val, hw, equal.trans (congrArg (ZFSet.pair w.val) (value w hw).symm)⟩
  exact equal ▸ whole

end TransitiveGround




noncomputable def orderedPairNameGraph (one W f g : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ w ∈ W, ∃ a b, ZFSet.pair w a ∈ f ∧ ZFSet.pair w b ∈ g ∧
    x = ZFSet.pair w (orderedPairNameCode one a b))
    (ZFSet.prod W (orderedPairNameFamily one (functionGraphRange W f) (functionGraphRange W g)))

theorem mem_orderedPairNameGraph (one W f g x : ZFSet.{u}) :
    x ∈ orderedPairNameGraph one W f g ↔
      ∃ w ∈ W, ∃ a b, ZFSet.pair w a ∈ f ∧ ZFSet.pair w b ∈ g ∧
        x = ZFSet.pair w (orderedPairNameCode one a b) := by
  rw [orderedPairNameGraph, ZFSet.mem_sep]
  refine ⟨And.right, ?_⟩
  intro h
  rcases h with ⟨w, hw, a, b, ha, hb, rfl⟩
  exact ⟨ZFSet.pair_mem_prod.2 ⟨hw, (mem_orderedPairNameFamily _ _ _ _).2
    ⟨a, (mem_functionGraphRange W f a).2 ⟨w, hw, ha⟩,
      b, (mem_functionGraphRange W g b).2 ⟨w, hw, hb⟩, rfl⟩⟩,
      ⟨w, hw, a, b, ha, hb, rfl⟩⟩

namespace SetFormula

def orderedPairNameGraphEntryFormula : SetFormula 5 :=
  ex (ex (ex (ex (.conj (.mem 3 5)
    (.conj (pairMembershipFormula 3 2 6) (.conj (pairMembershipFormula 3 1 7)
      (.conj (orderedPairNameCodeFormula 0 2 1 8) (orderedPairFormula 4 3 0))))))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_orderedPairNameGraphEntryFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (env : Fin 5 → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets orderedPairNameGraphEntryFormula env ↔
      env 0 ∈ orderedPairNameGraph (env 4) (env 1) (env 2) (env 3) := by
  rw [orderedPairNameGraphEntryFormula, realize_ex, mem_orderedPairNameGraph]
  constructor
  · rintro ⟨w, hw, rest⟩
    obtain ⟨a, ha, rest⟩ := (realize_ex M.sets _ _).1 rest
    obtain ⟨b, hb, rest⟩ := (realize_ex M.sets _ _).1 rest
    obtain ⟨v, hv, member, left, right, pairName, pair⟩ := (realize_ex M.sets _ _).1 rest
    have all : ∀ j, extend v (extend b (extend a (extend w env))) j ∈ M.sets :=
      Fin.cases hv (Fin.cases hb (Fin.cases ha (Fin.cases hw members)))
    have l := (M.realize_pairMembershipFormula pairing 3 2 6 _ hw ha (members 2)).1 left
    have r := (M.realize_pairMembershipFormula pairing 3 1 7 _ hw hb (members 3)).1 right
    have named := (M.realize_orderedPairNameCodeFormula pairing 0 2 1 8 _ all).1 pairName
    have equal := (M.realize_orderedPairFormula pairing 4 3 0 _ (members 0) hw hv).1 pair
    exact ⟨w, member, a, b, l, r, equal.trans (congrArg (ZFSet.pair w) named)⟩
  · rintro ⟨w, hw, a, b, left, right, equal⟩
    have hwM := M.transitive (members 1) hw
    have ha := M.pair_right (M.transitive (members 2) left)
    have hb := M.pair_right (M.transitive (members 3) right)
    have hv := M.orderedPairNameCode_mem pairing (members 4) ha hb
    refine ⟨w, hwM, ?_⟩
    rw [realize_ex]
    refine ⟨a, ha, ?_⟩
    rw [realize_ex]
    refine ⟨b, hb, ?_⟩
    rw [realize_ex]
    refine ⟨orderedPairNameCode (env 4) a b, hv, hw, ?_, ?_, ?_, ?_⟩
    · exact (M.realize_pairMembershipFormula pairing 3 2 6 _ hwM ha (members 2)).2 left
    · exact (M.realize_pairMembershipFormula pairing 3 1 7 _ hwM hb (members 3)).2 right
    · exact (M.realize_orderedPairNameCodeFormula pairing 0 2 1 8 _
        (Fin.cases hv (Fin.cases hb (Fin.cases ha (Fin.cases hwM members))))).2 rfl
    · exact (M.realize_orderedPairFormula pairing 4 3 0 _ (members 0) hwM hv).2 equal

theorem orderedPairNameGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {one W f g : ZFSet.{u}} (hone : one ∈ M.sets) (hW : W ∈ M.sets)
    (hf : f ∈ M.sets) (hg : g ∈ M.sets) : orderedPairNameGraph one W f g ∈ M.sets := by
  have bound := M.prod_mem pairing unions powers separation hW
    (M.orderedPairNameFamily_mem pairing unions powers separation hone
      (M.functionGraphRange_mem unions separation hW hf) (M.functionGraphRange_mem unions separation hW hg))
  let params := extend W (extend f (extend g (extend one Fin.elim0)))
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases hW (Fin.cases hf (Fin.cases hg (Fin.cases hone (fun j => Fin.elim0 j))))
  have selected := M.separation_mem separation orderedPairNameGraphEntryFormula params members bound
  have equal : ZFSet.sep (fun x => Realize M.sets orderedPairNameGraphEntryFormula (extend x params))
      (ZFSet.prod W (orderedPairNameFamily one (functionGraphRange W f) (functionGraphRange W g))) =
      orderedPairNameGraph one W f g := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hx, formula⟩
      exact (M.realize_orderedPairNameGraphEntryFormula pairing _
        (Fin.cases (M.transitive bound hx) members)).1 formula
    · intro member
      have hx := (ZFSet.mem_sep.1 member).1
      exact ⟨hx, (M.realize_orderedPairNameGraphEntryFormula pairing _
        (Fin.cases (M.transitive bound hx) members)).2 member⟩
  exact equal ▸ selected

end TransitiveGround

namespace Name
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

noncomputable def refinementPairClassGraph (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (Rf Rc : Name s)
    (W : ZFSet.{u}) (validW : ∀ z ∈ W, IsName s z) : ZFSet.{u} :=
  orderedPairNameGraph (s.encode ⊤) W
    (refinementClassGraph T valid Rf W validW) (refinementClassGraph T valid Rc W validW)

theorem pair_mem_refinementPairClassGraph (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (Rf Rc : Name s)
    (W : ZFSet.{u}) (validW : ∀ z ∈ W, IsName s z) (w : Name s) (y : ZFSet.{u}) :
    ZFSet.pair w.val y ∈ refinementPairClassGraph T valid Rf Rc W validW ↔
      w.val ∈ W ∧ y = (orderedPair ⊤ (refinementClass T valid Rf w) (refinementClass T valid Rc w)).val := by
  rw [refinementPairClassGraph, mem_orderedPairNameGraph]
  constructor
  · rintro ⟨x, hx, a, b, left, right, equal⟩
    obtain ⟨same, value⟩ := ZFSet.pair_inj.1 equal
    rw [← same] at hx left right
    obtain ⟨_, rfl⟩ := (pair_mem_refinementClassGraph T valid Rf W validW w a).1 left
    obtain ⟨_, rfl⟩ := (pair_mem_refinementClassGraph T valid Rc W validW w b).1 right
    exact ⟨hx, value.trans (orderedPair_code ⊤ _ _).symm⟩
  · rintro ⟨hw, equal⟩
    exact ⟨w.val, hw, _, _,
      (pair_mem_refinementClassGraph T valid Rf W validW w _).2 ⟨hw, rfl⟩,
      (pair_mem_refinementClassGraph T valid Rc W validW w _).2 ⟨hw, rfl⟩,
      congrArg (ZFSet.pair w.val) (equal.trans (orderedPair_code ⊤ _ _))⟩

end Name

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]

theorem refinementPairClassGraph_mem (s : Presentation P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {T W : ZFSet.{u}} (hT : T ∈ M.sets) (hW : W ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (validW : ∀ z ∈ W, IsName s z)
    (Rf Rc : Name s) (hRf : Rf.val ∈ M.sets) (hRc : Rc.val ∈ M.sets) :
    Name.refinementPairClassGraph T valid Rf Rc W validW ∈ M.sets :=
  M.orderedPairNameGraph_mem pairing unions powers separation
    (M.transitive carrier (s.encode_mem ⊤)) hW
    (M.refinementClassGraph_mem s pairing unions powers separation collection carrier order hT hW valid validW Rf hRf)
    (M.refinementClassGraph_mem s pairing unions powers separation collection carrier order hT hW valid validW Rc hRc)

end TransitiveGround


end PartitionPilot.Forcing

end OAI
