import OAI.SetTheory.PartitionPrinciple.Definability.ExternalGroupOperationGraphs

namespace OAI

namespace PartitionPilot.Forcing

open SetRealization SetFormula
universe u

noncomputable def externalActorSymbolGraph (G S : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ g ∈ G, ∃ a ∈ externalGeneratorAlphabet G S,
    z = ZFSet.pair g a ∧ a = externalActorSymbol g)
    (ZFSet.prod G (externalGeneratorAlphabet G S))

noncomputable def externalGeneratorSymbolGraph (G S : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ s ∈ S, ∃ a ∈ externalGeneratorAlphabet G S,
    z = ZFSet.pair s a ∧ a = externalLetterSymbol s true)
    (ZFSet.prod S (externalGeneratorAlphabet G S))

theorem pair_mem_externalActorSymbolGraph (G S g a : ZFSet.{u}) :
    ZFSet.pair g a ∈ externalActorSymbolGraph G S ↔ g ∈ G ∧ a = externalActorSymbol g := by
  constructor
  · intro h
    obtain ⟨_, g', hg, a', _, eq, value⟩ := ZFSet.mem_sep.1 h
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hg, value⟩
  · rintro ⟨hg, rfl⟩
    have ha := (externalActorSymbol_mem G S g).2 hg
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hg, ha⟩, g, hg, _, ha, rfl, rfl⟩

theorem pair_mem_externalGeneratorSymbolGraph (G S s a : ZFSet.{u}) :
    ZFSet.pair s a ∈ externalGeneratorSymbolGraph G S ↔ s ∈ S ∧ a = externalLetterSymbol s true := by
  constructor
  · intro h
    obtain ⟨_, s', hs, a', _, eq, value⟩ := ZFSet.mem_sep.1 h
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hs, value⟩
  · rintro ⟨hs, rfl⟩
    have ha := (externalLetterSymbol_mem G S s true).2 hs
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hs, ha⟩, s, hs, _, ha, rfl, rfl⟩

theorem externalActorSymbolGraph_eq_graph {J L : Type u} (s : Presentation J) (t : Presentation L) :
    externalActorSymbolGraph s.carrier t.carrier = s.graph
      (externalGeneratorAlphabetPresentation s t) Sum.inl := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph]
  constructor
  · intro hz
    obtain ⟨g, hg, a, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).1
    have value := ((pair_mem_externalActorSymbolGraph _ _ g a).1 hz).2
    obtain ⟨g, rfl⟩ := (s.mem_carrier g).1 hg
    exact ⟨g, congrArg (ZFSet.pair (s.encode g)) value.symm⟩
  · rintro ⟨g, rfl⟩
    exact (pair_mem_externalActorSymbolGraph _ _ _ _).2 ⟨s.encode_mem g, rfl⟩

theorem externalGeneratorSymbolGraph_eq_graph {J L : Type u}
    (s : Presentation J) (t : Presentation L) :
    externalGeneratorSymbolGraph s.carrier t.carrier = t.graph
      (externalGeneratorAlphabetPresentation s t) (fun a => Sum.inr (a, true)) := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph]
  constructor
  · intro hz
    obtain ⟨l, hl, a, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).1
    have value := ((pair_mem_externalGeneratorSymbolGraph _ _ l a).1 hz).2
    obtain ⟨l, rfl⟩ := (t.mem_carrier l).1 hl
    exact ⟨l, congrArg (ZFSet.pair (t.encode l)) value.symm⟩
  · rintro ⟨l, rfl⟩
    exact (pair_mem_externalGeneratorSymbolGraph _ _ _ _).2 ⟨t.encode_mem l, rfl⟩

namespace BoundedFormula

def externalActorSymbolEntryFormula {n} (z G alphabet zero : Fin n) : BoundedFormula n :=
  exMem G (exMem alphabet.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (orderedPairFormula 0 zero.succ.succ 1)))

theorem truth_externalActorSymbolEntryFormula {n} (z G alphabet zero : Fin n)
    (env : Fin n → ZFSet.{u}) (hZero : env zero = natSetCode 0) :
    Truth (externalActorSymbolEntryFormula z G alphabet zero) env ↔
      ∃ g ∈ env G, ∃ a ∈ env alphabet, env z = ZFSet.pair g a ∧ a = externalActorSymbol g := by
  simp only [externalActorSymbolEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  change (∃ g ∈ env G, ∃ a ∈ env alphabet, env z = ZFSet.pair g a ∧
    a = ZFSet.pair (env zero) g) ↔ _
  rw [hZero]
  rfl

def externalGeneratorSymbolEntryFormula {n} (z S alphabet one : Fin n) : BoundedFormula n :=
  exMem S (exMem alphabet.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (orderedRightTripleFormula 0 one.succ.succ 1 one.succ.succ)))

theorem truth_externalGeneratorSymbolEntryFormula {n} (z S alphabet one : Fin n)
    (env : Fin n → ZFSet.{u}) (hOne : env one = natSetCode 1) :
    Truth (externalGeneratorSymbolEntryFormula z S alphabet one) env ↔
      ∃ s ∈ env S, ∃ a ∈ env alphabet, env z = ZFSet.pair s a ∧ a = externalLetterSymbol s true := by
  simp only [externalGeneratorSymbolEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_orderedRightTripleFormula]
  change (∃ s ∈ env S, ∃ a ∈ env alphabet, env z = ZFSet.pair s a ∧
    a = ZFSet.pair (env one) (ZFSet.pair s (env one))) ↔ _
  rw [hOne]
  rfl

end BoundedFormula

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem externalActorSymbolGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {G S : ZFSet.{u}} (hG : G ∈ M.sets) (hS : S ∈ M.sets) :
    externalActorSymbolGraph G S ∈ M.sets := by
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  have hZero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨G, hG⟩
  let params := extend G (extend (externalGeneratorAlphabet G S) (extend (natSetCode 0) Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalActorSymbolEntryFormula 0 1 2 3) params
    (Fin.cases hG (Fin.cases hAlphabet (Fin.cases hZero (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hG hAlphabet)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalActorSymbolEntryFormula 0 1 2 3) (extend z params))
      (ZFSet.prod G (externalGeneratorAlphabet G S)) = externalActorSymbolGraph G S := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, externalActorSymbolGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_externalActorSymbolEntryFormula 0 1 2 3 _ rfl)
  exact equal ▸ selected

theorem externalGeneratorSymbolGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {G S : ZFSet.{u}} (hG : G ∈ M.sets) (hS : S ∈ M.sets) :
    externalGeneratorSymbolGraph G S ∈ M.sets := by
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  have hZero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨G, hG⟩
  have hOne : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hZero hZero
  let params := extend S (extend (externalGeneratorAlphabet G S) (extend (natSetCode 1) Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalGeneratorSymbolEntryFormula 0 1 2 3) params
    (Fin.cases hS (Fin.cases hAlphabet (Fin.cases hOne (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hS hAlphabet)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalGeneratorSymbolEntryFormula 0 1 2 3) (extend z params))
      (ZFSet.prod S (externalGeneratorAlphabet G S)) = externalGeneratorSymbolGraph G S := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, externalGeneratorSymbolGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_externalGeneratorSymbolEntryFormula 0 1 2 3 _ rfl)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

section

namespace PartitionPilot.Forcing

open SetRealization SetFormula
universe u

noncomputable def singletonWordGraph (A W : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ A, ∃ w ∈ W, z = ZFSet.pair x w ∧ w = wordSingleton x)
    (ZFSet.prod A W)

theorem pair_mem_singletonWordGraph (A W x w : ZFSet.{u}) :
    ZFSet.pair x w ∈ singletonWordGraph A W ↔ x ∈ A ∧ w ∈ W ∧ w = wordSingleton x := by
  constructor
  · intro h
    obtain ⟨_, y, hy, v, hv, eq, value⟩ := ZFSet.mem_sep.1 h
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hy, hv, value⟩
  · rintro ⟨hx, hw, value⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hx, hw⟩, x, hx, w, hw, rfl, value⟩

namespace BoundedFormula

def singletonWordFormula {n} (w zero x : Fin n) : BoundedFormula n :=
  exMem w (.conj (orderedPairFormula 0 zero.succ x.succ) (singletonFormula w.succ 0))

theorem truth_singletonWordFormula {n} (w zero x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (singletonWordFormula w zero x) env ↔ env w = {ZFSet.pair (env zero) (env x)} := by
  simp only [singletonWordFormula, truth_exMem, Truth, truth_orderedPairFormula, truth_singletonFormula]
  change (∃ z ∈ env w, z = ZFSet.pair (env zero) (env x) ∧ env w = {z}) ↔ _
  constructor
  · rintro ⟨z, _, rfl, eq⟩
    exact eq
  · intro eq
    exact ⟨_, eq.symm ▸ ZFSet.mem_singleton.2 rfl, rfl, eq⟩

def singletonWordEntryFormula {n} (z A W zero : Fin n) : BoundedFormula n :=
  exMem A (exMem W.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (singletonWordFormula 0 zero.succ.succ 1)))

theorem truth_singletonWordEntryFormula {n} (z A W zero : Fin n)
    (env : Fin n → ZFSet.{u}) (hZero : env zero = natSetCode 0) :
    Truth (singletonWordEntryFormula z A W zero) env ↔
      ∃ x ∈ env A, ∃ w ∈ env W, env z = ZFSet.pair x w ∧ w = wordSingleton x := by
  simp only [singletonWordEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_singletonWordFormula]
  change (∃ x ∈ env A, ∃ w ∈ env W, env z = ZFSet.pair x w ∧
    w = {ZFSet.pair (env zero) x}) ↔ _
  rw [hZero]
  rfl

end BoundedFormula

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem singletonWordGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A W : ZFSet.{u}} (hA : A ∈ M.sets) (hW : W ∈ M.sets) :
    singletonWordGraph A W ∈ M.sets := by
  have hZero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨A, hA⟩
  let params := extend A (extend W (extend (natSetCode 0) Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.singletonWordEntryFormula 0 1 2 3) params
    (Fin.cases hA (Fin.cases hW (Fin.cases hZero (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hA hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.singletonWordEntryFormula 0 1 2 3) (extend z params)) (ZFSet.prod A W) =
      singletonWordGraph A W := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, singletonWordGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_singletonWordEntryFormula 0 1 2 3 _ rfl)
  exact equal ▸ selected

theorem singletonWordGraph_eq_graph
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {B : Type u} (s : Presentation B) (hA : s.carrier ∈ M.sets) :
    singletonWordGraph s.carrier (M.finiteWords s.carrier) =
      s.graph (finiteWordPresentation s M pairing unions separation infinite hA) (fun x => [x]) := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph]
  constructor
  · intro hz
    obtain ⟨x, hx, w, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).1
    have value := ((pair_mem_singletonWordGraph _ _ x w).1 hz).2.2
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    exact ⟨x, congrArg (ZFSet.pair (s.encode x)) ((finiteWordGraph_singleton s x).trans value.symm)⟩
  · rintro ⟨x, rfl⟩
    exact (pair_mem_singletonWordGraph _ _ _ _).2 ⟨s.encode_mem x,
      finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hA [x],
      finiteWordGraph_singleton s x⟩

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.SetRealization.Presentation

open Forcing
universe u

theorem relationCompose_graph {A B C : Type u}
    (s : Presentation A) (t : Presentation B) (v : Presentation C) (f : A → B) (g : B → C) :
    relationCompose s.carrier t.carrier v.carrier (s.graph t f) (t.graph v g) =
      s.graph v (fun x => g (f x)) := by
  apply ZFSet.ext
  intro z
  rw [mem_relationCompose, mem_graph]
  constructor
  · rintro ⟨x, hx, y, hy, w, hw, rfl, first, second⟩
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (t.mem_carrier y).1 hy
    obtain ⟨c, rfl⟩ := (v.mem_carrier w).1 hw
    have ab := (s.pair_mem_graph t f a b).1 first
    have bc := (t.pair_mem_graph v g b c).1 second
    subst b c
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨s.encode a, s.encode_mem a, t.encode (f a), t.encode_mem (f a),
      v.encode (g (f a)), v.encode_mem (g (f a)), rfl,
      (s.pair_mem_graph t f a (f a)).2 rfl,
      (t.pair_mem_graph v g (f a) (g (f a))).2 rfl⟩

end PartitionPilot.SetRealization.Presentation

end

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

structure GroundExternalGroupData (M : TransitiveGround.{u}) (G S m inv one : ZFSet.{u}) : Prop where
  carrier_mem : M.externalGroupCarrier G S m one ∈ M.sets
  multiplication_mem : M.externalGroupMultiplication G S m one ∈ M.sets
  inverse_mem : M.externalGroupInverse G S m inv one ∈ M.sets
  identity_mem : M.externalGroupIdentity G S m one ∈ M.sets
  projection_mem : M.externalGroupProjection G S m one ∈ M.sets
  group_code : GroupCode (M.externalGroupCarrier G S m one)
    (M.externalGroupMultiplication G S m one) (M.externalGroupInverse G S m inv one)
    (M.externalGroupIdentity G S m one)

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

include pairing unions powers separation infinite in
theorem externalGroup_code_of_presentation {J L : Type u} [Group J]
    (s : Presentation J) (t : Presentation L)
    (hG : s.carrier ∈ M.sets) (hS : t.carrier ∈ M.sets) :
    GroupCode
      (M.externalGroupCarrier s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1))
      (M.externalGroupMultiplication s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1))
      (M.externalGroupInverse s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2))
        (s.graph s Inv.inv) (s.encode 1))
      (M.externalGroupIdentity s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1)) := by
  rw [M.externalGroupMultiplication_eq_graph pairing unions powers separation infinite s t hG hS,
    M.externalGroupInverse_eq_graph pairing unions powers separation infinite s t hG hS,
    M.externalGroupIdentity_eq_encode pairing unions powers separation infinite s t hG hS]
  exact (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS).groupCode

include pairing unions powers separation infinite in
theorem externalGroup_code {G S m inv one : ZFSet.{u}} (group : GroupCode G m inv one)
    (hG : G ∈ M.sets) (hS : S ∈ M.sets) :
    GroupCode (M.externalGroupCarrier G S m one) (M.externalGroupMultiplication G S m one)
      (M.externalGroupInverse G S m inv one) (M.externalGroupIdentity G S m one) := by
  let := group.toGroup
  have code := M.externalGroup_code_of_presentation pairing unions powers separation infinite
    (SetMembers.presentation G) (SetMembers.presentation S) hG hS
  rw [group.multiplication_graph_eq, group.inverse_graph_eq, group.identity_code_eq] at code
  exact code

include pairing unions powers separation infinite in
theorem externalGroupData {G S m inv one : ZFSet.{u}} (group : GroupCode G m inv one)
    (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hm : m ∈ M.sets) (hInv : inv ∈ M.sets) :
    GroundExternalGroupData M G S m inv one := by
  have ground := M.externalGroupOperations_ground pairing unions powers separation infinite hG hS hm hInv
    (M.transitive hG group.identity_mem)
  exact ⟨ground.1, ground.2.1, ground.2.2.1, ground.2.2.2.1, ground.2.2.2.2,
    M.externalGroup_code pairing unions powers separation infinite group hG hS⟩

theorem GroundExternalGroupData.realize_group {G S m inv one : ZFSet.{u}}
    (data : GroundExternalGroupData M G S m inv one) :
    Realize M.sets (BoundedFormula.groupFormula 0 1 2 3).toFormula
      (extend (M.externalGroupCarrier G S m one)
        (extend (M.externalGroupMultiplication G S m one)
          (extend (M.externalGroupInverse G S m inv one)
            (extend (M.externalGroupIdentity G S m one) Fin.elim0)))) :=
  (M.realize_groupCode data.carrier_mem data.multiplication_mem data.inverse_mem data.identity_mem).2 data.group_code

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
open Compression.RecursiveMaps.CosetGeometry
universe u
variable (M : TransitiveGround.{u})

noncomputable def externalSymbolClasses (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  let alphabet := externalGeneratorAlphabet G S
  let words := M.finiteWords alphabet
  relationCompose alphabet words (M.externalGroupCarrier G S m one)
    (singletonWordGraph alphabet words) (M.externalGroupProjection G S m one)

noncomputable def externalOldInclusion (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose G (externalGeneratorAlphabet G S) (M.externalGroupCarrier G S m one)
    (externalActorSymbolGraph G S) (M.externalSymbolClasses G S m one)

noncomputable def externalChildGenerators (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose S (externalGeneratorAlphabet G S) (M.externalGroupCarrier G S m one)
    (externalGeneratorSymbolGraph G S) (M.externalSymbolClasses G S m one)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

include pairing unions powers separation infinite in
theorem externalSymbolClasses_mem {G S m one : ZFSet.{u}}
    (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hm : m ∈ M.sets) (hOne : one ∈ M.sets) :
    M.externalSymbolClasses G S m one ∈ M.sets := by
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  have hWords := M.finiteWords_mem pairing unions powers separation infinite hAlphabet
  have hE := M.externalWordEquivalence_mem pairing unions powers separation infinite hG hS hm hOne
  have hQ := M.equivalenceClasses_mem powers separation hWords hE
  have hProjection := M.equivalenceClassifier_mem pairing unions powers separation hWords hE
  exact M.relationCompose_mem pairing unions powers separation hAlphabet hWords hQ
    (M.singletonWordGraph_mem pairing unions powers separation hAlphabet hWords) hProjection

include pairing unions powers separation infinite in
theorem externalGeneratorGraphs_mem {G S m one : ZFSet.{u}}
    (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hm : m ∈ M.sets) (hOne : one ∈ M.sets) :
    M.externalOldInclusion G S m one ∈ M.sets ∧
      M.externalChildGenerators G S m one ∈ M.sets := by
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  have hWords := M.finiteWords_mem pairing unions powers separation infinite hAlphabet
  have hE := M.externalWordEquivalence_mem pairing unions powers separation infinite hG hS hm hOne
  have hQ := M.equivalenceClasses_mem powers separation hWords hE
  have hClasses := M.externalSymbolClasses_mem pairing unions powers separation infinite hG hS hm hOne
  exact ⟨M.relationCompose_mem pairing unions powers separation hG hAlphabet hQ
      (M.externalActorSymbolGraph_mem pairing unions powers separation hG hS) hClasses,
    M.relationCompose_mem pairing unions powers separation hS hAlphabet hQ
      (M.externalGeneratorSymbolGraph_mem pairing unions powers separation hG hS) hClasses⟩

variable {J L : Type u} [Group J] (s : Presentation J) (t : Presentation L)
variable (hG : s.carrier ∈ M.sets) (hS : t.carrier ∈ M.sets)

theorem externalSymbolClasses_eq_graph :
    M.externalSymbolClasses s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2))
      (s.encode 1) = (externalGeneratorAlphabetPresentation s t).graph
        (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS)
        (ExternalWordRewrite.symbolValue J L) := by
  let a := externalGeneratorAlphabetPresentation s t
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  let w := finiteWordPresentation a M pairing unions separation infinite hAlphabet
  let q := M.externalGroupPresentation pairing unions powers separation infinite s t hG hS
  unfold externalSymbolClasses externalGroupProjection
  dsimp only
  have singleton := M.singletonWordGraph_eq_graph pairing unions separation infinite a hAlphabet
  change singletonWordGraph (externalGeneratorAlphabet s.carrier t.carrier)
    (M.finiteWords (externalGeneratorAlphabet s.carrier t.carrier)) = _ at singleton
  rw [singleton, M.externalGroupClassifier_eq_graph pairing unions powers separation infinite s t hG hS]
  have composed := a.relationCompose_graph w q (fun x => [x]) (ExternalWordRewrite.evalWord J L)
  have single : (fun x : J ⊕ (L × Bool) => ExternalWordRewrite.evalWord J L [x]) =
      ExternalWordRewrite.symbolValue J L := by
    rfl
  rw [single] at composed
  exact composed

theorem externalOldInclusion_eq_graph :
    M.externalOldInclusion s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2))
      (s.encode 1) = s.graph
        (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS) (old J L) := by
  unfold externalOldInclusion
  rw [externalActorSymbolGraph_eq_graph,
    M.externalSymbolClasses_eq_graph pairing unions powers separation infinite s t hG hS]
  exact s.relationCompose_graph (externalGeneratorAlphabetPresentation s t)
    (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS)
    Sum.inl (ExternalWordRewrite.symbolValue J L)

theorem externalChildGenerators_eq_graph :
    M.externalChildGenerators s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2))
      (s.encode 1) = t.graph
        (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS) (generator J L) := by
  unfold externalChildGenerators
  rw [externalGeneratorSymbolGraph_eq_graph,
    M.externalSymbolClasses_eq_graph pairing unions powers separation infinite s t hG hS]
  exact t.relationCompose_graph (externalGeneratorAlphabetPresentation s t)
    (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS)
    (fun x => Sum.inr (x, true)) (ExternalWordRewrite.symbolValue J L)

theorem externalOldInclusion_entry_iff (g : J) (x : External J L) :
    ZFSet.pair (s.encode g)
      ((M.externalGroupPresentation pairing unions powers separation infinite s t hG hS).encode x) ∈
      M.externalOldInclusion s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1) ↔
        old J L g = x := by
  rw [M.externalOldInclusion_eq_graph pairing unions powers separation infinite s t hG hS]
  exact s.pair_mem_graph _ _ g x

theorem externalChildGenerators_entry_iff (l : L) (x : External J L) :
    ZFSet.pair (t.encode l)
      ((M.externalGroupPresentation pairing unions powers separation infinite s t hG hS).encode x) ∈
      M.externalChildGenerators s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1) ↔
        generator J L l = x := by
  rw [M.externalChildGenerators_eq_graph pairing unions powers separation infinite s t hG hS]
  exact t.pair_mem_graph _ _ l x

include pairing unions powers separation infinite hG hS in
theorem externalGeneratorGraphs_injections :
    InjectionCode s.carrier
      (M.externalGroupCarrier s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1))
      (M.externalOldInclusion s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1)) ∧
    InjectionCode t.carrier
      (M.externalGroupCarrier s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1))
      (M.externalChildGenerators s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1)) := by
  rw [M.externalOldInclusion_eq_graph pairing unions powers separation infinite s t hG hS,
    M.externalChildGenerators_eq_graph pairing unions powers separation infinite s t hG hS]
  have generatorInj : Function.Injective (generator J L) :=
    (Monoid.CoprodI.of_injective (M := Factor J L) true).comp FreeGroup.of_injective
  let q := M.externalGroupPresentation pairing unions powers separation infinite s t hG hS
  exact ⟨s.graph_injection q _ (old_injective J L), t.graph_injection q _ generatorInj⟩

include pairing unions powers separation infinite in
theorem externalGeneratorGraphs_ground_injections {G S m inv one : ZFSet.{u}}
    (group : GroupCode G m inv one) (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hm : m ∈ M.sets) :
    M.externalOldInclusion G S m one ∈ M.sets ∧
      InjectionCode G (M.externalGroupCarrier G S m one) (M.externalOldInclusion G S m one) ∧
      M.externalChildGenerators G S m one ∈ M.sets ∧
      InjectionCode S (M.externalGroupCarrier G S m one) (M.externalChildGenerators G S m one) := by
  let := group.toGroup
  have maps := M.externalGeneratorGraphs_injections pairing unions powers separation infinite
    (SetMembers.presentation G) (SetMembers.presentation S) hG hS
  rw [group.multiplication_graph_eq, group.identity_code_eq] at maps
  have ground := M.externalGeneratorGraphs_mem pairing unions powers separation infinite hG hS hm
    (M.transitive hG group.identity_mem)
  exact ⟨ground.1, maps.1, ground.2, maps.2⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
