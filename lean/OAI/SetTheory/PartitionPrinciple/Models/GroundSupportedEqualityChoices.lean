import OAI.SetTheory.PartitionPrinciple.Definability.SupportedCertificateRelations
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundProjectedRowChooserWitnesses
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundOrdinaryCountableFunctions

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

def OrdinalChoiceValue (T e x y : ZFSet.{u}) : Prop :=
  ∃ i ∈ T, ZFSet.pair i y ∈ e ∧ ∀ j ∈ i, ∀ z ∈ x, ZFSet.pair j z ∉ e

noncomputable def ordinalIndexedChoiceGraph (A T e : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ A, ∃ y ∈ x, z = ZFSet.pair x y ∧ OrdinalChoiceValue T e x y)
    (ZFSet.prod A (⋃₀ A))

theorem pair_mem_ordinalIndexedChoiceGraph (A T e x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ ordinalIndexedChoiceGraph A T e ↔
      x ∈ A ∧ y ∈ x ∧ OrdinalChoiceValue T e x y := by
  rw [ordinalIndexedChoiceGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, x', hx, y', hy, eq, least⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hx, hy, least⟩
  · rintro ⟨hx, hy, least⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, ZFSet.mem_sUnion.2 ⟨x, hx, hy⟩⟩,
      x, hx, y, hy, rfl, least⟩

theorem ordinalIndexedChoiceGraph_choice {A T e : ZFSet.{u}}
    (ordinal : ordinalSetProperty T) (function : FunctionGraphOn T e)
    (meets : ∀ x ∈ A, ∃ i ∈ T, ∃ y ∈ x, ZFSet.pair i y ∈ e) :
    ChoiceFunctionCode A (ordinalIndexedChoiceGraph A T e) := by
  obtain ⟨B, function⟩ := function
  refine ⟨⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩, ?_⟩
  · intro x hx
    let indices : Set ZFSet.{u} := {i | i ∈ T ∧ ∃ y ∈ x, ZFSet.pair i y ∈ e}
    have inhabited : indices.Nonempty := by
      obtain ⟨i, hi, y, hy, entry⟩ := meets x hx
      exact ⟨i, hi, y, hy, entry⟩
    obtain ⟨i, hi, minimal⟩ := ZFSet.mem_wf.has_min indices inhabited
    obtain ⟨hiT, y, hy, entry⟩ := hi
    have least : OrdinalChoiceValue T e x y := by
      refine ⟨i, hiT, entry, ?_⟩
      intro j hji z hz rel
      exact minimal j ⟨ordinal.1 i hiT j hji, z, hz, rel⟩ hji
    refine ⟨y, (pair_mem_ordinalIndexedChoiceGraph A T e x y).2 ⟨hx, hy, least⟩, ?_⟩
    intro z hz
    obtain ⟨_, zx, j, hjT, jz, smaller⟩ := (pair_mem_ordinalIndexedChoiceGraph A T e x z).1 hz
    rcases ordinalSetProperty_mem_compare ordinal hiT hjT with before | equal | after
    · exact False.elim (smaller i before y hy entry)
    · subst j
      obtain ⟨v, _, unique⟩ := function.2 i hiT
      exact (unique z jz).trans (unique y entry).symm
    · exact False.elim (minimal j ⟨hjT, z, zx, jz⟩ after)
  · intro x y entry
    exact ((pair_mem_ordinalIndexedChoiceGraph A T e x y).1 entry).2.1

namespace BoundedFormula

def ordinalChoiceValueFormula {n} (T e x y : Fin n) : BoundedFormula n :=
  exMem T (.conj (pairMembershipFormula 0 y.succ e.succ)
    (allMem 0 (allMem x.succ.succ (.neg (pairMembershipFormula 1 0 e.succ.succ.succ)))))

theorem truth_ordinalChoiceValueFormula {n} (T e x y : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (ordinalChoiceValueFormula T e x y) env ↔
      OrdinalChoiceValue (env T) (env e) (env x) (env y) := by
  simp only [ordinalChoiceValueFormula, truth_exMem, Truth, truth_pairMembershipFormula]
  rfl

def ordinalIndexedChoiceEntryFormula {n} (z A T e : Fin n) : BoundedFormula n :=
  exMem A (exMem 0 (.conj (orderedPairFormula z.succ.succ 1 0)
    (ordinalChoiceValueFormula T.succ.succ e.succ.succ 1 0)))

theorem truth_ordinalIndexedChoiceEntryFormula {n} (z A T e : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (ordinalIndexedChoiceEntryFormula z A T e) env ↔
      ∃ x ∈ env A, ∃ y ∈ x, env z = ZFSet.pair x y ∧ OrdinalChoiceValue (env T) (env e) x y := by
  simp only [ordinalIndexedChoiceEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_ordinalChoiceValueFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

theorem ordinalIndexedChoiceGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A T e : ZFSet.{u}} (hA : A ∈ M.sets) (hT : T ∈ M.sets) (he : e ∈ M.sets) :
    ordinalIndexedChoiceGraph A T e ∈ M.sets := by
  let env := extend A (extend T (extend e Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.ordinalIndexedChoiceEntryFormula 0 1 2 3) env
    (Fin.cases hA (Fin.cases hT (Fin.cases he (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hA (M.union_mem unions hA))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.ordinalIndexedChoiceEntryFormula 0 1 2 3) (extend z env))
      (ZFSet.prod A (⋃₀ A)) = ordinalIndexedChoiceGraph A T e := by
    apply ZFSet.ext
    intro z
    rw [ordinalIndexedChoiceGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_ordinalIndexedChoiceEntryFormula _ _ _ _ _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
universe u

theorem ordinalIndexedChoiceGraph_total {F T e : ZFSet.{u}}
    (ordinal : ordinalSetProperty T)
    (meets : ∀ R ∈ F, ∃ i ∈ T, ∃ y ∈ R, ZFSet.pair i y ∈ e) :
    ∀ R ∈ F, ∃ y ∈ ⋃₀ F, ZFSet.pair R y ∈ ordinalIndexedChoiceGraph F T e := by
  intro R hR
  let indices : Set ZFSet.{u} := {i | i ∈ T ∧ ∃ y ∈ R, ZFSet.pair i y ∈ e}
  have inhabited : indices.Nonempty := meets R hR
  obtain ⟨i, hi, minimal⟩ := ZFSet.mem_wf.has_min indices inhabited
  obtain ⟨hiT, y, hy, entry⟩ := hi
  refine ⟨y, ZFSet.mem_sUnion.2 ⟨R, hR, hy⟩,
    (pair_mem_ordinalIndexedChoiceGraph F T e R y).2 ⟨hR, hy, i, hiT, entry, ?_⟩⟩
  intro j hji z hz stored
  exact minimal j ⟨ordinal.1 i hiT j hji, z, hz, stored⟩ hji

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem exists_ordinalRelationChoice
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {A T e : ZFSet.{u}} (hA : A ∈ M.sets) (hT : T ∈ M.sets) (he : e ∈ M.sets)
    (ordinal : ordinalSetProperty T)
    (covers : ∀ x ∈ A, ∃ i ∈ T, ZFSet.pair i x ∈ e) :
    ∃ c ∈ M.sets, ChoiceFunctionCode (M.nonemptyGroundSubsets A) c ∧
      ∀ R y, ZFSet.pair R y ∈ c → OrdinalChoiceValue T e R y := by
  let F := M.nonemptyGroundSubsets A
  have hF : F ∈ M.sets := M.nonemptyGroundSubsets_mem powers separation hA
  have meets : ∀ R ∈ F, ∃ i ∈ T, ∃ y ∈ R, ZFSet.pair i y ∈ e := by
    intro R hR
    obtain ⟨_, subset, y, hy⟩ := (M.mem_nonemptyGroundSubsets A R).1 hR
    obtain ⟨i, hi, entry⟩ := covers y (subset hy)
    exact ⟨i, hi, y, hy, entry⟩
  obtain ⟨c, hc, function, selected⟩ := M.uniformize_relation pairing unions powers separation choice
    hF (M.union_mem unions hF)
    (M.ordinalIndexedChoiceGraph_mem pairing unions powers separation hF hT he)
    (ordinalIndexedChoiceGraph_total ordinal meets)
  refine ⟨c, hc, ⟨function, ?_⟩, ?_⟩
  · intro R y entry
    exact ((pair_mem_ordinalIndexedChoiceGraph F T e R y).1 (selected entry)).2.1
  · intro R y entry
    exact ((pair_mem_ordinalIndexedChoiceGraph F T e R y).1 (selected entry)).2.2

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem choice_of_witnesses
    (witnesses : ∀ A ∈ M.sets, (∀ x ∈ A, x.Nonempty) →
      ∃ f ∈ M.sets, ChoiceFunctionCode A f) :
    Realize M.sets SetFormula.choice Fin.elim0 := by
  intro A hA
  apply (realize_imp M.sets _ _ _).2
  intro premise
  have nonempty : ∀ x ∈ A, x.Nonempty := by
    have raw := (BoundedFormula.realize_toFormula M
      (BoundedFormula.allMem 0 (BoundedFormula.nonemptyFormula 0))
      (extend A Fin.elim0) (Fin.cases hA (fun i => Fin.elim0 i))).1 premise
    intro x hx
    exact (BoundedFormula.truth_nonemptyFormula 0 _).1 (raw x hx)
  obtain ⟨f, hf, code⟩ := witnesses A hA nonempty
  apply (realize_ex M.sets _ _).2
  refine ⟨f, hf, ?_⟩
  apply (BoundedFormula.realize_toFormula M _ _
    (Fin.cases hf (Fin.cases hA (fun i => Fin.elim0 i)))).2
  exact (BoundedFormula.truth_choiceFunctionFormula 1 0 _).2 code

variable {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))

include pairing unions powers separation collection infinite choice carrier order generic in
theorem ordinaryExtension_choice_witness {A : ZFSet.{u}}
    (hA : A ∈ (M.ordinaryExtension s H).sets) (nonempty : ∀ x ∈ A, x.Nonempty) :
    ∃ f ∈ (M.ordinaryExtension s H).sets, ChoiceFunctionCode A f := by
  let N := M.ordinaryExtension s H
  have zf := M.ordinaryExtension_ZF s pairing unions powers separation collection carrier order infinite H generic
  have pairingN : Realize N.sets SetFormula.pairing Fin.elim0 := zf.1.2.2.2.1
  have unionsN : Realize N.sets SetFormula.union Fin.elim0 := zf.1.2.2.2.2.1
  have powersN : Realize N.sets powerSet Fin.elim0 := zf.1.2.2.2.2.2.1
  have separationN : SeparationSchema N.sets := zf.2.1
  have hUnion := N.union_mem unionsN hA
  obtain ⟨β, hβ, value⟩ := (M.mem_ordinaryExtension s H (⋃₀ A)).1 hUnion
  have boundM := M.union_mem unions (M.union_mem unions hβ)
  have poolM := M.namePool_mem s pairing unions powers separation collection carrier boundM
  obtain ⟨T, hT, f, hf, ordinal, injection, onto⟩ :=
    M.exists_groundOrdinalEnumeration pairing unions powers separation collection choice poolM
  let function : FunctionGraphOn T f := ⟨_, injection.function⟩
  have names : ∀ i, IsName s (function.value i) := by
    intro i
    exact ((mem_namePool s _ _).1
      (ZFSet.pair_mem_prod.1 (injection.function.1 (function.value_entry i))).2).2
  let η := Name.indexedGraphName ⊤ function names
  have hη : η ∈ (M.nameDomain s).names :=
    M.indexedGraphName_mem s ⊤ pairing unions powers separation collection
      (M.transitive carrier (s.encode_mem ⊤)) hT hf function names
  let e := Name.eval {q | H.mem q} η
  have he : e ∈ N.sets := (M.mem_ordinaryExtension s H e).2 ⟨η, hη, rfl⟩
  have includes := M.ground_subset_ordinaryExtension s pairing unions powers separation collection carrier H
  have hTN : T ∈ N.sets := includes hT
  have enumeration : FunctionGraphOn T e :=
    ⟨_, Name.eval_indexedGraphName_function {q | H.mem q} ⊤ H.top_mem function names⟩
  have covers := Name.indexedGraphName_covers_eval {q | H.mem q} ⊤ H.top_mem β function names onto
  have meets : ∀ x ∈ A, ∃ i ∈ T, ∃ y ∈ x, ZFSet.pair i y ∈ e := by
    intro x hx
    obtain ⟨y, hy⟩ := nonempty x hx
    have member : y ∈ Name.eval {q | H.mem q} β := by
      rw [value]
      exact ZFSet.mem_sUnion.2 ⟨x, hx, hy⟩
    obtain ⟨i, hi, entry⟩ := covers y member
    exact ⟨i, hi, y, hy, entry⟩
  exact ⟨ordinalIndexedChoiceGraph A T e,
    N.ordinalIndexedChoiceGraph_mem pairingN unionsN powersN separationN hA hTN he,
    ordinalIndexedChoiceGraph_choice ordinal enumeration meets⟩

include pairing unions powers separation collection infinite choice carrier order generic in
theorem ordinaryExtension_choice :
    Realize (M.ordinaryExtension s H).sets SetFormula.choice Fin.elim0 := by
  apply (M.ordinaryExtension s H).choice_of_witnesses
  intro A hA nonempty
  exact M.ordinaryExtension_choice_witness s pairing unions powers separation collection infinite choice
    carrier order H generic hA nonempty

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable {G : Type v} [Group G]

theorem supportedNameFamily_graph_choice
    (s : Presentation P) (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0) (carrier : s.carrier ∈ M.sets)
    {W : ZFSet.{u}} (hW : W ∈ M.sets) (valid : ∀ z ∈ W, IsName s z)
    (K : Subgroup G) (support : F.mem K)
    (fixed : ∀ psi : Name s, psi.val ∈ W → K ≤ a.stabilizer s psi)
    (children : ∀ psi : Name s, psi.val ∈ W → HereditarilySymmetric a s F psi)
    (H : ConditionFilter P) (zf : ZFRealization (M.symmetricExtension s a F H).sets)
    {delta z : ZFSet.{u}}
    (hDelta : delta ∈ (M.symmetricExtension s a F H).sets)
    (hz : z ∈ (M.symmetricExtension s a F H).sets) (function : FunctionGraphOn delta z)
    (available : ∀ beta ∈ delta, ∃ psi : Name s, psi.val ∈ W ∧
      ∃ A, ZFSet.pair beta A ∈ z ∧ Name.eval {p | H.mem p} psi ∈ A) :
    ∃ f ∈ (M.symmetricExtension s a F H).sets, FunctionGraphOn delta f ∧
      ∀ beta A x, ZFSet.pair beta A ∈ z → ZFSet.pair beta x ∈ f → x ∈ A := by
  let N := M.symmetricExtension s a F H
  have pairingN : Realize N.sets SetFormula.pairing Fin.elim0 := zf.1.2.2.2.1
  have unionsN : Realize N.sets SetFormula.union Fin.elim0 := zf.1.2.2.2.2.1
  have powersN : Realize N.sets powerSet Fin.elim0 := zf.1.2.2.2.2.2.1
  have separationN : SeparationSchema N.sets := zf.2.1
  obtain ⟨T, hT, e, he, ordinal, injection, onto⟩ :=
    M.exists_groundOrdinalEnumeration pairing unions powers separation collection choice hW
  let enumeration : FunctionGraphOn T e := ⟨W, injection.function⟩
  have values : ∀ i, enumeration.value i ∈ W := by
    intro i
    exact (ZFSet.pair_mem_prod.1 (injection.function.1 (enumeration.value_entry i))).2
  have names : ∀ i, IsName s (enumeration.value i) := fun i => valid _ (values i)
  have sequence := M.supportedNameSequence_function_mem s a F pairing unions powers separation
    collection carrier hT he enumeration names K support
    (fun g hg i => fixed ⟨enumeration.value i, names i⟩ (values i) hg)
    (fun i => children ⟨enumeration.value i, names i⟩ (values i)) H
  let E := Name.eval {p | H.mem p} (Name.indexedGraphName ⊤ enumeration names)
  have hE : E ∈ N.sets := sequence.2.2.2.2
  have evalFunction : FunctionGraphOn T E := ⟨_, sequence.2.2.2.1⟩
  have includes := M.ground_subset_symmetricExtension s a F
    pairing unions powers separation collection carrier H
  have hTN : T ∈ N.sets := includes hT
  let B := ⋃₀ ⋃₀ z
  let A := relationImage delta B z
  have hB : B ∈ N.sets := N.union_mem unionsN (N.union_mem unionsN hz)
  have hA : A ∈ N.sets := N.relationImage_mem separationN hDelta hB hz
  have imageEntry {beta Y : ZFSet.{u}} (edge : ZFSet.pair beta Y ∈ z) : Y ∈ A :=
    (mem_relationImage delta B z Y).2
      ⟨pair_second_mem_doubleUnion edge, beta, function.pair_source edge, edge⟩
  have meets : ∀ Y ∈ A, ∃ i ∈ T, ∃ x ∈ Y, ZFSet.pair i x ∈ E := by
    intro Y member
    obtain ⟨_bound, beta, hBeta, edge⟩ := (mem_relationImage delta B z Y).1 member
    obtain ⟨psi, hPsi, Y', otherEdge, memberValue⟩ := available beta hBeta
    have same : Y' = Y := function.unique otherEdge edge
    rw [same] at memberValue
    obtain ⟨i, hi, code⟩ := onto psi.val hPsi
    let j : T.toSet := ⟨i, hi⟩
    have valueEq : enumeration.value j = psi.val := enumeration.value_eq_of_entry j code
    have nameEq : (⟨enumeration.value j, names j⟩ : Name s) = psi := Subtype.ext valueEq
    refine ⟨i, hi, Name.eval {p | H.mem p} psi, memberValue, ?_⟩
    exact (Name.pair_mem_eval_indexedGraphName {p | H.mem p} ⊤ H.top_mem
      enumeration names j _).2 (congrArg (Name.eval {p | H.mem p}) nameEq)
  let c := ordinalIndexedChoiceGraph A T E
  have hc : c ∈ N.sets := N.ordinalIndexedChoiceGraph_mem pairingN unionsN powersN separationN hA hTN hE
  have chooser : ChoiceFunctionCode A c := ordinalIndexedChoiceGraph_choice ordinal evalFunction meets
  let f := relationCompose delta A (⋃₀ A) z c
  have hf : f ∈ N.sets := N.relationCompose_mem pairingN unionsN powersN separationN
    hDelta hA (N.union_mem unionsN hA) hz hc
  have code : ZFSet.IsFunc delta (⋃₀ A) f := by
    refine ⟨fun _ member => (ZFSet.mem_sep.1 member).1, ?_⟩
    intro beta hBeta
    obtain ⟨Y, edge⟩ := function.total hBeta
    have member := imageEntry edge
    obtain ⟨x, chosen, unique⟩ := chooser.function.2 Y member
    have hx := chooser.chosen Y x chosen
    refine ⟨x, (pair_mem_relationCompose delta A (⋃₀ A) z c beta x).2
      ⟨hBeta, ZFSet.mem_sUnion.2 ⟨Y, member, hx⟩, Y, member, edge, chosen⟩, ?_⟩
    intro y yEdge
    obtain ⟨_key, _range, Y', _member, other, picked⟩ :=
      (pair_mem_relationCompose delta A (⋃₀ A) z c beta y).1 yEdge
    have same : Y' = Y := function.unique other edge
    exact unique y (same ▸ picked)
  refine ⟨f, hf, ⟨⋃₀ A, code⟩, ?_⟩
  intro beta Y x edge chosen
  obtain ⟨_key, _range, Y', _member, other, picked⟩ :=
    (pair_mem_relationCompose delta A (⋃₀ A) z c beta x).1 chosen
  have same : Y' = Y := function.unique other edge
  exact same ▸ chooser.chosen Y' x picked

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (T : ZFSet.{u}) (K : L → Subgroup G)

theorem exists_ground_supportedEqualityChoice
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (H : ConditionFilter P) (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
    {B : ZFSet.{u}} (hB : B ∈ M.sets) (smallB : M.groundEmbeddable B ZFSet.omega)
    (subset : B ⊆ b.carrier) (z : (M.nameDomain s).names)
    (visible : ∀ v : L, b.encode v ∈ B → Name.eval {p | H.mem p} z.val ∈
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (K v))) :
    ∃ f ∈ M.sets, ZFSet.IsFunc B (M.niceSupportNameCodes a s T K) f ∧
      f ⊆ supportedEqualityRelation B (M.niceSupportNameCodes a s T K)
        (M.niceSupportRelation a s b T K)
        (Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T K))
        (Name.eval {p | H.mem p} z.val) := by
  let N := M.ordinaryExtension s H
  have codesGround := M.niceSupportNameCodes_mem a s b T K t pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  have relationGround := M.supportedEqualityRelation_mem_ordinary a s b T K H t pairing unions powers
    separation collection infinite carrier order group nodes supports maps hT valid genericFormula hB z
  have total := M.supportedEqualityRelation_total a s b T K H subset visible
  have zf := M.ordinaryExtension_ZF s pairing unions powers separation collection carrier order
    infinite H genericFormula
  have choiceN := M.ordinaryExtension_choice s pairing unions powers separation collection infinite
    choice carrier order H genericFormula
  have includes := M.ground_subset_ordinaryExtension s pairing unions powers separation collection carrier H
  obtain ⟨f, hf, function, selected⟩ := N.uniformize_relation zf.1.2.2.2.1 zf.1.2.2.2.2.1
    zf.1.2.2.2.2.2.1 zf.2.1 choiceN (includes hB) (includes codesGround) relationGround total
  have ground := M.ordinaryExtension_countableDomainFunction_mem s pairing unions powers separation
    collection infinite choice carrier order small hB codesGround smallB closed H genericCoded
    genericFormula hf function
  exact ⟨f, ground, function, selected⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
