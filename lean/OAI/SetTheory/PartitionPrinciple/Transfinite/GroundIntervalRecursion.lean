import OAI.SetTheory.PartitionPrinciple.Definability.NaturalStepFormulas
import OAI.SetTheory.PartitionPrinciple.Geometry.FiniteIntervalExtension
import OAI.SetTheory.PartitionPrinciple.Geometry.IntervalTraceValidity

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem collect_ordinalSuccessorTraces
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {k : Nat} (φ : SetFormula (k + 3)) (params : Fin k → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {A : ZFSet.{u}} (hA : A ∈ M.sets)
    (traces : ∀ β ∈ A, ∃ f ∈ M.sets,
      OrdinalRecursionTrace (groundRecursionStep M φ params) (insert β β) f) :
    ∃ family ∈ M.sets,
      (∀ f ∈ family, ∃ β ∈ A,
        OrdinalRecursionTrace (groundRecursionStep M φ params) (insert β β) f) ∧
      ∀ β ∈ A, ∃ f ∈ family,
        OrdinalRecursionTrace (groundRecursionStep M φ params) (insert β β) f := by
  have witnesses : ∀ β ∈ A, ∃ f ∈ M.sets,
      Realize M.sets (ordinalSuccessorTraceFormula φ) (extend β (extend f params)) := by
    intro β hβ
    obtain ⟨f, hf, trace⟩ := traces β hβ
    exact ⟨f, hf, (M.realize_ordinalSuccessorTraceFormula pairing unions φ params
      members (M.transitive hA hβ) hf).2 trace⟩
  obtain ⟨W, hW, covers⟩ := M.collection_witness collection (ordinalSuccessorTraceFormula φ)
    params members hA witnesses
  let family := ZFSet.sep (fun f => Realize M.sets
    (relationImageFormula (ordinalSuccessorTraceFormula φ)) (extend f (extend A params))) W
  have hFamily : family ∈ M.sets := M.separation_mem separation
    (relationImageFormula (ordinalSuccessorTraceFormula φ)) (extend A params)
    (Fin.cases hA members) hW
  refine ⟨family, hFamily, ?_, ?_⟩
  · intro f hf
    obtain ⟨hfW, selected⟩ := ZFSet.mem_sep.1 hf
    obtain ⟨β, hβ, relation⟩ := (M.realize_relationImageFormula
      (ordinalSuccessorTraceFormula φ) params A f hA).1 selected
    exact ⟨β, hβ, (M.realize_ordinalSuccessorTraceFormula pairing unions φ params
      members (M.transitive hA hβ) (M.transitive hW hfW)).1 relation⟩
  · intro β hβ
    obtain ⟨f, hfW, relation⟩ := covers β hβ
    have selected := (M.realize_relationImageFormula (ordinalSuccessorTraceFormula φ)
      params A f hA).2 ⟨β, hβ, relation⟩
    exact ⟨f, ZFSet.mem_sep.2 ⟨hfW, selected⟩,
      (M.realize_ordinalSuccessorTraceFormula pairing unions φ params members
        (M.transitive hA hβ) (M.transitive hW hfW)).1 relation⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

open SetFormula
universe u

def GroundOrdinalStepClosure (M : TransitiveGround.{u}) (T : ZFSet.{u})
    {k : Nat} (φ : SetFormula (k + 3)) (params : Fin k → ZFSet.{u}) : Prop :=
  ∀ α ∈ T, ∀ p ∈ M.sets, OrdinalRecursionTrace (groundRecursionStep M φ params) α p →
    ∃ y ∈ M.sets, Realize M.sets φ (extend α (extend p (extend y params))) ∧
      ∀ z ∈ M.sets, Realize M.sets φ (extend α (extend p (extend z params))) → z = y

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem groundRecursionStep_unique_on_traces {T : ZFSet.{u}} {k : Nat}
    {φ : SetFormula (k + 3)} {params : Fin k → ZFSet.{u}}
    (step : GroundOrdinalStepClosure M T φ params) :
    ∀ α ∈ T, ∀ p, OrdinalRecursionTrace (groundRecursionStep M φ params) α p →
      ∀ y z, groundRecursionStep M φ params α p y →
        groundRecursionStep M φ params α p z → y = z := by
  intro α hα p trace y z first second
  obtain ⟨w, _, _, unique⟩ := step α hα p first.1 trace
  exact (unique y first.2.1 first.2.2).trans (unique z second.2.1 second.2.2).symm

theorem exists_ordinalRecursionTrace
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (ordinal : ordinalSetProperty T)
    {k : Nat} (φ : SetFormula (k + 3)) (params : Fin k → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets)
    (step : GroundOrdinalStepClosure M T φ params) :
    ∃ f ∈ M.sets, OrdinalRecursionTrace (groundRecursionStep M φ params) T f := by
  have unique := M.groundRecursionStep_unique_on_traces step
  have successors : ∀ α ∈ T, ∃ f ∈ M.sets,
      OrdinalRecursionTrace (groundRecursionStep M φ params) (insert α α) f := by
    intro α
    induction α using ZFSet.inductionOn with
    | h α ih =>
      intro hα
      have hαM := M.transitive hT hα
      have ordinalα := ordinalSetProperty_member ordinal hα
      have subsetα : α ⊆ T := fun β hβ => ordinal.1 α hα β hβ
      obtain ⟨family, hFamily, traces, covers⟩ := M.collect_ordinalSuccessorTraces pairing unions
        separation collection φ params members hαM
        (fun β hβ => ih β hβ (subsetα hβ))
      have prefixTrace := OrdinalRecursionTrace.sUnion_successors ordinalα subsetα unique traces covers
      have hPrefix := M.union_mem unions hFamily
      obtain ⟨y, hy, relation, _⟩ := step α hα family.sUnion hPrefix prefixTrace
      exact ⟨insert (ZFSet.pair α y) family.sUnion,
        M.insert_mem pairing unions (M.orderedPair_mem pairing hαM hy) hPrefix,
        prefixTrace.succ ordinalα ⟨hPrefix, hy, relation⟩⟩
  obtain ⟨family, hFamily, traces, covers⟩ := M.collect_ordinalSuccessorTraces pairing unions
    separation collection φ params members hT successors
  exact ⟨family.sUnion, M.union_mem unions hFamily,
    OrdinalRecursionTrace.sUnion_successors ordinal (fun _ hx => hx) unique traces covers⟩

theorem ordinalRecursionTrace_entry {T f : ZFSet.{u}} (ordinal : ordinalSetProperty T)
    {k : Nat} {φ : SetFormula (k + 3)} {params : Fin k → ZFSet.{u}}
    (step : GroundOrdinalStepClosure M T φ params)
    (trace : OrdinalRecursionTrace (groundRecursionStep M φ params) T f) :
    ∀ α ∈ T, ∀ y ∈ M.sets, ZFSet.pair α y ∈ f ↔
      Realize M.sets φ (extend α (extend (graphRestriction α f) (extend y params))) := by
  intro α hα y hy
  constructor
  · intro entry
    exact (trace.2 α hα y entry).2.2
  · intro relation
    obtain ⟨w, entry⟩ := trace.1.total hα
    have stepW := trace.2 α hα w entry
    have prefixTrace := trace.restrict (ordinalSetProperty_member ordinal hα)
      (fun β hβ => ordinal.1 α hα β hβ)
    have equal := M.groundRecursionStep_unique_on_traces step α hα _ prefixTrace y w
      ⟨stepW.1, hy, relation⟩ stepW
    rw [equal]
    exact entry

theorem exists_unique_ordinalRecursionTrace
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (ordinal : ordinalSetProperty T)
    {k : Nat} (φ : SetFormula (k + 3)) (params : Fin k → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets)
    (step : GroundOrdinalStepClosure M T φ params) :
    ∃ f ∈ M.sets, OrdinalRecursionTrace (groundRecursionStep M φ params) T f ∧
      (∀ g, OrdinalRecursionTrace (groundRecursionStep M φ params) T g → g = f) ∧
      ∀ α ∈ T, ∀ y ∈ M.sets, ZFSet.pair α y ∈ f ↔
        Realize M.sets φ (extend α (extend (graphRestriction α f) (extend y params))) := by
  obtain ⟨f, hf, trace⟩ := M.exists_ordinalRecursionTrace pairing unions separation collection
    hT ordinal φ params members step
  exact ⟨f, hf, trace, fun g other => other.unique trace ordinal (fun _ hx => hx)
    (M.groundRecursionStep_unique_on_traces step), M.ordinalRecursionTrace_entry ordinal step trace⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open SetFormula SetRealization
universe u

def intervalSequenceParams (A D rA rD e lo hi c : ZFSet.{u}) : Fin 9 → ZFSet.{u} :=
  extend A (extend D (extend rA (extend rD (extend e
    (extend lo (extend hi (extend c (extend ZFSet.omega Fin.elim0))))))))

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem exists_ground_intervalSequence
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A D rA rD e lo hi c : ZFSet.{u}}
    (hA : A ∈ M.sets) (hD : D ∈ M.sets) (hrA : rA ∈ M.sets)
    (hrD : rD ∈ M.sets) (he : e ∈ M.sets) (hc : c ∈ M.sets)
    (source : StrictLinearOrderCode A rA) (target : DenseOrderCode D rD)
    (injection : InjectionCode D ZFSet.omega c)
    (enumeration : ZFSet.IsFunc ZFSet.omega A e)
    (loD : lo ∈ D) (hiD : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD) :
    ∃ t ∈ M.sets, IntervalSequenceCode ZFSet.omega A D rA rD e lo hi t ∧
      OrdinalRecursionTrace
        (groundRecursionStep M intervalSequenceStepFormula (intervalSequenceParams A D rA rD e lo hi c))
        ZFSet.omega t ∧
      ∀ s, OrdinalRecursionTrace
        (groundRecursionStep M intervalSequenceStepFormula (intervalSequenceParams A D rA rD e lo hi c))
        ZFSet.omega s → s = t := by
  have hw := M.omega_mem separation infinite
  have hlo := M.transitive hD loD
  have hhi := M.transitive hD hiD
  let params := intervalSequenceParams A D rA rD e lo hi c
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hA (Fin.cases hD (Fin.cases hrA (Fin.cases hrD (Fin.cases he
      (Fin.cases hlo (Fin.cases hhi (Fin.cases hc (Fin.cases hw (fun i => Fin.elim0 i)))))))))
  have decode (N p y : ZFSet.{u}) (hN : N ∈ M.sets) (hp : p ∈ M.sets) (hy : y ∈ M.sets) :
      Realize M.sets intervalSequenceStepFormula (extend N (extend p (extend y params))) ↔
        leastIntervalNextCandidate N A D rA rD e lo hi p c y :=
    M.realize_intervalSequenceStepFormula (extend N (extend p (extend y params)))
      (Fin.cases hN (Fin.cases hp (Fin.cases hy members))) rfl
  have valid {N p : ZFSet.{u}} (natural : N ⊆ ZFSet.omega)
      (trace : OrdinalRecursionTrace (groundRecursionStep M intervalSequenceStepFormula params) N p) :
      IntervalSequenceCode N A D rA rD e lo hi p := by
    apply intervalSequence_of_next source target.toStrictLinearOrderCode enumeration natural trace.1
    intro i hiN y entry
    have step := trace.2 i hiN y entry
    exact ((decode i (graphRestriction i p) y (M.transitive hw (natural hiN))
      step.1 step.2.1).1 step.2.2).1
  have closure : GroundOrdinalStepClosure M ZFSet.omega intervalSequenceStepFormula params := by
    intro N hN p hp trace
    have hNM := M.transitive hw hN
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode N).1 hN
    have natural : natSetCode n ⊆ (ZFSet.omega : ZFSet.{u}) := by
      intro i hiN
      obtain ⟨k, _, rfl⟩ := (mem_natSetCode i n).1 hiN
      exact natSetCode_mem_omega k
    have prefixValid := valid natural trace
    have candidate := finite_intervalNextCandidate_exists n prefixValid enumeration source target
      loD hiD gap
    obtain ⟨y, selected, unique⟩ := leastIntervalNextCandidate_exists_unique injection candidate
    have hy := M.transitive hD selected.1.1
    exact ⟨y, hy, (decode _ p y hNM hp hy).2 selected,
      fun z hz relation => unique z ((decode _ p z hNM hp hz).1 relation)⟩
  have ordinal : ordinalSetProperty (ZFSet.omega : ZFSet.{u}) := by
    rw [← ordinalCode_omega]
    exact ordinalSetProperty_ordinalCode Ordinal.omega0
  obtain ⟨t, ht, trace, unique, _⟩ := M.exists_unique_ordinalRecursionTrace
    pairing unions separation collection hw ordinal intervalSequenceStepFormula params members closure
  exact ⟨t, ht, valid (fun _ hi => hi) trace, trace, unique⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
