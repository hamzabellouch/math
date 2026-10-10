import OAI.SetTheory.PartitionPrinciple.Geometry.GroundGrowthLayerRecognition
import OAI.SetTheory.PartitionPrinciple.Transfinite.SerializedChronologyCodes

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

def ChronologyLayerLookup (T : ZFSet.{u}) (graphs : Fin 5 → ZFSet.{u})
    (layers s t L r μ birth z : ZFSet.{u}) : Prop :=
  s ∈ T ∧ t ∈ T ∧ (t = s ∨ t ∈ s) ∧
    ZFSet.pair s L ∈ graphs 0 ∧ ZFSet.pair s r ∈ graphs 1 ∧
    ZFSet.pair s μ ∈ graphs 2 ∧ ZFSet.pair s birth ∈ graphs 3 ∧
    ZFSet.pair (ZFSet.pair s t) z ∈ layers

namespace BoundedFormula
def chronologyLayerLookupFormula {n} (T : Fin n) (graphs : Fin 5 → Fin n)
    (layers s t L r μ birth z : Fin n) : BoundedFormula n :=
  .conj (.mem s T) (.conj (.mem t T) (.conj (disj (.equal t s) (.mem t s))
    (.conj (pairMembershipFormula s L (graphs 0)) (.conj (pairMembershipFormula s r (graphs 1))
      (.conj (pairMembershipFormula s μ (graphs 2)) (.conj (pairMembershipFormula s birth (graphs 3))
        (tripleMembershipFormula s t z layers)))))))

theorem truth_chronologyLayerLookupFormula {n} (T : Fin n) (graphs : Fin 5 → Fin n)
    (layers s t L r μ birth z : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (chronologyLayerLookupFormula T graphs layers s t L r μ birth z) env ↔
      ChronologyLayerLookup (env T) (fun j => env (graphs j)) (env layers)
        (env s) (env t) (env L) (env r) (env μ) (env birth) (env z) := by
  simp only [chronologyLayerLookupFormula, Truth, truth_disj, truth_pairMembershipFormula,
    truth_tripleMembershipFormula, ChronologyLayerLookup]
end BoundedFormula

namespace SetFormula
def chronologyLayerClause {n} (T N : Fin n) (graphs : Fin 5 → Fin n)
    (layers s t L r μ birth z : Fin n) : SetFormula n :=
  imp (BoundedFormula.chronologyLayerLookupFormula T graphs layers s t L r μ birth z).toFormula
    (growthLayerWitnessFormula z (graphs 0) (graphs 1) (graphs 2) L r μ birth t N)

def chronologyLayerEntriesFormula {n} (T N : Fin n) (graphs : Fin 5 → Fin n)
    (layers : Fin n) : SetFormula n :=
  let old := suffixIndex n 7
  let field := prefixIndex n 7
  allBlock 7 (chronologyLayerClause (old T) (old N) (fun j => old (graphs j))
    (old layers) (field 0) (field 1) (field 2) (field 3) (field 4) (field 5) (field 6))
end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_chronologyLayerClause
    (unions : Realize M.sets SetFormula.union Fin.elim0) {n}
    (T V C D rD N : Fin n) (graphs : Fin 5 → Fin n)
    (layers s t L r μ birth z : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets)
    (core : ChronologyCoreCode (env T) (env V) (env C) (env D) (env rD) (fun j => env (graphs j))) :
    Realize M.sets (chronologyLayerClause T N graphs layers s t L r μ birth z) env ↔
      (ChronologyLayerLookup (env T) (fun j => env (graphs j)) (env layers)
        (env s) (env t) (env L) (env r) (env μ) (env birth) (env z) →
        GrowthLayerWitnessCode (env (graphs 0)) (env (graphs 1)) (env (graphs 2))
          (env L) (env r) (env μ) (env birth) (env t) (env N) (env z)) := by
  rw [chronologyLayerClause, realize_imp]
  have lookup := (BoundedFormula.realize_toFormula M _ env members).trans
    (BoundedFormula.truth_chronologyLayerLookupFormula T graphs layers s t L r μ birth z env)
  have recognized (h : ChronologyLayerLookup (env T) (fun j => env (graphs j)) (env layers)
      (env s) (env t) (env L) (env r) (env μ) (env birth) (env z)) :=
    M.realize_growthLayerWitnessFormula unions z (graphs 0) (graphs 1) (graphs 2)
      L r μ birth t N env members
      (core.meet_of_entries h.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1)
  exact ⟨fun h actual => (recognized actual).1 (h (lookup.2 actual)),
    fun h actual => (recognized (lookup.1 actual)).2 (h (lookup.1 actual))⟩

theorem realize_chronologyLayerEntriesFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0) {n}
    (T V C D rD N : Fin n) (graphs : Fin 5 → Fin n) (layers : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (core : ChronologyCoreCode (env T) (env V) (env C) (env D) (env rD) (fun j => env (graphs j))) :
    Realize M.sets (chronologyLayerEntriesFormula T N graphs layers) env ↔
      ChronologyLayerEntries (env T) (env N) (fun j => env (graphs j)) (env layers) := by
  let old := suffixIndex n 7
  let field := prefixIndex n 7
  let body := chronologyLayerClause (old T) (old N) (fun j => old (graphs j))
    (old layers) (field 0) (field 1) (field 2) (field 3) (field 4) (field 5) (field 6)
  have clause (values : Fin 7 → ZFSet.{u}) (ground : ∀ i, values i ∈ M.sets) :
      Realize M.sets body (extendMany 7 values env) ↔
        (ChronologyLayerLookup (env T) (fun j => env (graphs j)) (env layers)
          (values 0) (values 1) (values 2) (values 3) (values 4) (values 5) (values 6) →
          GrowthLayerWitnessCode (env (graphs 0)) (env (graphs 1)) (env (graphs 2))
            (values 2) (values 3) (values 4) (values 5) (values 1) (env N) (values 6)) := by
    have lifted : ChronologyCoreCode ((extendMany 7 values env) (old T))
        ((extendMany 7 values env) (old V)) ((extendMany 7 values env) (old C))
        ((extendMany 7 values env) (old D)) ((extendMany 7 values env) (old rD))
        (fun j => (extendMany 7 values env) (old (graphs j))) := by
      simpa only [old, extendMany_suffix] using core
    simpa only [body, old, field, extendMany_prefix, extendMany_suffix] using
      M.realize_chronologyLayerClause unions (old T) (old V) (old C) (old D) (old rD)
        (old N) (fun j => old (graphs j)) (old layers) (field 0) (field 1) (field 2)
        (field 3) (field 4) (field 5) (field 6) (extendMany 7 values env)
        (extendMany_members 7 values env ground members) lifted
  change Realize M.sets (allBlock 7 body) env ↔ _
  rw [realize_allBlock]
  constructor
  · intro recognized s hs t ht earlier L r μ birth z eL er eμ eb entry
    let values : Fin 7 → ZFSet.{u} := Fin.cases s (Fin.cases t (Fin.cases L
      (Fin.cases r (Fin.cases μ (Fin.cases birth (fun _ => z))))))
    have ground : ∀ i, values i ∈ M.sets :=
      Fin.cases (M.transitive (members T) hs) (Fin.cases (M.transitive (members T) ht)
        (Fin.cases (M.pair_right (M.transitive (members (graphs 0)) eL))
          (Fin.cases (M.pair_right (M.transitive (members (graphs 1)) er))
            (Fin.cases (M.pair_right (M.transitive (members (graphs 2)) eμ))
              (Fin.cases (M.pair_right (M.transitive (members (graphs 3)) eb))
                (fun _ => M.pair_right (M.transitive (members layers) entry)))))))
    exact (clause values ground).1 (recognized values ground) ⟨hs, ht, earlier, eL, er, eμ, eb, entry⟩
  · intro code values ground
    apply (clause values ground).2
    rintro ⟨hs, ht, earlier, eL, er, eμ, eb, entry⟩
    exact code _ hs _ ht earlier _ _ _ _ _ eL er eμ eb entry

end TransitiveGround

namespace SetFormula
def chronologyLayerFunctionFormula {n} (T W layers : Fin n) : SetFormula n :=
  ex (.conj (BoundedFormula.chronologyPairsEquationFormula 0 T.succ).toFormula
    (BoundedFormula.functionFormula 0 W.succ layers.succ).toFormula)

def serializedChronologyFormula {n} (T V C D rD N : Fin n)
    (graphs : Fin 5 → Fin n) (W layers : Fin n) : SetFormula n :=
  .conj (BoundedFormula.ordinalFormula T).toFormula
    (.conj (BoundedFormula.chronologyCoreFormula T V C D rD graphs).toFormula
      (.conj (chronologyLayerFunctionFormula T W layers)
        (chronologyLayerEntriesFormula T N graphs layers)))
end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_chronologyLayerFunctionFormula {n} (T W layers : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (chronologyLayerFunctionFormula T W layers) env ↔
      ZFSet.IsFunc (chronologyPairs (env T)) (env W) (env layers) := by
  rw [chronologyLayerFunctionFormula, realize_ex]
  constructor
  · rintro ⟨J, hJ, recognized, function⟩
    have equal := (BoundedFormula.realize_chronologyPairsEquationFormula M 0 T.succ
      (extend J env) (Fin.cases hJ members)).1 recognized
    have actual := (BoundedFormula.realize_toFormula M _ (extend J env) (Fin.cases hJ members)).1 function
    have code := (BoundedFormula.truth_functionFormula 0 W.succ layers.succ (extend J env)).1 actual
    exact equal ▸ code
  · intro function
    have hJ := M.chronologyPairs_mem pairing unions powers separation (members T)
    exact ⟨chronologyPairs (env T), hJ,
      (BoundedFormula.realize_chronologyPairsEquationFormula M 0 T.succ
        (extend (chronologyPairs (env T)) env) (Fin.cases hJ members)).2 rfl,
      (BoundedFormula.realize_toFormula M _ _ (Fin.cases hJ members)).2
        ((BoundedFormula.truth_functionFormula 0 W.succ layers.succ _).2 function)⟩

theorem realize_serializedChronologyFormula {n} (T V C D rD N : Fin n)
    (graphs : Fin 5 → Fin n) (W layers : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (serializedChronologyFormula T V C D rD N graphs W layers) env ↔
      SerializedChronologyCode (env T) (env V) (env C) (env D) (env rD) (env N)
        (fun j => env (graphs j)) (env W) (env layers) := by
  change (Realize M.sets (BoundedFormula.ordinalFormula T).toFormula env ∧
    Realize M.sets (BoundedFormula.chronologyCoreFormula T V C D rD graphs).toFormula env ∧
    Realize M.sets (chronologyLayerFunctionFormula T W layers) env ∧
    Realize M.sets (chronologyLayerEntriesFormula T N graphs layers) env) ↔ _
  rw [BoundedFormula.realize_ordinalFormula M T env members, ← ordinalSetProperty_iff,
    BoundedFormula.realize_chronologyCoreFormula M T V C D rD graphs env members,
    M.realize_chronologyLayerFunctionFormula pairing unions powers separation T W layers env members]
  constructor
  · rintro ⟨ordinal, core, function, entries⟩
    exact ⟨ordinal, core, function,
      (M.realize_chronologyLayerEntriesFormula unions T V C D rD N graphs layers env members core).1 entries⟩
  · intro code
    exact ⟨code.ordinal, code.core, code.function,
      (M.realize_chronologyLayerEntriesFormula unions T V C D rD N graphs layers env members code.core).2 code.entries⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
