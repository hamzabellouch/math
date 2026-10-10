import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRefinementValidityForcing
import OAI.SetTheory.PartitionPrinciple.Models.GroundRefinementQuotientNames

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

theorem equivalenceClass_empty_of_not_mem {U R x : ZFSet.{u}}
    (shape : R ⊆ ZFSet.prod U U) (inactive : x ∉ U) : equivalenceClass U R x = ∅ := by
  apply ZFSet.ext
  intro y
  constructor
  · intro hy
    exact False.elim (inactive (ZFSet.pair_mem_prod.1 (shape (mem_equivalenceClass U R x y |>.1 hy).2)).2)
  · exact False.elim ∘ ZFSet.notMem_empty y

structure RefinementObjectValues {P : Type u} [PartialOrder P] [OrderTop P]
    {s : Presentation P} (H : Set P) (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U Rf Rc : Name s) : Prop where
  validity : RefinementValidityCode (Name.eval H (Name.familySet ⊤ T valid))
    (Name.eval H U) (Name.eval H Rf) (Name.eval H Rc)
  fine_class : ∀ w : Name s, w.val ∈ T →
    Name.eval H (Name.refinementClass T valid Rf w) =
      equivalenceClass (Name.eval H U) (Name.eval H Rf) (Name.eval H w)
  coarse_class : ∀ w : Name s, w.val ∈ T →
    Name.eval H (Name.refinementClass T valid Rc w) =
      equivalenceClass (Name.eval H U) (Name.eval H Rc) (Name.eval H w)
  fine_quotient : Name.eval H (Name.refinementQuotient T valid U Rf) =
    equivalenceClasses (Name.eval H U) (Name.eval H Rf)
  coarse_quotient : Name.eval H (Name.refinementQuotient T valid U Rc) =
    equivalenceClasses (Name.eval H U) (Name.eval H Rc)
  natural_map : Name.eval H (Name.refinementNaturalMap T valid U Rf Rc) =
    refinementQuotientMap (Name.eval H U) (Name.eval H Rf) (Name.eval H Rc)
  function : ZFSet.IsFunc (Name.eval H (Name.refinementQuotient T valid U Rf))
    (Name.eval H (Name.refinementQuotient T valid U Rc))
    (Name.eval H (Name.refinementNaturalMap T valid U Rf Rc))
  onto : ∀ C ∈ Name.eval H (Name.refinementQuotient T valid U Rc),
    ∃ D ∈ Name.eval H (Name.refinementQuotient T valid U Rf),
      ZFSet.pair D C ∈ Name.eval H (Name.refinementNaturalMap T valid U Rf Rc)
  inactive : ∀ w : Name s, w.val ∈ T → Name.eval H w ∉ Name.eval H U →
    Name.eval H (Name.refinementClass T valid Rf w) = ∅ ∧
    Name.eval H (Name.refinementClass T valid Rc w) = ∅

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)

noncomputable def refinementNameEnv (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (hFamily : (Name.familySet ⊤ T valid).val ∈ M.sets)
    (U Rf Rc : (M.nameDomain s).names) : Assignment (M.nameDomain s) 4 :=
  extend U (extend Rf (extend Rc (extend ⟨Name.familySet ⊤ T valid, hFamily⟩ Fin.elim0)))

theorem refinementObjects_eval
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (carrier : s.carrier ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (hFamily : (Name.familySet ⊤ T valid).val ∈ M.sets)
    (U Rf Rc : (M.nameDomain s).names)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    {p : P} (hp : H.mem p)
    (forced : Forces (M.nameDomain s) BoundedFormula.refinementValidityFormula.toFormula
      (M.refinementNameEnv s T valid hFamily U Rf Rc) p) :
    RefinementObjectValues {q | H.mem q} T valid U.val Rf.val Rc.val := by
  have validity : RefinementValidityCode (Name.eval {q | H.mem q} (Name.familySet ⊤ T valid))
      (Name.eval {q | H.mem q} U.val) (Name.eval {q | H.mem q} Rf.val) (Name.eval {q | H.mem q} Rc.val) :=
    M.refinementValidity_eval s (M.refinementNameEnv s T valid hFamily U Rf Rc) H generic hp forced
  have atomic : H.GenericFor (Name.atomicFamily (M.nameDomain s)) :=
    fun E hE dense => generic E (Or.inl hE) dense
  have terms (w : Name s) (hw : w.val ∈ T) : w ∈ (M.nameDomain s).names := M.transitive hT hw
  have pairs (z w : Name s) (hz : z.val ∈ T) (hw : w.val ∈ T) :
      Name.orderedPair ⊤ z w ∈ (M.nameDomain s).names := by
    change (Name.orderedPair ⊤ z w).val ∈ M.sets
    rw [Name.orderedPair_code]
    exact M.orderedPairNameCode_mem pairing (M.transitive carrier (s.encode_mem ⊤))
      (M.transitive hT hz) (M.transitive hT hw)
  have fineClass (w : Name s) (hw : w.val ∈ T) :=
    (M.eval_refinementClass s pairing carrier hT valid Rf.val w Rf.property (M.transitive hT hw) H generic).trans
      (equivalenceClass_eq_of_carrier_subset validity.1 validity.2.1.shape (Name.eval {q | H.mem q} w))
  have coarseClass (w : Name s) (hw : w.val ∈ T) :=
    (M.eval_refinementClass s pairing carrier hT valid Rc.val w Rc.property (M.transitive hT hw) H generic).trans
      (equivalenceClass_eq_of_carrier_subset validity.1 validity.2.2.1.shape (Name.eval {q | H.mem q} w))
  have fineQuotient := Name.eval_refinementQuotient (M.nameDomain s) H atomic T valid U.val Rf.val
    U.property Rf.property terms pairs validity.1 validity.2.1.shape
  have coarseQuotient := Name.eval_refinementQuotient (M.nameDomain s) H atomic T valid U.val Rc.val
    U.property Rc.property terms pairs validity.1 validity.2.2.1.shape
  have naturalMap := Name.eval_refinementNaturalMap (M.nameDomain s) H atomic T valid U.val Rf.val Rc.val
    U.property Rf.property Rc.property terms pairs validity.1 validity.2.1.shape validity.2.2.1.shape
  refine ⟨validity, fineClass, coarseClass, fineQuotient, coarseQuotient, naturalMap, ?_, ?_, ?_⟩
  · rw [fineQuotient, coarseQuotient, naturalMap]
    exact refinementQuotientMap_function validity.2.1 validity.2.2.1 validity.2.2.2
  · intro C hC
    rw [coarseQuotient] at hC
    obtain ⟨D, hD, entry⟩ := refinementQuotientMap_onto (Rf := Name.eval {q | H.mem q} Rf.val) hC
    exact ⟨D, fineQuotient.symm ▸ hD, naturalMap.symm ▸ entry⟩
  · intro w hw inactive
    rw [fineClass w hw, coarseClass w hw]
    exact ⟨equivalenceClass_empty_of_not_mem validity.2.1.shape inactive,
      equivalenceClass_empty_of_not_mem validity.2.2.1.shape inactive⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u

theorem normalizedRefinementOutputs
    (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
    (s : Presentation P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (normalized : Assignment (M.nameDomain s) 4)
    (last : (normalized 3).val = Name.familySet ⊤ T valid)
    (forced : Forces (M.nameDomain s)
      BoundedFormula.refinementValidityFormula.toFormula normalized ⊤) :
    (Name.refinementQuotient T valid (normalized 0).val (normalized 1).val).val ∈ M.sets ∧
    (Name.refinementQuotient T valid (normalized 0).val (normalized 2).val).val ∈ M.sets ∧
    (Name.refinementNaturalMap T valid (normalized 0).val (normalized 1).val
      (normalized 2).val).val ∈ M.sets ∧
    ∀ H : ConditionFilter P, H.GenericFor (formulaFamily (M.nameDomain s)) →
      RefinementObjectValues {p | H.mem p} T valid
        (normalized 0).val (normalized 1).val (normalized 2).val := by
  have familyGround : (Name.familySet ⊤ T valid).val ∈ M.sets := by
    rw [← last]
    exact (normalized 3).property
  have lastName : normalized 3 = ⟨Name.familySet ⊤ T valid, familyGround⟩ := Subtype.ext last
  have sameEnv : normalized = M.refinementNameEnv s T valid familyGround
      (normalized 0) (normalized 1) (normalized 2) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases lastName (fun j => Fin.elim0 j)))) i
  refine ⟨M.refinementQuotient_mem s pairing unions powers separation collection carrier order
      hT valid _ _ (normalized 0).property (normalized 1).property,
    M.refinementQuotient_mem s pairing unions powers separation collection carrier order
      hT valid _ _ (normalized 0).property (normalized 2).property,
    M.refinementNaturalMap_mem s pairing unions powers separation collection carrier order
      hT valid _ _ _ (normalized 0).property (normalized 1).property (normalized 2).property, ?_⟩
  intro H generic
  exact M.refinementObjects_eval s pairing carrier hT valid familyGround
    (normalized 0) (normalized 1) (normalized 2) H generic H.top_mem (sameEnv ▸ forced)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
