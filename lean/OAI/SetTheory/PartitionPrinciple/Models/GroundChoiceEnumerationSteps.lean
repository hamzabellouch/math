import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundIntervalRecursion

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def enumerationRemainder (A a p : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ¬ ∃ b ∈ a, ZFSet.pair b x ∈ p) A

theorem mem_enumerationRemainder (A a p x : ZFSet.{u}) :
    x ∈ enumerationRemainder A a p ↔ x ∈ A ∧ ¬ ∃ b ∈ a, ZFSet.pair b x ∈ p :=
  ZFSet.mem_sep

def ChoiceEnumerationStep (A F c a p y : ZFSet.{u}) : Prop :=
  (∃ R ∈ F, R = enumerationRemainder A a p ∧ ZFSet.pair R y ∈ c) ∨
    (¬ (enumerationRemainder A a p).Nonempty ∧ y = A)

namespace BoundedFormula

def enumerationRemainderFormula {n} (R A a p : Fin n) : BoundedFormula n :=
  .conj (.allMem R (.mem 0 A.succ)) (.allMem A
    (.conj (imp (.mem 0 R.succ)
      (.neg (exMem a.succ (pairMembershipFormula 0 1 p.succ.succ))))
      (imp (.neg (exMem a.succ (pairMembershipFormula 0 1 p.succ.succ)))
        (.mem 0 R.succ))))

theorem truth_enumerationRemainderFormula {n} (R A a p : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (enumerationRemainderFormula R A a p) env ↔
      env R = enumerationRemainder (env A) (env a) (env p) := by
  simp only [enumerationRemainderFormula, Truth, truth_imp, truth_exMem,
    truth_pairMembershipFormula, ← iff_def]
  change ((∀ x ∈ env R, x ∈ env A) ∧ ∀ x ∈ env A,
    x ∈ env R ↔ ¬ ∃ b ∈ env a, ZFSet.pair b x ∈ env p) ↔ _
  constructor
  · rintro ⟨subset, spec⟩
    apply ZFSet.ext
    intro x
    rw [mem_enumerationRemainder]
    exact ⟨fun hx => ⟨subset x hx, (spec x (subset x hx)).1 hx⟩,
      fun ⟨hx, unused⟩ => (spec x hx).2 unused⟩
  · intro equal
    rw [equal]
    exact ⟨fun _ hx => (mem_enumerationRemainder _ _ _ _).1 hx |>.1,
      fun x hx => by rw [mem_enumerationRemainder]; exact and_iff_right hx⟩

def choiceEnumerationStepFormula {n} (A F c a p y : Fin n) : BoundedFormula n :=
  disj (exMem F (.conj (enumerationRemainderFormula 0 A.succ a.succ p.succ)
    (pairMembershipFormula 0 y.succ c.succ)))
    (.conj (.neg (exMem A (.neg (exMem a.succ
      (pairMembershipFormula 0 1 p.succ.succ))))) (.equal y A))

theorem truth_choiceEnumerationStepFormula {n} (A F c a p y : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (choiceEnumerationStepFormula A F c a p y) env ↔
      ChoiceEnumerationStep (env A) (env F) (env c) (env a) (env p) (env y) := by
  simp only [choiceEnumerationStepFormula, truth_disj, truth_exMem, Truth,
    truth_enumerationRemainderFormula, truth_pairMembershipFormula]
  change ((∃ R ∈ env F, R = enumerationRemainder (env A) (env a) (env p) ∧
    ZFSet.pair R (env y) ∈ env c) ∨
    (¬ (∃ x ∈ env A, ¬ ∃ b ∈ env a, ZFSet.pair b x ∈ env p) ∧ env y = env A)) ↔ _
  have nonempty : (enumerationRemainder (env A) (env a) (env p)).Nonempty ↔
      ∃ x ∈ env A, ¬ ∃ b ∈ env a, ZFSet.pair b x ∈ env p := by
    change (∃ x, x ∈ enumerationRemainder (env A) (env a) (env p)) ↔ _
    simp only [mem_enumerationRemainder]
  simp only [ChoiceEnumerationStep, nonempty]

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem enumerationRemainder_mem (separation : SeparationSchema M.sets)
    {A a p : ZFSet.{u}} (hA : A ∈ M.sets) (ha : a ∈ M.sets) (hp : p ∈ M.sets) :
    enumerationRemainder A a p ∈ M.sets := by
  let formula : BoundedFormula 3 := .neg (BoundedFormula.exMem 1
    (BoundedFormula.pairMembershipFormula 0 1 3))
  let params := extend a (extend p Fin.elim0)
  have ground := M.bounded_separation_mem separation formula params
    (Fin.cases ha (Fin.cases hp (fun i => Fin.elim0 i))) hA
  have equal : ZFSet.sep (fun x => BoundedFormula.Truth formula (extend x params)) A =
      enumerationRemainder A a p := by
    apply ZFSet.ext
    intro x
    simp only [ZFSet.mem_sep, enumerationRemainder, formula, BoundedFormula.Truth,
      BoundedFormula.truth_exMem, BoundedFormula.truth_pairMembershipFormula]
    rfl
  exact equal ▸ ground

theorem choiceEnumerationStep_exists_unique (separation : SeparationSchema M.sets)
    {A c a p : ZFSet.{u}} (hA : A ∈ M.sets) (ha : a ∈ M.sets) (hp : p ∈ M.sets)
    (code : ChoiceFunctionCode (M.nonemptyGroundSubsets A) c) :
    ∃ y ∈ M.sets, ChoiceEnumerationStep A (M.nonemptyGroundSubsets A) c a p y ∧
      ∀ z, ChoiceEnumerationStep A (M.nonemptyGroundSubsets A) c a p z → z = y := by
  classical
  let R := enumerationRemainder A a p
  have hR := M.enumerationRemainder_mem separation hA ha hp
  have subset : R ⊆ A := fun _ hx => (mem_enumerationRemainder _ _ _ _).1 hx |>.1
  by_cases nonempty : R.Nonempty
  · have member := (M.mem_nonemptyGroundSubsets A R).2 ⟨hR, subset, nonempty⟩
    obtain ⟨y, entry, unique⟩ := code.function.2 R member
    have hy := code.chosen R y entry
    refine ⟨y, M.transitive hA (subset hy), Or.inl ⟨R, member, rfl, entry⟩, ?_⟩
    intro z step
    rcases step with ⟨S, _, rfl, selected⟩ | ⟨empty, _⟩
    · exact unique z selected
    · exact False.elim (empty nonempty)
  · refine ⟨A, hA, Or.inr ⟨nonempty, rfl⟩, ?_⟩
    intro z step
    rcases step with ⟨S, member, rfl, _⟩ | ⟨_, equal⟩
    · exact False.elim (nonempty ((M.mem_nonemptyGroundSubsets A _).1 member).2.2)
    · exact equal

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
