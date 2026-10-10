import OAI.SetTheory.PartitionPrinciple.Definability.NaturalSetCodes
import OAI.SetTheory.PartitionPrinciple.Forcing.FlatLimitConditionCodes

namespace OAI

section

namespace PartitionPilot.SetRealization

universe u

theorem ordinalCode_zero : ordinalCode (0 : Ordinal.{u}) = ∅ := by
  apply ZFSet.ext
  intro x
  rw [mem_ordinalCode]
  exact ⟨fun ⟨_, lower, _⟩ => False.elim (not_lt_of_ge bot_le lower),
    fun h => False.elim (ZFSet.notMem_empty x h)⟩

theorem ordinalCode_succ (o : Ordinal.{u}) :
    ordinalCode (Order.succ o) = insert (ordinalCode o) (ordinalCode o) := by
  apply ZFSet.ext
  intro x
  rw [mem_ordinalCode, ZFSet.mem_insert_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases lt_or_eq_of_le (Order.lt_succ_iff.1 ha) with lower | eq
    · exact Or.inr ((mem_ordinalCode_iff a o).2 lower)
    · exact Or.inl (congrArg ordinalCode eq)
  · rintro (rfl | member)
    · exact ⟨o, Order.lt_succ o, rfl⟩
    · obtain ⟨a, ha, eq⟩ := mem_ordinalCode.1 member
      exact ⟨a, ha.trans (Order.lt_succ o), eq⟩

theorem ordinalCode_subset_iff (a b : Ordinal.{u}) : ordinalCode a ⊆ ordinalCode b ↔ a ≤ b := by
  constructor
  · intro subset
    have ranks := ZFSet.rank_mono subset
    simpa only [rank_ordinalCode] using ranks
  · intro lower x hx
    obtain ⟨o, ho, rfl⟩ := mem_ordinalCode.1 hx
    exact (mem_ordinalCode_iff o b).2 (ho.trans_le lower)

theorem ordinalCode_nat (n : Nat) : ordinalCode (n : Ordinal.{u}) = Forcing.natSetCode n := by
  induction n with
  | zero => exact ordinalCode_zero
  | succ n ih =>
    rw [Nat.cast_add_one, ← Order.succ_eq_add_one, ordinalCode_succ, ih]
    rfl

theorem ordinalCode_omega : ordinalCode Ordinal.omega0 = ZFSet.omega.{u} := by
  apply ZFSet.ext
  intro x
  rw [mem_ordinalCode, Forcing.mem_omega_iff_natSetCode]
  constructor
  · rintro ⟨o, ho, eq⟩
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 ho
    exact ⟨n, eq.symm.trans (ordinalCode_nat n)⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, Ordinal.natCast_lt_omega0 n, ordinalCode_nat n⟩

end PartitionPilot.SetRealization

namespace PartitionPilot.Forcing

open SetRealization
open scoped ZFSet
universe u

theorem ordinalSetProperty_member {x y : ZFSet.{u}}
    (hx : ordinalSetProperty x) (hy : y ∈ x) : ordinalSetProperty y :=
  ⟨hx.2 y hy, fun z hz => hx.2 z (hx.1 y hy z hz)⟩

theorem setTransitive_ordinalCode (o : Ordinal.{u}) : setTransitive (ordinalCode o) := by
  intro y hy z hz
  obtain ⟨b, hb, rfl⟩ := mem_ordinalCode.1 hy
  obtain ⟨a, ha, rfl⟩ := mem_ordinalCode.1 hz
  exact (mem_ordinalCode_iff a o).2 (ha.trans hb)

theorem ordinalSetProperty_ordinalCode (o : Ordinal.{u}) : ordinalSetProperty (ordinalCode o) := by
  refine ⟨setTransitive_ordinalCode o, ?_⟩
  intro y hy
  obtain ⟨a, _, rfl⟩ := mem_ordinalCode.1 hy
  exact setTransitive_ordinalCode a

theorem ordinalSetProperty_eq_code_rank (x : ZFSet.{u}) :
    ordinalSetProperty x → x = ordinalCode (ZFSet.rank x) := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    intro hx
    apply ZFSet.ext
    intro y
    constructor
    · intro hy
      have child := ih y hy (ordinalSetProperty_member hx hy)
      rw [child]
      exact (mem_ordinalCode_iff (ZFSet.rank y) (ZFSet.rank x)).2 (ZFSet.rank_lt_of_mem hy)
    · intro hy
      obtain ⟨o, ho, eq⟩ := mem_ordinalCode.1 hy
      obtain ⟨z, hz, lower⟩ := ZFSet.lt_rank_iff.1 ho
      have child := ih z hz (ordinalSetProperty_member hx hz)
      rcases lt_or_eq_of_le lower with less | equal
      · have member : y ∈ z := by
          rw [child, ← eq]
          exact (mem_ordinalCode_iff o (ZFSet.rank z)).2 less
        exact hx.1 z hz y member
      · have same : z = y := child.trans ((congrArg ordinalCode equal).symm.trans eq)
        exact same ▸ hz

theorem ordinalSetProperty_iff (x : ZFSet.{u}) :
    ordinalSetProperty x ↔ ∃ o : Ordinal.{u}, x = ordinalCode o := by
  constructor
  · intro hx
    exact ⟨ZFSet.rank x, ordinalSetProperty_eq_code_rank x hx⟩
  · rintro ⟨o, rfl⟩
    exact ordinalSetProperty_ordinalCode o

theorem ordinalSetProperty_empty : ordinalSetProperty (∅ : ZFSet.{u}) := by
  rw [← ordinalCode_zero]
  exact ordinalSetProperty_ordinalCode 0

theorem ordinalSetProperty_succ {x : ZFSet.{u}} (hx : ordinalSetProperty x) :
    ordinalSetProperty (insert x x) := by
  obtain ⟨o, rfl⟩ := (ordinalSetProperty_iff x).1 hx
  rw [← ordinalCode_succ]
  exact ordinalSetProperty_ordinalCode (Order.succ o)

theorem ordinalSetProperty_sUnion {x : ZFSet.{u}}
    (members : ∀ y ∈ x, ordinalSetProperty y) : ordinalSetProperty (⋃₀ x) := by
  constructor
  · intro y hy z hz
    obtain ⟨a, ha, ya⟩ := ZFSet.mem_sUnion.1 hy
    exact ZFSet.mem_sUnion.2 ⟨a, ha, (members a ha).1 y ya z hz⟩
  · intro y hy
    obtain ⟨a, ha, ya⟩ := ZFSet.mem_sUnion.1 hy
    exact (members a ha).2 y ya

end PartitionPilot.Forcing

end


namespace PartitionPilot.Forcing
universe u

structure FlatOrdinalCarrierRecursion (stages history levels : ZFSet.{u})
    (candidate tests : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) : Prop where
  function : FunctionGraphOn stages history
  zero : ∅ ∈ stages → ∀ Q, ZFSet.pair ∅ Q ∈ history → ∀ row A,
    ZFSet.pair row A ∈ Q ↔ candidate ∅ row A
  successor : ∀ beta, insert beta beta ∈ stages → ∀ Q Qnext,
    ZFSet.pair beta Q ∈ history → ZFSet.pair (insert beta beta) Qnext ∈ history → ∀ row A,
    ZFSet.pair row A ∈ Qnext ↔ candidate (insert beta beta) row A ∧
      ZFSet.pair row (assignmentCut levels beta A) ∈ Q ∧ tests beta row A
  limit : ∀ beta ∈ stages, beta ≠ ∅ → (∀ gamma, beta ≠ insert gamma gamma) →
    ∀ Q, ZFSet.pair beta Q ∈ history → ∀ row A,
      ZFSet.pair row A ∈ Q ↔ candidate beta row A ∧ FlatHistoryCuts beta history levels row A

namespace FlatOrdinalCarrierRecursion
variable {stages history levels : ZFSet.{u}}
variable {candidate tests : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
variable (recursion : FlatOrdinalCarrierRecursion stages history levels candidate tests)
variable (ordinal : ordinalSetProperty stages)
variable (locality : ∀ beta ∈ stages, ∀ row A,
  tests beta row (assignmentCut levels (insert beta beta) A) ↔ tests beta row A)

include recursion locality

include ordinal in
theorem cuts_of_tests (row A : ZFSet.{u})
    (candidates : ∀ beta ∈ stages, candidate beta row (assignmentCut levels beta A))
    (allTests : ∀ beta ∈ stages, tests beta row A) :
    FlatHistoryCuts stages history levels row A := by
  apply (flatHistoryCuts_lookup_iff recursion.function).2
  intro beta
  induction beta using ZFSet.inductionOn with
  | h beta ih =>
    intro hbeta Q entry
    by_cases zero : beta = ∅
    · subst beta
      exact (recursion.zero hbeta Q entry row _).2 (candidates ∅ hbeta)
    · by_cases successor : ∃ gamma, beta = insert gamma gamma
      · obtain ⟨gamma, rfl⟩ := successor
        have hgamma : gamma ∈ stages := ordinal.1 _ hbeta _ (ZFSet.mem_insert _ _)
        obtain ⟨Qprev, prev⟩ := recursion.function.total hgamma
        apply (recursion.successor gamma hbeta Qprev Q prev entry row _).2
        refine ⟨candidates _ hbeta, ?_, (locality gamma hgamma row A).2 (allTests gamma hgamma)⟩
        rw [assignmentCut_nested (fun _ h => ZFSet.mem_insert_of_mem gamma h)]
        exact ih gamma (ZFSet.mem_insert _ _) hgamma Qprev prev
      · apply (recursion.limit beta hbeta zero (fun gamma equal => successor ⟨gamma, equal⟩)
          Q entry row _).2
        refine ⟨candidates beta hbeta, ?_⟩
        intro gamma hgamma
        have member : gamma ∈ stages := ordinal.1 beta hbeta gamma hgamma
        obtain ⟨Qprev, prev⟩ := recursion.function.total member
        refine ⟨Qprev, prev, ?_⟩
        rw [assignmentCut_nested (ordinal.2 beta hbeta gamma hgamma)]
        exact ih gamma hgamma member Qprev prev

theorem tests_of_cuts
    (successors : ∀ beta ∈ stages, insert beta beta ∈ stages)
    (row A : ZFSet.{u}) (cuts : FlatHistoryCuts stages history levels row A) :
    ∀ beta ∈ stages, tests beta row A := by
  intro beta hbeta
  obtain ⟨Q, entry⟩ := recursion.function.total hbeta
  obtain ⟨Qnext, next, member⟩ := cuts (insert beta beta) (successors beta hbeta)
  exact (locality beta hbeta row A).1
    ((recursion.successor beta (successors beta hbeta) Q Qnext entry next row _).1 member).2.2

include ordinal in
theorem cuts_iff_tests
    (successors : ∀ beta ∈ stages, insert beta beta ∈ stages)
    (row A : ZFSet.{u})
    (candidates : ∀ beta ∈ stages, candidate beta row (assignmentCut levels beta A)) :
    FlatHistoryCuts stages history levels row A ↔ ∀ beta ∈ stages, tests beta row A :=
  ⟨recursion.tests_of_cuts locality successors row A,
    recursion.cuts_of_tests ordinal locality row A candidates⟩

end FlatOrdinalCarrierRecursion

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open scoped ZFSet
universe u

def OrdinalRecursionTrace (R : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (A f : ZFSet.{u}) : Prop :=
  FunctionGraphOn A f ∧ ∀ β ∈ A, ∀ y, ZFSet.pair β y ∈ f → R β (graphRestriction β f) y

namespace OrdinalRecursionTrace

variable {R : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}

theorem restriction_eq_of_common_values {A B C f g : ZFSet.{u}}
    (first : FunctionGraphOn A f) (second : FunctionGraphOn B g)
    (left : C ⊆ A) (right : C ⊆ B)
    (agree : ∀ x ∈ C, ∀ y z, ZFSet.pair x y ∈ f → ZFSet.pair x z ∈ g → y = z) :
    graphRestriction C f = graphRestriction C g := by
  apply ZFSet.ext
  intro w
  constructor
  · intro hw
    obtain ⟨V, function⟩ := first.restrict left
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.1 (function.1 hw)
    obtain ⟨xy, hx⟩ := pair_mem_graphRestriction.1 hw
    obtain ⟨z, xz⟩ := second.total (right hx)
    exact pair_mem_graphRestriction.2 ⟨agree x hx y z xy xz ▸ xz, hx⟩
  · intro hw
    obtain ⟨V, function⟩ := second.restrict right
    obtain ⟨x, _, z, _, rfl⟩ := ZFSet.mem_prod.1 (function.1 hw)
    obtain ⟨xz, hx⟩ := pair_mem_graphRestriction.1 hw
    obtain ⟨y, xy⟩ := first.total (left hx)
    exact pair_mem_graphRestriction.2 ⟨agree x hx y z xy xz ▸ xy, hx⟩

theorem restrict {A B f : ZFSet.{u}} (trace : OrdinalRecursionTrace R A f)
    (ordinalB : ordinalSetProperty B) (subset : B ⊆ A) :
    OrdinalRecursionTrace R B (graphRestriction B f) := by
  refine ⟨trace.1.restrict subset, ?_⟩
  intro β hβ y hy
  have earlier : β ⊆ B := fun x hx => ordinalB.1 β hβ x hx
  rw [graphRestriction_restrict earlier]
  exact trace.2 β (subset hβ) y (pair_mem_graphRestriction.1 hy).1

theorem overlap {A B T f g : ZFSet.{u}}
    (first : OrdinalRecursionTrace R A f) (second : OrdinalRecursionTrace R B g)
    (ordinalA : ordinalSetProperty A) (ordinalB : ordinalSetProperty B)
    (left : A ⊆ T) (_right : B ⊆ T)
    (stepUnique : ∀ β ∈ T, ∀ p, OrdinalRecursionTrace R β p →
      ∀ y z, R β p y → R β p z → y = z) :
    ∀ β ∈ A, β ∈ B → ∀ y z, ZFSet.pair β y ∈ f → ZFSet.pair β z ∈ g → y = z := by
  intro β
  induction β using ZFSet.inductionOn with
  | h β ih =>
    intro hβA hβB y z hy hz
    have beforeA : β ⊆ A := fun x hx => ordinalA.1 β hβA x hx
    have beforeB : β ⊆ B := fun x hx => ordinalB.1 β hβB x hx
    have prefixes : graphRestriction β f = graphRestriction β g :=
      restriction_eq_of_common_values first.1 second.1 beforeA beforeB
        (fun x hx a b xa xb => ih x hx (beforeA hx) (beforeB hx) a b xa xb)
    have prefixTrace := first.restrict (ordinalSetProperty_member ordinalA hβA) beforeA
    have firstStep := first.2 β hβA y hy
    have secondStep := second.2 β hβB z hz
    rw [← prefixes] at secondStep
    exact stepUnique β (left hβA) (graphRestriction β f) prefixTrace y z firstStep secondStep

theorem unique {A T f g : ZFSet.{u}}
    (first : OrdinalRecursionTrace R A f) (second : OrdinalRecursionTrace R A g)
    (ordinalA : ordinalSetProperty A) (subset : A ⊆ T)
    (stepUnique : ∀ β ∈ T, ∀ p, OrdinalRecursionTrace R β p →
      ∀ y z, R β p y → R β p z → y = z) : f = g := by
  have eq := restriction_eq_of_common_values first.1 second.1 (fun _ hx => hx) (fun _ hx => hx)
    (fun x hx y z xy xz => first.overlap second ordinalA ordinalA subset subset stepUnique x hx hx y z xy xz)
  simpa only [first.1.restriction_eq, second.1.restriction_eq] using eq

theorem restriction_insert_last {A B f : ZFSet.{u}} (function : FunctionGraphOn A f)
    (subset : B ⊆ A) (y : ZFSet.{u}) :
    graphRestriction B (insert (ZFSet.pair A y) f) = graphRestriction B f := by
  apply restriction_eq_of_common_values (function.insert (ZFSet.mem_irrefl A) y) function
    (fun _ hx => ZFSet.mem_insert_of_mem A (subset hx)) subset
  intro x hx z w xz xw
  rcases ZFSet.mem_insert_iff.1 xz with eq | xz
  · have same : x = A := (ZFSet.pair_inj.1 eq).1
    exact False.elim (ZFSet.mem_irrefl A (same ▸ subset hx))
  · exact function.unique xz xw

theorem succ {A f y : ZFSet.{u}} (trace : OrdinalRecursionTrace R A f)
    (ordinalA : ordinalSetProperty A) (step : R A f y) :
    OrdinalRecursionTrace R (insert A A) (insert (ZFSet.pair A y) f) := by
  refine ⟨trace.1.insert (ZFSet.mem_irrefl A) y, ?_⟩
  intro β hβ z hz
  rcases ZFSet.mem_insert_iff.1 hβ with eq | hβ
  · subst β
    have value : z = y := (trace.1.insert (ZFSet.mem_irrefl A) y).unique hz
      (ZFSet.mem_insert _ _)
    rw [restriction_insert_last trace.1 (fun _ hx => hx) y, trace.1.restriction_eq, value]
    exact step
  · rw [restriction_insert_last trace.1 (fun x hx => ordinalA.1 β hβ x hx) y]
    rcases ZFSet.mem_insert_iff.1 hz with eq | hz
    · have same : β = A := (ZFSet.pair_inj.1 eq).1
      exact False.elim (ZFSet.mem_irrefl A (same ▸ hβ))
    · exact trace.2 β hβ z hz

theorem sUnion {A T W : ZFSet.{u}} (subset : A ⊆ T)
    (stepUnique : ∀ β ∈ T, ∀ p, OrdinalRecursionTrace R β p →
      ∀ y z, R β p y → R β p z → y = z)
    (members : ∀ f ∈ W, ∃ B, ordinalSetProperty B ∧ B ⊆ A ∧ OrdinalRecursionTrace R B f)
    (cover : ∀ β ∈ A, ∃ f ∈ W, ∃ y, ZFSet.pair β y ∈ f) :
    OrdinalRecursionTrace R A (⋃₀ W) := by
  have agree : ∀ f ∈ W, ∀ g ∈ W, ∀ x y z,
      ZFSet.pair x y ∈ f → ZFSet.pair x z ∈ g → y = z := by
    intro f hf g hg x y z xy xz
    obtain ⟨B, ordinalB, boundB, first⟩ := members f hf
    obtain ⟨C, ordinalC, boundC, second⟩ := members g hg
    exact first.overlap second ordinalB ordinalC (fun _ hx => subset (boundB hx))
      (fun _ hx => subset (boundC hx)) stepUnique x
      (first.1.pair_source xy) (second.1.pair_source xz) y z xy xz
  have function : FunctionGraphOn A (⋃₀ W) := functionGraphOn_sUnion
    (fun f hf => by
      obtain ⟨B, _, bound, trace⟩ := members f hf
      exact ⟨B, bound, trace.1⟩) cover agree
  refine ⟨function, ?_⟩
  intro β _ y hy
  obtain ⟨f, hf, βy⟩ := ZFSet.mem_sUnion.1 hy
  obtain ⟨B, ordinalB, boundB, trace⟩ := members f hf
  have βB := trace.1.pair_source βy
  have beforeB : β ⊆ B := fun x hx => ordinalB.1 β βB x hx
  have prefixes : graphRestriction β (⋃₀ W) = graphRestriction β f := by
    apply restriction_eq_of_common_values function trace.1 (fun _ hx => boundB (beforeB hx)) beforeB
    intro x _ z w xz xw
    obtain ⟨g, hg, xz⟩ := ZFSet.mem_sUnion.1 xz
    exact agree g hg f hf x z w xz xw
  rw [prefixes]
  exact trace.2 β βB y βy

theorem sUnion_successors {A T W : ZFSet.{u}} (ordinalA : ordinalSetProperty A)
    (subset : A ⊆ T)
    (stepUnique : ∀ β ∈ T, ∀ p, OrdinalRecursionTrace R β p →
      ∀ y z, R β p y → R β p z → y = z)
    (members : ∀ f ∈ W, ∃ β ∈ A, OrdinalRecursionTrace R (insert β β) f)
    (cover : ∀ β ∈ A, ∃ f ∈ W, OrdinalRecursionTrace R (insert β β) f) :
    OrdinalRecursionTrace R A (⋃₀ W) := by
  apply sUnion subset stepUnique
  · intro f hf
    obtain ⟨β, hβ, trace⟩ := members f hf
    refine ⟨insert β β, ordinalSetProperty_succ (ordinalSetProperty_member ordinalA hβ), ?_, trace⟩
    intro x hx
    exact (ZFSet.mem_insert_iff.1 hx).elim (fun eq => eq ▸ hβ) (fun hx => ordinalA.1 β hβ x hx)
  · intro β hβ
    obtain ⟨f, hf, trace⟩ := cover β hβ
    obtain ⟨y, βy⟩ := trace.1.total (ZFSet.mem_insert β β)
    exact ⟨f, hf, y, βy⟩

end OrdinalRecursionTrace

end PartitionPilot.Forcing

end OAI
