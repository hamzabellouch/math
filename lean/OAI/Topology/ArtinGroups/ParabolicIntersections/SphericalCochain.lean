import OAI.Topology.ArtinGroups.Complexes.PositiveWordActionTest
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedFamily

namespace OAI

/-! The ordinary cochain bound in Lemma 7.2 of paper 082-03. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-- Unlike `ClassTestUpper`, this bounds ordinary cochain degree, uniformly
in total degree. -/
def ClassTestCochainUpper (x : FiniteHomotopyClass Q (K := K)) (U : Set V) (m : ℤ) : Prop :=
  ∀ α ∈ U, ∀ l c : ℤ, m < c → ClassTestExact Q α l c x

lemma classTestCochainUpper_mono (x : FiniteHomotopyClass Q (K := K)) (U : Set V)
    {m n : ℤ} (hmn : m ≤ n) (h : ClassTestCochainUpper Q x U m) :
    ClassTestCochainUpper Q x U n :=
  fun α hα l c hc => h α hα l c (hmn.trans_lt hc)

lemma classTestCochainUpper_positive (hn : ∀ a, Q.source a ≠ Q.target a)
    (x : FiniteHomotopyClass Q (K := K)) (U : Set V) (α : V) (hα : α ∈ U)
    (m : ℤ) (h : ClassTestCochainUpper Q x U m) :
    ClassTestCochainUpper Q (classPositiveTwist Q α x) U m := by
  intro β hβ l c hc
  by_cases he : β = α
  · subst β
    apply (classTestExact_positive_self Q hn x α l c).mpr
    exact h α hα (l-1) (c+1) (by omega)
  · exact classTestExact_positive_other Q x α β he l c
      (h α hα l (c+1) (by omega)) (h β hβ l c hc)

lemma positiveWord_cochain_bounds (hn : ∀ a, Q.source a ≠ Q.target a)
    (w : List V) (x : FiniteHomotopyClass Q (K := K)) (U : Set V)
    (hw : ∀ α ∈ w, α ∈ U) (m : ℤ) (h : ClassTestCochainUpper Q x U m) :
    ClassTestCochainUpper Q (positiveWordAction Q w x) U m ∧
      ∀ α ∈ w, ∀ l c : ℤ, m-1 < c →
        ClassTestExact Q α l c (positiveWordAction Q w x) := by
  induction w with
  | nil => exact ⟨h, fun _ hα => (List.not_mem_nil hα).elim⟩
  | cons α w ih =>
    obtain ⟨hbound, himproved⟩ := ih (fun β hβ => hw β (List.mem_cons_of_mem α hβ))
    refine ⟨classTestCochainUpper_positive Q hn _ U α (hw α (by simp)) m hbound, ?_⟩
    intro β hβ l c hc
    change ClassTestExact Q β l c (classPositiveTwist Q α (positiveWordAction Q w x))
    by_cases he : β = α
    · subst β
      apply (classTestExact_positive_self Q hn _ α l c).mpr
      exact hbound α (hw α (by simp)) (l-1) (c+1) (by omega)
    · apply classTestExact_positive_other Q _ α β he l c
      · exact hbound α (hw α (by simp)) l (c+1) (by omega)
      · exact himproved β ((List.mem_cons.mp hβ).resolve_left he) l c hc

/-- A pass containing every operated vertex lowers the ordinary cochain
bound by one. This is proved from the actual twist test formulas. -/
theorem positiveWord_complete_cochain_drop (hn : ∀ a, Q.source a ≠ Q.target a)
    (w : List V) (x : FiniteHomotopyClass Q (K := K)) (U : Set V)
    (hw : ∀ α, α ∈ w ↔ α ∈ U) (m : ℤ) (h : ClassTestCochainUpper Q x U m) :
    ClassTestCochainUpper Q (positiveWordAction Q w x) U (m-1) := by
  have hh := (positiveWord_cochain_bounds Q hn w x U (fun α hα => (hw α).mp hα) m h).2
  exact fun α hα => hh α ((hw α).mpr hα)

omit [Fintype V] [DecidableEq A] in
lemma scalarExact_of_absent_cochain {I : Type} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K := K) I) (α : V) (l c : ℤ)
    (h : ∀ i, (E.placement i).cochain ≠ c) : ScalarExactAt Q E α l c := by
  intro x hx _
  have hz : x = 0 := by
    funext i
    exact hx i (fun hi => h i hi.2)
  refine ⟨0, fun _ _ => rfl, ?_⟩
  rw [Matrix.zero_vecMul, hz]

/-- Every bounded family admits an ordinary cochain upper bound. -/
theorem classTestCochainUpper_exists (x : FiniteHomotopyClass Q (K := K)) (U : Set V) :
    ∃ m : ℤ, ClassTestCochainUpper Q x U m := by
  induction x using Quotient.inductionOn with
  | _ E =>
    obtain ⟨m, hm⟩ := Finite.bddAbove_range (fun i : E.Index => (E.complex.placement i).cochain)
    refine ⟨m, ?_⟩
    intro α _ l c hc
    change ScalarExactAt Q (E.complex.testComplex Q α) α l c
    apply scalarExact_of_absent_cochain Q
    intro i hi
    have hle := hm (Set.mem_range_self i.1)
    change (E.complex.placement i.1).cochain = c at hi
    omega

end HarmonicArtin.ParabolicIntersections

end OAI
