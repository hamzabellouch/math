import OAI.RingTheory.DirectFiniteness.PrescribedIncidence

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

abbrev Affine (h : Input) := Fin (dimension h.val) → Q h
abbrev Pair (h : Input) := Finset (Affine h) × Finset (Finset (Affine h))

/-- Coordinate-lex order, then indicator order for points and lines,
then indicator order for families, finally lexicographic order of the pair.
Discarding the non-full-line candidates does not change relative order. -/
@[instance_reducible] def pairOrder (h : Input) : LinearOrder (Pair h) :=
  letI : LinearOrder (Affine h) := vectorOrder
  letI : LinearOrder (Finset (Affine h)) := subsetOrder _
  letI : LinearOrder (Finset (Finset (Affine h))) := subsetOrder _
  LinearOrder.lift' (toLex : Pair h → Lex (Pair h)) (fun _ _ he => he)

def Test (h : Input) (p : Pair h) : Prop :=
  Successful (enumeration h) (prime h.val) p

def Succeeds (h : ℕ) : Prop := ∃ hh : 2 ≤ h, ∃ p, Test ⟨h,hh⟩ p

lemma succeeds217 : Succeeds 217 := by
  refine ⟨by decide,?_⟩
  let h : Input := ⟨217,by decide⟩
  have hs := succeeds_217 (Q h) (Q_card h) (enumeration h)
  have hn : dimension h.val=1200 := dimension_217
  have hp : prime h.val=FiniteGeometry.sourcePrime := prime_217
  unfold Test
  change ∃ p : Finset (Fin (dimension h.val) → Q h) ×
    Finset (Finset (Fin (dimension h.val) → Q h)), Successful (enumeration h) (prime h.val) p
  rw [hn,hp]
  exact hs

local instance : DecidablePred Succeeds := Classical.decPred _

/-- The exact least successful outer input, not the convenient existence bound 217. -/
def selectedH : ℕ := Nat.find (show ∃ h, Succeeds h from ⟨217,succeeds217⟩)
lemma selectedH_spec : Succeeds selectedH := Nat.find_spec _
lemma selectedH_le (h : ℕ) (hh : Succeeds h) : selectedH ≤ h := Nat.find_min' _ hh
lemma selectedH_ge : 2 ≤ selectedH := selectedH_spec.choose
lemma selectedH_le217 : selectedH ≤ 217 := selectedH_le 217 succeeds217

def selectedInput : Input := ⟨selectedH,selectedH_ge⟩
lemma selectedInput_success : ∃ p, Test selectedInput p := selectedH_spec.choose_spec

/-- The first successful pair in the literal finite lexicographic search. -/
def selectedPair : Pair selectedInput :=
  letI := pairOrder selectedInput
  first (Test selectedInput) selectedInput_success

lemma selectedPair_spec : Test selectedInput selectedPair := by
  let _ := pairOrder selectedInput
  exact first_spec (Test selectedInput) selectedInput_success
lemma selectedPair_minimal (p : Pair selectedInput) (hp : Test selectedInput p) :
    @LE.le _ (pairOrder selectedInput).toLE selectedPair p := by
  let _ := pairOrder selectedInput
  exact first_le (Test selectedInput) selectedInput_success p hp

/-- Formal termination certificate for both the outer loop and its finite inner loop. -/
theorem finite_search_terminates :
    2 ≤ selectedH ∧ selectedH ≤ 217 ∧ Test selectedInput selectedPair ∧
      (∀ h, Succeeds h → selectedH ≤ h) ∧
      (∀ p, Test selectedInput p → @LE.le _ (pairOrder selectedInput).toLE selectedPair p) :=
  ⟨selectedH_ge,selectedH_le217,selectedPair_spec,selectedH_le,selectedPair_minimal⟩

end KaplanskyCounterexample.Prescription
end

end OAI
