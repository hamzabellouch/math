import OAI.Topology.ArtinGroups.ParabolicIntersections.SphericalGap
import OAI.Topology.ArtinGroups.Complexes.PositiveWordLowerBound
import OAI.Topology.ArtinGroups.Complexes.InverseWordAction

namespace OAI

/-! Bounded total height forbids infinitely many complete positive passes. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A) [Fintype V] [Fintype A]
  [DecidableEq V] [DecidableEq A]

lemma positiveWord_generator_exterior (w : List V) (x : FiniteHomotopyClass Q (K := ℂ))
    (U : Set V) (hw : ∀ v ∈ w, v ∈ U) (p : GeneratorPlacement V) (hp : p.color ∉ U) :
    classGeneratorArray Q (positiveWordAction Q w x) p = classGeneratorArray Q x p := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    change classGeneratorArray Q (classPositiveTwist Q v (positiveWordAction Q w x)) p = _
    rw [classPositiveTwist_exterior Q _ v p (fun he => hp (he ▸ hw v (by simp)))]
    exact ih (fun a ha => hw a (List.mem_cons_of_mem v ha))

lemma classPositiveTwist_outside_placement (x : FiniteHomotopyClass Q (K := ℂ))
    (U : Set V) (v : V) (hv : v ∈ U) (P : GeneratorPlacement V → Prop)
    (h : ∀ i, ((minimalClassModel Q x).complex.placement i).color ∉ U →
      P ((minimalClassModel Q x).complex.placement i)) :
    ∀ i, ((minimalClassModel Q (classPositiveTwist Q v x)).complex.placement i).color ∉ U →
      P ((minimalClassModel Q (classPositiveTwist Q v x)).complex.placement i) := by
  let E := minimalClassModel Q x
  let F := E.complex.positiveTwist Q v
  have hx : classOfComplex Q F = classPositiveTwist Q v x := by
    change classPositiveTwist Q v (classOfComplex Q E.complex) = _
    exact congrArg (classPositiveTwist Q v) (minimalClassModel_class Q x)
  rw [← hx]
  apply minimal_bound_transport Q F _ (minimalClassModel_minimal Q _)
    (minimalClassModelEquivalence Q F).symm (fun p => p.color ∉ U → P p)
  intro i hi
  rcases i with i | i
  · exact (hi hv).elim
  · exact h i hi

lemma positiveWord_outside_placement (w : List V) (x : FiniteHomotopyClass Q (K := ℂ))
    (U : Set V) (hw : ∀ v ∈ w, v ∈ U) (P : GeneratorPlacement V → Prop)
    (h : ∀ i, ((minimalClassModel Q x).complex.placement i).color ∉ U →
      P ((minimalClassModel Q x).complex.placement i)) :
    ∀ i, ((minimalClassModel Q (positiveWordAction Q w x)).complex.placement i).color ∉ U →
      P ((minimalClassModel Q (positiveWordAction Q w x)).complex.placement i) := by
  induction w with
  | nil => exact h
  | cons v w ih =>
    exact classPositiveTwist_outside_placement Q _ U v (hw v (by simp)) P
      (ih (fun a ha => hw a (List.mem_cons_of_mem v ha)))

lemma positiveWord_allTests_reflect (hn : ∀ a, Q.source a ≠ Q.target a)
    (w : List V) (x : FiniteHomotopyClass Q (K := ℂ)) (U : Set V)
    (hw : ∀ v ∈ w, v ∈ U)
    (h : ∀ α ∈ U, ∀ l c, ClassTestExact Q α l c (positiveWordAction Q w x)) :
    ∀ α ∈ U, ∀ l c, ClassTestExact Q α l c x := by
  have href : ∀ t, ClassTestUpper Q (positiveWordAction Q w x) U t →
      ClassTestUpper Q x U t := by
    clear h
    intro t
    induction w with
    | nil => exact id
    | cons v w ih =>
      intro ht
      exact ih (fun a ha => hw a (List.mem_cons_of_mem v ha))
        (classPositiveTwist_testUpper_reflect Q hn _ U v (hw v (by simp)) ht)
  intro α hα l c
  exact href (l-1) (fun β hβ k _ d => h β hβ k d) α hα l (by omega) c

omit [Fintype V] [DecidableEq A] in
lemma generatorArray_positive_iff (x : FiniteHomotopyClass Q (K := ℂ))
    (p : GeneratorPlacement V) :
    0 < classGeneratorArray Q x p ↔ ∃ i : (minimalClassModel Q x).Index,
      (minimalClassModel Q x).complex.placement i = p := by
  have he := congrArg (fun a => a p)
    (classGeneratorArray_of_minimal Q (minimalClassModel Q x) (minimalClassModel_minimal Q x))
  rw [minimalClassModel_class Q x] at he
  rw [he, generatorArray_apply]
  change 0 < Nat.card {i : (minimalClassModel Q x).Index //
      (minimalClassModel Q x).complex.placement i = p} ↔ _
  rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff]
  exact nonempty_subtype

/-- Proposition 7.4 for actual positive vertex operations. The only
published input is the abstract mesh-algebra path identity. -/
theorem no_bounded_complete_positive_chain (hn : ∀ a, Q.source a ≠ Q.target a)
    (U : Set V) (hmesh : MeshNilpotent Q U)
    (x : ℕ → FiniteHomotopyClass Q (K := ℂ)) (w : ℕ → List V)
    (hstep : ∀ n, x (n+1) = positiveWordAction Q (w n) (x n))
    (hw : ∀ n v, v ∈ w n ↔ v ∈ U)
    (hdim : classHomDimension Q 0 0 (x 0) (x 0) ≤ 1)
    (hframe : ∃ p : GeneratorPlacement V, p.color ∉ U ∧ 0 < classGeneratorArray Q (x 0) p)
    (hnonzero : ¬ ∀ α ∈ U, ∀ l c, ClassTestExact Q α l c (x 0))
    (t : ℤ) (ht : ∀ n, ClassTestUpper Q (x n) U t) : False := by
  cases Subsingleton.elim (inferInstance : DecidableEq V) (Classical.decEq V)
  cases Subsingleton.elim (inferInstance : DecidableEq A) (Classical.decEq A)
  obtain ⟨frame, hframeU, hframe⟩ := hframe
  obtain ⟨d₁, hd₁⟩ := Finite.bddBelow_range
    (fun i : (minimalClassModel Q (x 0)).Index =>
      ((minimalClassModel Q (x 0)).complex.placement i).level)
  obtain ⟨b, hb⟩ := Finite.bddAbove_range
    (fun i : (minimalClassModel Q (x 0)).Index =>
      ((minimalClassModel Q (x 0)).complex.placement i).level)
  obtain ⟨p, hp⟩ := Finite.bddBelow_range
    (fun i : (minimalClassModel Q (x 0)).Index =>
      ((minimalClassModel Q (x 0)).complex.placement i).cochain)
  obtain ⟨m, hm⟩ := classTestCochainUpper_exists Q (x 0) U
  let d₂ := max b (t-2)
  have hstate : ∀ n,
      ClassLowerBound Q d₁ (x n) ∧ ClassOutsideCap Q (x n) U d₂ ∧
      (∀ i, ((minimalClassModel Q (x n)).complex.placement i).color ∉ U →
        p ≤ ((minimalClassModel Q (x n)).complex.placement i).cochain) ∧
      classGeneratorArray Q (x n) frame = classGeneratorArray Q (x 0) frame ∧
      classHomDimension Q 0 0 (x n) (x n) ≤ 1 ∧
      ClassTestCochainUpper Q (x n) U (m-n) ∧
      ¬ (∀ α ∈ U, ∀ l c, ClassTestExact Q α l c (x n)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun i => hd₁ (Set.mem_range_self i),
        fun i _ => (hb (Set.mem_range_self i)).trans (le_max_left _ _),
        fun i _ => hp (Set.mem_range_self i), rfl, hdim, ?_, hnonzero⟩
      simpa only [Int.natCast_zero, sub_zero] using hm
    | succ n ih =>
      rw [hstep n]
      refine ⟨positiveWord_lower_bound Q _ _ ih.1,
        positiveWord_outside_cap Q _ _ U d₂ (fun a ha => (hw n a).mp ha) ih.2.1,
        positiveWord_outside_placement Q _ _ U (fun a ha => (hw n a).mp ha)
          (fun q => p ≤ q.cochain) ih.2.2.1,
        (positiveWord_generator_exterior Q _ _ U (fun a ha => (hw n a).mp ha)
          frame hframeU).trans ih.2.2.2.1, ?_, ?_, ?_⟩
      · rw [positiveWord_homDimension Q hn]
        exact ih.2.2.2.2.1
      · have hh := positiveWord_complete_cochain_drop Q hn (w n) (x n) U (hw n)
          (m-n) ih.2.2.2.2.2.1
        convert hh using 1
        push_cast
        ring
      · intro h
        exact ih.2.2.2.2.2.2 (positiveWord_allTests_reflect Q hn _ _ U
          (fun a ha => (hw n a).mp ha) h)
  have hupper (n : ℕ) : ClassUpperBound Q d₂ (x n) := by
    apply classUpperBound_of_test_and_outside Q _ U d₂ _ (hstate n).2.1
    intro α hα l hl c
    exact ht n α hα l (by have := le_max_right b (t-2); dsimp only [d₂] at hl; omega) c
  obtain ⟨j₀, hj₀⟩ := (generatorArray_positive_iff Q (x 0) frame).mp hframe
  have hdd : d₁ ≤ d₂ := (hstate 0).1 j₀ |>.trans (hupper 0 j₀)
  obtain ⟨N, _, hbound⟩ := cochain_lower_obstruction_of_mesh Q U hmesh
  let l := p-1-N*(d₂-d₁+1)
  let n := (m-l+1).toNat
  have hn : m-(n:ℤ) < l := by
    dsimp only [n]
    have : m-l+1 ≤ ((m-l+1).toNat : ℤ) := by omega
    omega
  have hs := hstate n
  apply hs.2.2.2.2.2.2
  rw [← minimalClassModel_class Q (x n)]
  apply hbound _ (minimalClassModel Q (x n)).complex (minimalClassModel_minimal Q (x n))
    (by rw [minimalClassModel_homDimension]; exact hs.2.2.2.2.1) d₁ d₂ p hdd
    (fun i => ⟨hs.1 i, hupper n i⟩) hs.2.2.1
  · obtain ⟨j, hj⟩ := (generatorArray_positive_iff Q (x n) frame).mp
      (by rw [hs.2.2.2.1]; exact hframe)
    refine ⟨j, ?_⟩
    have hext : p ≤ frame.cochain := by
      rw [← hj₀]
      exact hp (Set.mem_range_self j₀)
    rwa [hj]
  · intro α hα d c hc
    have hh := hs.2.2.2.2.2.1 α hα d c (by change l ≤ c at hc; omega)
    rwa [← minimalClassModel_class Q (x n)] at hh

end HarmonicArtin.ParabolicIntersections

end OAI
