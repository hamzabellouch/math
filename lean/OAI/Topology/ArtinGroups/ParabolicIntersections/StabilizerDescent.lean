import OAI.Topology.ArtinGroups.ParabolicIntersections.Consequences

namespace OAI

/-!
# The rank induction in §8 of paper 082-03

The finite-rank induction is proved here for an actual group action.
`ReductionAt` records the three alternatives that the paper obtains from
its new relative-height arguments. It is deliberately not called a
published input: constructing these alternatives for the categorical
action is still required before this module implies the main theorem.
-/

namespace HarmonicArtin.ParabolicIntersections

variable {S : Type*} (M : CoxeterMatrix S)
variable {V : Type*} [MulAction (Artin M) V] (v : V)

/-- Stabilizer of the transported family, restricted to a standard subgroup.
For a family of homotopy classes, take `V` to be the product of the classes. -/
def relativeStabilizer (Y : Set S) (x : Artin M) : Subgroup (Artin M) :=
  artinParabolic M Y ⊓ MulAction.stabilizer (Artin M) (x • v)

@[simp] theorem mem_relativeStabilizer (Y : Set S) (x a : Artin M) :
    a ∈ relativeStabilizer M v Y x ↔
      a ∈ artinParabolic M Y ∧ a • (x • v) = x • v := Iff.rfl

theorem conjugate_stabilizer (b x : Artin M) :
    conjugate b (MulAction.stabilizer (Artin M) (x • v)) =
      MulAction.stabilizer (Artin M) ((b * x) • v) := by
  ext a
  rw [mem_conjugate, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  rw [← smul_left_cancel_iff b]
  simp only [← mul_smul, mul_assoc, mul_inv_cancel_left]

/-- Lemma 8.1: a containing smaller parabolic removes the ambient
intersection after conjugation. -/
theorem relativeStabilizer_conjugation (Y D : Set S) (b x : Artin M)
    (hD : D ⊆ Y) (hb : b ∈ artinParabolic M Y)
    (hcontain : relativeStabilizer M v Y x ≤ conjugate b⁻¹ (artinParabolic M D)) :
    conjugate b (relativeStabilizer M v Y x) = relativeStabilizer M v D (b * x) := by
  have hsmall : conjugate b (relativeStabilizer M v Y x) ≤ artinParabolic M D := by
    have h := conjugate_mono b hcontain
    simpa [← conjugate_mul] using h
  have hlarge : artinParabolic M D ≤ artinParabolic M Y := standard_mono M hD
  have he : conjugate b (relativeStabilizer M v Y x) =
      artinParabolic M Y ⊓ MulAction.stabilizer (Artin M) ((b * x) • v) := by
    rw [relativeStabilizer, conjugate_inf, conjugate_eq_self hb, conjugate_stabilizer]
  apply le_antisymm
  · exact le_inf hsmall (he.le.trans inf_le_right)
  · rw [he]
    exact inf_le_inf hlarge le_rfl

/-- The alternatives furnished by the spherical positive-height reduction
and the nonspherical harmonic-minimum reduction. The split case expresses
the invisible direct factor, including its normalization property. -/
inductive ReductionAt (Y : Set S) (x : Artin M) : Prop
  | fixed : relativeStabilizer M v Y x = artinParabolic M Y → ReductionAt Y x
  | smaller (D : Set S) (b : Artin M) :
      D ⊂ Y → b ∈ artinParabolic M Y →
      relativeStabilizer M v Y x ≤ conjugate b⁻¹ (artinParabolic M D) → ReductionAt Y x
  | split (T K : Set S) :
      T ⊂ Y → K ⊆ Y →
      (∀ c ∈ artinParabolic M T, conjugate c (artinParabolic M K) = artinParabolic M K) →
      relativeStabilizer M v Y x = artinParabolic M K ⊔ relativeStabilizer M v T x →
      ReductionAt Y x

variable [Finite S]

/-- Theorem 8.2's rank induction. The genuinely new local alternatives are
an explicit premise, so this is not advertised as the completed theorem. -/
theorem relativeStabilizers_of_reductions
    (hred : ∀ (Y : Set S) (x : Artin M), ReductionAt M v Y x)
    (Y : Set S) (x : Artin M) :
    ∃ (R : Set S) (c : Artin M), R ⊆ Y ∧ c ∈ artinParabolic M Y ∧
      relativeStabilizer M v Y x = conjugate c⁻¹ (artinParabolic M R) := by
  suffices h : ∀ n : ℕ, ∀ Y : Set S, Y.ncard = n → ∀ x : Artin M,
      ∃ (R : Set S) (c : Artin M), R ⊆ Y ∧ c ∈ artinParabolic M Y ∧
        relativeStabilizer M v Y x = conjugate c⁻¹ (artinParabolic M R) from h _ Y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Y hY x
    rcases hred Y x with hfixed | ⟨D, b, hD, hb, hcontain⟩ | ⟨T, K, hT, hK, hnorm, hsplit⟩
    · refine ⟨Y, 1, Set.Subset.rfl, (artinParabolic M Y).one_mem, ?_⟩
      simpa using hfixed
    · have hlt : D.ncard < n := hY ▸ Set.ncard_lt_ncard hD
      obtain ⟨R, c, hRD, hc, he⟩ := ih _ hlt D rfl (b * x)
      have hconj := relativeStabilizer_conjugation M v Y D b x hD.subset hb hcontain
      have heq := congrArg (conjugate b⁻¹) (hconj.trans he)
      refine ⟨R, c * b, hRD.trans hD.subset,
        (artinParabolic M Y).mul_mem (standard_mono M hD.subset hc) hb, ?_⟩
      simpa only [← conjugate_mul, inv_mul_cancel, conjugate_one, mul_inv_rev] using heq
    · have hlt : T.ncard < n := hY ▸ Set.ncard_lt_ncard hT
      obtain ⟨R, c, hRT, hc, he⟩ := ih _ hlt T rfl x
      have hn := hnorm c⁻¹ ((artinParabolic M T).inv_mem hc)
      refine ⟨K ∪ R, c, Set.union_subset hK (hRT.trans hT.subset),
        standard_mono M hT.subset hc, ?_⟩
      rw [hsplit, he, standard_union, conjugate_sup, hn]

/-- Once the relative categorical action has its initial stabilizer and
local reductions, its stabilizer induction gives the inside intersection.
Neither of those new categorical assertions is installed as an axiom. -/
theorem inside_at_of_action_reductions (X Y : Set S) (g : Artin M)
    (hinit : MulAction.stabilizer (Artin M) v = artinParabolic M X)
    (hred : ∀ (D : Set S) (x : Artin M), ReductionAt M v D x) :
    ∃ (R : Set S) (c : Artin M), R ⊆ Y ∧ c ∈ artinParabolic M Y ∧
      artinParabolic M Y ⊓ conjugate g (artinParabolic M X) =
        conjugate c (artinParabolic M R) := by
  obtain ⟨R, c, hR, hc, he⟩ := relativeStabilizers_of_reductions M v hred Y g
  refine ⟨R, c⁻¹, hR, (artinParabolic M Y).inv_mem hc, ?_⟩
  have hg := conjugate_stabilizer M v g 1
  simp only [one_smul, mul_one, hinit] at hg
  simpa only [relativeStabilizer, ← hg] using he

end HarmonicArtin.ParabolicIntersections

end OAI
