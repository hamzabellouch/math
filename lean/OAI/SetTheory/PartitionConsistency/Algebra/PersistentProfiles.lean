import Mathlib
import OAI.SetTheory.PartitionConsistency.Algebra.ProbePresentations

namespace OAI

/-! ## Persistence of the full probe profile at successor stages -/


namespace PartitionConsistency.DiagramOrder
universe u v

/-- The full profile of a probe, with downsets taken in the entire monoid
rather than only in the base over which the probe was adjoined. -/
structure ProbeProfile {M : Type u} [Monoid M]
    (a b e m : M) (n : ℕ → M) : Prop where
  exit : m * b = a * e
  not_divides : ¬ m ∣ a
  divisors : ∀ x : M, x ∣ a ∧ x ∣ m ↔ ∃ i : ℕ, x ∣ n i
  joins : ∀ x : M, x ∣ a → ¬ x ∣ m →
    ∀ z : M, x ∣ z ∧ m ∣ z ↔ a * e ∣ z

/-- An old gate controls both old right multiples and intersections with
old cones not containing the new element. In probe normal forms this is
exactly the first-letter exit rule. -/
structure OldGate {M : Type u} {N : Type v} [Monoid M] [Monoid N]
    (f : M →* N) (w : N) (g : M) : Prop where
  divides : w ∣ f g
  old_multiples : ∀ x : M, w ∣ f x ↔ g ∣ x
  intersections : ∀ x : M, ¬ f x ∣ w →
    ∀ z : N, w ∣ z ∧ f x ∣ z ↔ f g ∣ z ∧ f x ∣ z

/-- Only elements with an old right multiple need a gate. For mergers
all such elements are already old, so the second alternative is unused. -/
def HasOldGates {M : Type u} {N : Type v} [Monoid M] [Monoid N]
    (f : M →* N) : Prop :=
  ∀ w : N, (∃ a : M, w ∣ f a) →
    (∃ x : M, f x = w) ∨ ∃ g : M, OldGate f w g

namespace ProbeProfile
variable {M : Type u} {N : Type v} [Monoid M] [Monoid N]
  {a b e m : M} {n : ℕ → M} (h : ProbeProfile a b e m n)
  {f : M →* N} (hf : Conservative f) (hg : HasOldGates f)

include hf hg h

/-- Source `lem:mono-profile-persistence`, successor step.  The new
full downward closure of the original path, not its old set of divisors,
is the profile in the extension. -/
theorem map : ProbeProfile (f a) (f b) (f e) (f m) (f ∘ n) where
  exit := by rw [← f.map_mul, h.exit, f.map_mul]
  not_divides hm := h.not_divides ((hf.dvd_iff m a).1 hm)
  divisors x := by
    constructor
    · rintro ⟨hxa,hxm⟩
      rcases hg x ⟨a,hxa⟩ with ⟨y,rfl⟩ | ⟨g,hg⟩
      · obtain ⟨i,hi⟩ := (h.divisors y).1 ⟨(hf.dvd_iff y a).1 hxa,
          (hf.dvd_iff y m).1 hxm⟩
        exact ⟨i,f.map_dvd hi⟩
      · obtain ⟨i,hi⟩ := (h.divisors g).1 ⟨(hg.old_multiples a).1 hxa,
          (hg.old_multiples m).1 hxm⟩
        exact ⟨i,hg.divides.trans (f.map_dvd hi)⟩
    · rintro ⟨i,hi⟩
      have hni := (h.divisors (n i)).2 ⟨i,dvd_refl _⟩
      exact ⟨hi.trans (f.map_dvd hni.1),hi.trans (f.map_dvd hni.2)⟩
  joins x hxa hxm z := by
    rcases hg x ⟨a,hxa⟩ with ⟨y,rfl⟩ | ⟨g,hg⟩
    · simpa only [f.map_mul] using hf.intersections y m (a * e)
        (h.joins y ((hf.dvd_iff y a).1 hxa) (fun hy => hxm (f.map_dvd hy))) z
    · have hga := (hg.old_multiples a).1 hxa
      have hgm : ¬ g ∣ m := fun hgm => hxm ((hg.old_multiples m).2 hgm)
      have hmx : ¬ f m ∣ x := fun hmx => h.not_divides ((hf.dvd_iff m a).1 (hmx.trans hxa))
      rw [hg.intersections m hmx z]
      simpa only [f.map_mul] using hf.intersections g m (a * e) (h.joins g hga hgm) z

end ProbeProfile
end PartitionConsistency.DiagramOrder

namespace PartitionConsistency.ProbeAlgebra.Path
universe u
open DiagramOrder
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}
  (P : Path M a) (he : e ≠ 1) (b : M)

/-- The gate hypothesis of profile persistence is supplied by the actual
probe extension, including all new words, not just the adjoined generators. -/
theorem hasOldGates (hM : HasConditionalJoins (LeftDivOrder M)) :
    HasOldGates (Word.oldHom (P.alphabet he) b) := by
  intro w hw
  classical
  by_cases ho : ∃ x : M, Word.old (P.alphabet he) b x = w
  · exact Or.inl ho
  · obtain ⟨y,hy⟩ := hw
    cases hs : Word.head (P.alphabet he) b w with
    | none => exact (ho (by
        obtain ⟨x,hx⟩ := (Word.head_eq_none_iff _ _ w).1 hs
        exact ⟨x,hx.symm⟩)).elim
    | some s =>
      obtain ⟨g,hg⟩ := Word.exists_gate_of_exit (P.alphabet he) b (P.oldIntersections he b hM)
        w hs hy (by intro h; cases h)
      refine Or.inr ⟨g,Word.Gate.dvd _ _ hg,Word.Gate.dvd_old_iff _ _ hg,?_⟩
      intro x hx z
      change (w ∣ z ∧ Word.old (P.alphabet he) b x ∣ z) ↔
        Word.old (P.alphabet he) b g ∣ z ∧ Word.old (P.alphabet he) b x ∣ z
      simpa only [and_comm] using Word.Gate.old_intersection _ _ hg hs
        (fun hd => hx ((Word.old_dvd_iff_headDiv _ _ x w).2 hd)) z

/-- The profile initially holds with all downsets in the new monoid. -/
theorem probeProfile (hM : HasConditionalJoins (LeftDivOrder M)) (hb : b ≠ 1) :
    ProbeProfile (Word.old (P.alphabet he) b a) (Word.old (P.alphabet he) b b)
      (Word.old (P.alphabet he) b e) (P.probe he b hb 0)
      (fun i => Word.old (P.alphabet he) b (P.node i)) where
  exit := P.probe_zero_mul_b he b hb
  not_divides := P.probe_not_dvd_a he b hb
  divisors x := by simpa only [and_comm] using P.probe_full_profile he b hb hM x
  joins x hxa hxm z := P.probe_join_profile he b hb hM hxa hxm z

/-- The same profile survives a later probe operation, whose parameters
need have no relation to the parameters of the original probe. -/
theorem preserve_profile (hM : HasConditionalJoins (LeftDivOrder M))
    {a₀ b₀ e₀ m₀ : M} {n₀ : ℕ → M} (h : ProbeProfile a₀ b₀ e₀ m₀ n₀) :
    ProbeProfile (Word.old (P.alphabet he) b a₀) (Word.old (P.alphabet he) b b₀)
      (Word.old (P.alphabet he) b e₀) (Word.old (P.alphabet he) b m₀)
      (fun i => Word.old (P.alphabet he) b (n₀ i)) :=
  h.map (P.oldHom_conservative he b) (P.hasOldGates he b hM)

end PartitionConsistency.ProbeAlgebra.Path

namespace PartitionConsistency.MergerAlgebra.Word
universe u v
open DiagramOrder
variable {M : Type u} {D : Type v} [Monoid M] [RightFreeAction M D]

/-- A merger introduces no new divisor of any old element. -/
theorem hasOldGates : HasOldGates (oldHom : M →* Word M D) := by
  rintro w ⟨a,q,hq⟩
  obtain ⟨x,y,hx,hy,hxy⟩ := factors_of_old hq.symm
  exact Or.inl ⟨x,hx.symm⟩

/-- Source profile persistence for a merger successor. -/
theorem preserve_profile {a b e m : M} {n : ℕ → M} (h : ProbeProfile a b e m n) :
    ProbeProfile (old a : Word M D) (old b) (old e) (old m) (fun i => old (n i)) :=
  h.map oldHom_conservative hasOldGates

end PartitionConsistency.MergerAlgebra.Word

end OAI
