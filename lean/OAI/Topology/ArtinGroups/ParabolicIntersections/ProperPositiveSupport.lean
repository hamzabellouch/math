import OAI.Topology.ArtinGroups.ParabolicIntersections.PositiveSupport

namespace OAI

/-! The finite-family argument in Lemma 7.6 of paper 082-03. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S)

/-- Common positive extensions preserving a bound, together with the
absence of infinitely many complete passes, give one common proper
support for all permitted continuations of a suitable endpoint. -/
theorem proper_positive_support
    (cancel : ∀ a b c : PositiveArtin M, a*c=b*c → a=b)
    (P : PositiveArtin M → Prop) (hOne : P 1)
    (hcommon : ∀ F : Finset (PositiveArtin M), (∀ a ∈ F, P a) →
      ∃ c, P c ∧ ∀ a ∈ F, ∃ q, c=q*a)
    (hchain : ∀ a b : ℕ → PositiveArtin M, a 0=1 → (∀ n, P (a n)) →
      (∀ n, a (n+1)=b n*a n) → (∀ n, positiveSupport M (b n)=Set.univ) → False) :
    ∃ p, P p ∧ ∃ J : Set S, J ⊂ Set.univ ∧
      ∀ b, P (b*p) → positiveSupport M b ⊆ J := by
  let U (p : PositiveArtin M) : Set S := {s | ∃ b, P (b*p) ∧ s ∈ positiveSupport M b}
  by_contra hgoal
  have hall (p : PositiveArtin M) (hp : P p) : U p=Set.univ := by
    by_contra he
    apply hgoal
    refine ⟨p, hp, U p, lt_of_le_of_ne (Set.subset_univ _) he, ?_⟩
    exact fun b hb s hs => ⟨b, hb, hs⟩
  have hstep (p : PositiveArtin M) (hp : P p) :
      ∃ c b, P c ∧ c=b*p ∧ positiveSupport M b=Set.univ := by
    have hcover (s : S) : ∃ b, P (b*p) ∧ s ∈ positiveSupport M b := by
      have hs : s ∈ U p := by rw [hall p hp]; trivial
      exact hs
    let b : S → PositiveArtin M := fun s => (hcover s).choose
    have hb (s : S) : P (b s*p) ∧ s ∈ positiveSupport M (b s) := (hcover s).choose_spec
    let F : Finset (PositiveArtin M) := insert p (Finset.univ.image (fun s => b s*p))
    obtain ⟨c, hc, hF⟩ := hcommon F (by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hp
      · obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp ha
        exact (hb s).1)
    obtain ⟨q, hq⟩ := hF p (Finset.mem_insert_self _ _)
    refine ⟨c, q, hc, hq, Set.eq_univ_of_forall ?_⟩
    intro s
    obtain ⟨d, hd⟩ := hF (b s*p) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩))
    have he : q=d*b s := cancel q (d*b s) p (hq.symm.trans (hd.trans (mul_assoc _ _ _).symm))
    rw [he, positiveSupport_mul]
    exact Or.inr (hb s).2
  let next (p : {p : PositiveArtin M // P p}) : PositiveArtin M × PositiveArtin M :=
    ((hstep p.val p.property).choose, (hstep p.val p.property).choose_spec.choose)
  have hnext (p : {p : PositiveArtin M // P p}) : P (next p).1 ∧
      (next p).1=(next p).2*p.val ∧ positiveSupport M (next p).2=Set.univ :=
    (hstep p.val p.property).choose_spec.choose_spec
  let a : ℕ → {p : PositiveArtin M // P p} :=
    fun n => Nat.rec ⟨1,hOne⟩ (fun _ p => ⟨(next p).1, (hnext p).1⟩) n
  apply hchain (fun n => (a n).val) (fun n => (next (a n)).2) rfl
    (fun n => (a n).property)
  · intro n
    exact (hnext (a n)).2.1
  · intro n
    exact (hnext (a n)).2.2

end HarmonicArtin.ParabolicIntersections

end OAI
