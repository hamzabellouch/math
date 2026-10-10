import Mathlib
import OAI.SetTheory.PartitionConsistency.Algebra.DirectLimits

namespace OAI

/-! ## Finite descent through a continuous tower of old gates -/

namespace PartitionConsistency.DiagramOrder

universe u v
variable {T : Type u} [Monoid T]

/-- The no-new-divisors alternative at a successor stage. All divisibility
statements are in the ambient final monoid. -/
def NoNewOldDivisors (B C : Submonoid T) : Prop :=
  ∀ w ∈ C, (∃ y ∈ B, w ∣ y) → w ∈ B

/-- The least-old-multiple alternative at a successor stage, including the
old-input implication used for descent. The new word must belong to the
successor stage; arbitrary elements of the final monoid are not called new
at this stage. -/
def OldGateStep (B C : Submonoid T) : Prop :=
  ∀ w ∈ C, w ∉ B → (∃ y ∈ B, w ∣ y) →
    ∃ g ∈ B, w ∣ g ∧ (∀ y ∈ B, w ∣ y → g ∣ y) ∧
      ∀ d ∈ B, g ∣ w * d → w * d ∈ B

/-- A continuous concrete tower with the two successor alternatives of
`thm:monoid`. Terminal segments may be constant. The successor alternatives
are recorded in the final divisibility relation, as allowed by conservative
embeddings in the source. This definition is not an existence assertion. -/
structure GateTower (T : Type u) [Monoid T] where
  stage : Ordinal.{v} → Submonoid T
  monotone : Monotone stage
  continuous : ∀ ω, Order.IsSuccLimit ω → ∀ x,
    x ∈ stage ω ↔ ∃ α < ω, x ∈ stage α
  step : ∀ α, NoNewOldDivisors (stage α) (stage (α + 1)) ∨
    OldGateStep (stage α) (stage (α + 1))

/-- A single admissible replacement, with both endpoints in the stipulated
set of alignments. Its right factor is the same as that of the path indices. -/
def Replaces (n : ℕ → T) (A : Set (ℕ × T)) (p q : ℕ × T) : Prop :=
  p ∈ A ∧ q ∈ A ∧ p.1 ≤ q.1 ∧ ∃ d, n p.1 * d = n q.1 ∧ p.2 * d = q.2

namespace GateTower
variable (S : GateTower.{u,v} T) (n : ℕ → T) (A : Set (ℕ × T))

/-- The finite descent in `lem:mono-descent`. The proof is by induction on
stages. Hence its result is an actual finite chain of admissible replacements,
not an appeal to the absence of an infinite decreasing sequence alone.
Countability of the initial stage is not needed for this descent. -/
theorem finite_descent
    (hn : ∀ i, n i ∈ S.stage 0)
    (hq : ∀ i j d, n i * d = n j → d ∈ S.stage 0)
    (hbound : ∀ p ∈ A, ∃ N, p.2 ∣ n N)
    (hreplace : ∀ p ∈ A, ∀ N, ∃ l' d,
      (l', p.2 * d) ∈ A ∧ p.1 ≤ l' ∧ n p.1 * d = n l' ∧ n N ∣ p.2 * d)
    (α : Ordinal.{v}) (p : ℕ × T) (hp : p ∈ A) (hα : p.2 ∈ S.stage α) :
    ∃ q ∈ A, q.2 ∈ S.stage 0 ∧ Relation.ReflTransGen (Replaces n A) p q := by
  classical
  induction α using Ordinal.limitRecOn generalizing p with
  | zero => exact ⟨p,hp,hα,Relation.ReflTransGen.refl⟩
  | add_one α ih =>
    by_cases ho : p.2 ∈ S.stage α
    · exact ih p hp ho
    obtain ⟨N,hN⟩ := hbound p hp
    have hnN : n N ∈ S.stage α := S.monotone (zero_le : (0 : Ordinal.{v}) ≤ α) (hn N)
    cases S.step α with
    | inl hnone => exact False.elim (ho (hnone p.2 hα ⟨n N,hnN,hN⟩))
    | inr hgates =>
      obtain ⟨g,_,_,hleast,hgate⟩ := hgates p.2 hα ho ⟨n N,hnN,hN⟩
      obtain ⟨l',d,hA',hll',hd,hNd⟩ := hreplace p hp N
      have hdo : d ∈ S.stage α := S.monotone (zero_le : (0 : Ordinal.{v}) ≤ α) (hq _ _ d hd)
      have hnew : p.2 * d ∈ S.stage α := hgate d hdo ((hleast _ hnN hN).trans hNd)
      obtain ⟨q,hqA,hq0,hpath⟩ := ih (l',p.2 * d) hA' hnew
      refine ⟨q,hqA,hq0,?_⟩
      have hstep : Replaces n A p (l',p.2 * d) := ⟨hp,hA',hll',d,hd,rfl⟩
      exact (Relation.ReflTransGen.single hstep).trans hpath
  | limit ω hω ih =>
    obtain ⟨α,hαω,hmem⟩ := (S.continuous ω hω p.2).1 hα
    exact ih α hαω p hp hmem

/-- The terminal-stage formulation: every initial alignment can be brought
to the designated base by finitely many replacements. -/
theorem finite_descent_terminal
    (hn : ∀ i, n i ∈ S.stage 0)
    (hq : ∀ i j d, n i * d = n j → d ∈ S.stage 0)
    (hbound : ∀ p ∈ A, ∃ N, p.2 ∣ n N)
    (hreplace : ∀ p ∈ A, ∀ N, ∃ l' d,
      (l', p.2 * d) ∈ A ∧ p.1 ≤ l' ∧ n p.1 * d = n l' ∧ n N ∣ p.2 * d)
    (ω : Ordinal.{v}) (hterminal : S.stage ω = ⊤)
    (p : ℕ × T) (hp : p ∈ A) :
    ∃ q ∈ A, q.2 ∈ S.stage 0 ∧ Relation.ReflTransGen (Replaces n A) p q := by
  apply S.finite_descent n A hn hq hbound hreplace ω p hp
  rw [hterminal]
  trivial

end GateTower
end PartitionConsistency.DiagramOrder

end OAI
