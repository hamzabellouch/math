import OAI.SetTheory.PartitionPrinciple.Forcing.EvaluatedDomains

namespace OAI

section

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

def EqualityStep (R : P → Name s → Name s → Prop) (p : P) (σ τ : Name s) : Prop :=
  (∀ ρ r, Entry ρ σ r → ∀ q, q ≤ p → q ≤ r →
    ∃ t, t ≤ q ∧ ∃ ν k, Entry ν τ k ∧ t ≤ k ∧ R t ρ ν) ∧
  (∀ ν k, Entry ν τ k → ∀ q, q ≤ p → q ≤ k →
    ∃ t, t ≤ q ∧ ∃ ρ r, Entry ρ σ r ∧ t ≤ r ∧ R t ρ ν)

def RelationMembership (R : P → Name s → Name s → Prop) (p : P) (σ τ : Name s) : Prop :=
  ∀ q, q ≤ p → ∃ t, t ≤ q ∧ ∃ ν r, Entry ν τ r ∧ t ≤ r ∧ R t σ ν

theorem equalityStep_mono {R S : P → Name s → Name s → Prop}
    (mono : ∀ p σ τ, R p σ τ → S p σ τ) {p : P} {σ τ : Name s}
    (h : EqualityStep R p σ τ) : EqualityStep S p σ τ := by
  constructor
  · intro ρ r hr q qp qr
    obtain ⟨t, tq, ν, k, hk, tk, rel⟩ := h.1 ρ r hr q qp qr
    exact ⟨t, tq, ν, k, hk, tk, mono t ρ ν rel⟩
  · intro ν k hk q qp qk
    obtain ⟨t, tq, ρ, r, hr, tr, rel⟩ := h.2 ν k hk q qp qk
    exact ⟨t, tq, ρ, r, hr, tr, mono t ρ ν rel⟩

theorem forcesEq_step (p : P) (σ τ : Name s) : ForcesEq p σ τ ↔ EqualityStep ForcesEq p σ τ := by
  rw [ForcesEq]
  simp only [EqualityStep, exists_prop]

theorem equalityStep_dense (R : P → Name s → Name s → Prop) (p : P) (σ τ : Name s) :
    EqualityStep R p σ τ ↔
      (∀ ρ r, Entry ρ σ r → ∀ q, q ≤ p → q ≤ r → RelationMembership R q ρ τ) ∧
      (∀ ν k, Entry ν τ k → ∀ q, q ≤ p → q ≤ k →
        RelationMembership (fun t ρ ν => R t ν ρ) q ν σ) := by
  constructor
  · intro h
    exact ⟨fun ρ r hr q qp qr t tq => h.1 ρ r hr t (tq.trans qp) (tq.trans qr),
      fun ν k hk q qp qk t tq => h.2 ν k hk t (tq.trans qp) (tq.trans qk)⟩
  · rintro ⟨left, right⟩
    exact ⟨fun ρ r hr q qp qr => left ρ r hr q qp qr q le_rfl,
      fun ν k hk q qp qk => right ν k hk q qp qk q le_rfl⟩

theorem postfixed_equality_sound (D : NameDomain s) (R : P → Name s → Name s → Prop)
    (post : ∀ σ ∈ D.names, ∀ τ ∈ D.names, ∀ p, R p σ τ → EqualityStep R p σ τ) :
    ∀ σ ∈ D.names, ∀ τ ∈ D.names, ∀ p, R p σ τ → ForcesEq p σ τ := by
  intro σ
  induction σ using inductionOn with
  | step σ ih =>
    intro hσ τ hτ p rel
    have h := post σ hσ τ hτ p rel
    rw [forcesEq_step]
    constructor
    · intro ρ r hr q qp qr
      obtain ⟨t, tq, ν, k, hk, tk, hrel⟩ := h.1 ρ r hr q qp qr
      exact ⟨t, tq, ν, k, hk, tk, ih ρ r hr (D.children hσ hr) ν (D.children hτ hk) t hrel⟩
    · intro ν k hk q qp qk
      obtain ⟨t, tq, ρ, r, hr, tr, hrel⟩ := h.2 ν k hk q qp qk
      exact ⟨t, tq, ρ, r, hr, tr, ih ρ r hr (D.children hσ hr) ν (D.children hτ hk) t hrel⟩

theorem prefixed_equality_complete (D : NameDomain s) (R : P → Name s → Name s → Prop)
    (pre : ∀ σ ∈ D.names, ∀ τ ∈ D.names, ∀ p, EqualityStep R p σ τ → R p σ τ) :
    ∀ σ ∈ D.names, ∀ τ ∈ D.names, ∀ p, ForcesEq p σ τ → R p σ τ := by
  intro σ
  induction σ using inductionOn with
  | step σ ih =>
    intro hσ τ hτ p forced
    have h := (forcesEq_step p σ τ).1 forced
    apply pre σ hσ τ hτ p
    constructor
    · intro ρ r hr q qp qr
      obtain ⟨t, tq, ν, k, hk, tk, hrel⟩ := h.1 ρ r hr q qp qr
      exact ⟨t, tq, ν, k, hk, tk, ih ρ r hr (D.children hσ hr) ν (D.children hτ hk) t hrel⟩
    · intro ν k hk q qp qk
      obtain ⟨t, tq, ρ, r, hr, tr, hrel⟩ := h.2 ν k hk q qp qk
      exact ⟨t, tq, ρ, r, hr, tr, ih ρ r hr (D.children hσ hr) ν (D.children hτ hk) t hrel⟩

theorem fixed_equality_iff (D : NameDomain s) (R : P → Name s → Name s → Prop)
    (fixed : ∀ σ ∈ D.names, ∀ τ ∈ D.names, ∀ p, R p σ τ ↔ EqualityStep R p σ τ)
    {σ τ : Name s} (hσ : σ ∈ D.names) (hτ : τ ∈ D.names) (p : P) :
    R p σ τ ↔ ForcesEq p σ τ :=
  ⟨postfixed_equality_sound D R (fun σ hσ τ hτ p => (fixed σ hσ τ hτ p).1) σ hσ τ hτ p,
    prefixed_equality_complete D R (fun σ hσ τ hτ p => (fixed σ hσ τ hτ p).2) σ hσ τ hτ p⟩

end PartitionPilot.Forcing.Name

end

end OAI
