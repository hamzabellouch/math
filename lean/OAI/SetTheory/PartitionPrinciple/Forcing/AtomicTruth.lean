import OAI.SetTheory.PartitionPrinciple.Geometry.AtomicSoundness

namespace OAI

section

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

def EqTruth (H : ConditionFilter P) (σ τ : Name s) : Prop :=
  eval {q | H.mem q} σ = eval {q | H.mem q} τ → ∃ p, H.mem p ∧ ForcesEq p σ τ

def MemTruth (H : ConditionFilter P) (σ τ : Name s) : Prop :=
  eval {q | H.mem q} σ ∈ eval {q | H.mem q} τ → ∃ p, H.mem p ∧ ForcesMem p σ τ

theorem memTruth_of_children (H : ConditionFilter P) (σ τ : Name s)
    (children : ∀ ν r, Entry ν τ r → EqTruth H σ ν) : MemTruth H σ τ := by
  intro hv
  obtain ⟨ν, r, entry, hr, values⟩ := (mem_eval {q | H.mem q} τ _).1 hv
  obtain ⟨p, hp, eq⟩ := children ν r entry values.symm
  obtain ⟨q, hq, qp, qr⟩ := H.directed hp hr
  exact ⟨q, hq, forcesMem_of_witness ⟨ν, r, entry, qr, forcesEq_mono eq qp⟩⟩

theorem eqTruth_of_children (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D)) (σ τ : Name s)
    (hσ : σ ∈ D.names) (hτ : τ ∈ D.names)
    (left : ∀ ρ r, Entry ρ σ r → MemTruth H ρ τ)
    (right : ∀ ν k, Entry ν τ k → MemTruth H ν σ) : EqTruth H σ τ := by
  intro values
  obtain ⟨p, hp, eq | bad | bad⟩ := generic (EqDecisionWitness σ τ)
    (Or.inr ⟨σ, τ, hσ, hτ, rfl⟩) (eqDecisionWitness_dense σ τ)
  · exact ⟨p, hp, eq⟩
  · obtain ⟨ρ, r, entry, pr, neg⟩ := bad
    have member : eval {q | H.mem q} ρ ∈ eval {q | H.mem q} τ := by
      rw [← values]
      exact (mem_eval {q | H.mem q} σ _).2 ⟨ρ, r, entry, H.upward hp pr, rfl⟩
    obtain ⟨q, hq, mem⟩ := left ρ r entry member
    obtain ⟨t, _, tp, tq⟩ := H.directed hp hq
    exact False.elim (neg t tp (forcesMem_mono mem tq))
  · obtain ⟨ν, k, entry, pk, neg⟩ := bad
    have member : eval {q | H.mem q} ν ∈ eval {q | H.mem q} σ := by
      rw [values]
      exact (mem_eval {q | H.mem q} τ _).2 ⟨ν, k, entry, H.upward hp pk, rfl⟩
    obtain ⟨q, hq, mem⟩ := right ν k entry member
    obtain ⟨t, _, tp, tq⟩ := H.directed hp hq
    exact False.elim (neg t tp (forcesMem_mono mem tq))

theorem atomic_truth (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D)) :
    ∀ σ ∈ D.names, ∀ τ ∈ D.names, EqTruth H σ τ ∧ MemTruth H σ τ ∧ MemTruth H τ σ := by
  intro σ
  induction σ using inductionOn with
  | step σ outer =>
    intro hσ τ
    induction τ using inductionOn with
    | step τ inner =>
      intro hτ
      have eq : EqTruth H σ τ := eqTruth_of_children D H generic σ τ hσ hτ
        (fun ρ r entry => (outer ρ r entry (D.children hσ entry) τ hτ).2.1)
        (fun ν k entry => (inner ν k entry (D.children hτ entry)).2.2)
      have mem : MemTruth H σ τ := memTruth_of_children H σ τ
        (fun ν k entry => (inner ν k entry (D.children hτ entry)).1)
      have reverse : MemTruth H τ σ := memTruth_of_children H τ σ (by
        intro ρ r entry values
        obtain ⟨p, hp, eq⟩ := (outer ρ r entry (D.children hσ entry) τ hτ).1 values.symm
        exact ⟨p, hp, forcesEq_symm eq⟩)
      exact ⟨eq, mem, reverse⟩

theorem eval_eq_iff_forcesEq (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D)) {σ τ : Name s}
    (hσ : σ ∈ D.names) (hτ : τ ∈ D.names) :
    eval {q | H.mem q} σ = eval {q | H.mem q} τ ↔ ∃ p, H.mem p ∧ ForcesEq p σ τ := by
  constructor
  · exact (atomic_truth D H generic σ hσ τ hτ).1
  · rintro ⟨p, hp, eq⟩
    exact forcesEq_sound D H generic σ hσ τ hτ p hp eq

theorem eval_mem_iff_forcesMem (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D)) {σ τ : Name s}
    (hσ : σ ∈ D.names) (hτ : τ ∈ D.names) :
    eval {q | H.mem q} σ ∈ eval {q | H.mem q} τ ↔ ∃ p, H.mem p ∧ ForcesMem p σ τ := by
  constructor
  · exact (atomic_truth D H generic σ hσ τ hτ).2.1
  · rintro ⟨p, hp, mem⟩
    exact forcesMem_sound D H generic hσ hτ hp mem

end PartitionPilot.Forcing.Name

end

end OAI
