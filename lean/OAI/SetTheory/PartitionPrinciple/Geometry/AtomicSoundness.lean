import OAI.SetTheory.PartitionPrinciple.Forcing.EvaluatedDomains

namespace OAI

section

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

theorem forcesEq_sound (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D)) :
    ∀ σ ∈ D.names, ∀ τ ∈ D.names, ∀ p, H.mem p → ForcesEq p σ τ →
      eval {q | H.mem q} σ = eval {q | H.mem q} τ := by
  intro σ
  induction σ using inductionOn with
  | step σ ih =>
    intro hσ τ hτ p hp eq
    apply ZFSet.ext
    intro value
    constructor
    · intro hv
      obtain ⟨ρ, r, entry, hr, old⟩ := (mem_eval {q | H.mem q} σ value).1 hv
      obtain ⟨q, hq, qp, qr⟩ := H.directed hp hr
      have hρ := D.children hσ entry
      obtain ⟨t, ht, ν, k, target, tk, childEq⟩ := generic_mem_witness D H generic hρ hτ hq
        (forcesEq_left eq entry qp qr)
      have values := ih ρ r entry hρ ν (D.children hτ target) t ht childEq
      exact (mem_eval {q | H.mem q} τ value).2
        ⟨ν, k, target, H.upward ht tk, values.symm.trans old⟩
    · intro hv
      obtain ⟨ν, k, entry, hk, old⟩ := (mem_eval {q | H.mem q} τ value).1 hv
      obtain ⟨q, hq, qp, qk⟩ := H.directed hp hk
      have hν := D.children hτ entry
      obtain ⟨t, ht, ρ, r, target, tr, childEq⟩ := generic_mem_witness D H generic hν hσ hq
        (forcesEq_right eq entry qp qk)
      have values := ih ρ r target (D.children hσ target) ν hν t ht (forcesEq_symm childEq)
      exact (mem_eval {q | H.mem q} σ value).2
        ⟨ρ, r, target, H.upward ht tr, values.trans old⟩

theorem forcesMem_sound (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D)) {σ τ : Name s}
    (hσ : σ ∈ D.names) (hτ : τ ∈ D.names) {p : P} (hp : H.mem p)
    (h : ForcesMem p σ τ) : eval {q | H.mem q} σ ∈ eval {q | H.mem q} τ := by
  obtain ⟨q, hq, ν, r, entry, qr, eq⟩ := generic_mem_witness D H generic hσ hτ hp h
  have values := forcesEq_sound D H generic σ hσ ν (D.children hτ entry) q hq eq
  exact (mem_eval {q | H.mem q} τ _).2 ⟨ν, r, entry, H.upward hq qr, values.symm⟩

end PartitionPilot.Forcing.Name

end

end OAI
