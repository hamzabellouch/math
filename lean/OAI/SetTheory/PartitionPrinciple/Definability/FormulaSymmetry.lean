import OAI.SetTheory.PartitionPrinciple.Forcing.OrbitPairGraphNames

namespace OAI

section

namespace PartitionPilot.Forcing.PosetAction

open SetRealization SetFormula
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

noncomputable def domainEquiv (D : Name.NameDomain s)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names) (g : G) : D.names ≃ D.names where
  toFun τ := ⟨a.act s g τ.val, closed g τ.val τ.property⟩
  invFun τ := ⟨a.act s g⁻¹ τ.val, closed g⁻¹ τ.val τ.property⟩
  left_inv τ := Subtype.ext (a.act_inv_left s g τ.val)
  right_inv τ := Subtype.ext (a.act_inv_right s g τ.val)

noncomputable def actAssignment (D : Name.NameDomain s)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names) (g : G)
    {n : Nat} (env : Assignment D n) : Assignment D n := fun i => a.domainEquiv s D closed g (env i)

theorem actAssignment_extend (D : Name.NameDomain s)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names) (g : G)
    {n : Nat} (τ : D.names) (env : Assignment D n) :
    a.actAssignment s D closed g (extend τ env) =
      extend (a.domainEquiv s D closed g τ) (a.actAssignment s D closed g env) :=
  map_extend (a.domainEquiv s D closed g) τ env

theorem formula_forces_act_iff (D : Name.NameDomain s)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names) (g : G)
    {n : Nat} (φ : SetFormula n) (env : Assignment D n) (p : P) :
    Forces D φ (a.actAssignment s D closed g env) (a.iso g p) ↔ Forces D φ env p := by
  induction φ generalizing p with
  | equal i j => exact a.forcesEq_act_iff s g p (env i).val (env j).val
  | mem i j => exact a.forcesMem_act_iff s g p (env i).val (env j).val
  | neg φ ih =>
    constructor
    · intro h q qp hφ
      exact h (a.iso g q) ((a.iso g).monotone qp) ((ih env q).2 hφ)
    · intro h q qp hφ
      have oldp : (a.iso g).symm q ≤ p := by simpa using (a.iso g).symm.monotone qp
      have oldφ := (ih env ((a.iso g).symm q)).1 (by simpa using hφ)
      exact h _ oldp oldφ
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ env p) (ihψ env p)
  | all φ ih =>
    constructor
    · intro h τ
      apply (ih (extend τ env) p).1
      rw [a.actAssignment_extend]
      exact h (a.domainEquiv s D closed g τ)
    · intro h ν
      obtain ⟨τ, rfl⟩ := (a.domainEquiv s D closed g).surjective ν
      have forced := (ih (extend τ env) p).2 (h τ)
      rw [a.actAssignment_extend] at forced
      exact forced

end PartitionPilot.Forcing.PosetAction

end

end OAI
