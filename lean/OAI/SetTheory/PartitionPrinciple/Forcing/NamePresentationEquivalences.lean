import OAI.SetTheory.PartitionPrinciple.Definability.NaturalSetCodes

namespace OAI

section

namespace PartitionPilot.SetRealization.Presentation
universe u
variable {P : Type u} (s : Presentation P)

noncomputable def intoSet (B : ZFSet.{u}) (sub : s.carrier ⊆ B) : P → SetMembers B :=
  fun p => SetMembers.ofMem (s.encode p) (sub (s.encode_mem p))

theorem encode_intoSet (B : ZFSet.{u}) (sub : s.carrier ⊆ B) (p : P) :
    (SetMembers.presentation B).encode (s.intoSet B sub p) = s.encode p :=
  SetMembers.raw_ofMem _ _

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P Q : Type u} {s : Presentation P}

theorem rename_val_of_encode (t : Presentation Q) (f : P → Q)
    (codes : ∀ p, t.encode (f p) = s.encode p) (τ : Name s) :
    (rename t f τ).val = τ.val := by
  induction τ using inductionOn with
  | step τ ih =>
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      obtain ⟨ρ, q, rfl⟩ := entries_cover (rename t f τ) hz
      obtain ⟨σ, p, entry, rfl, rfl⟩ := (entry_rename t f τ ρ q).1 hz
      rw [ih σ p entry, codes p]
      exact entry
    · intro hz
      obtain ⟨σ, p, rfl⟩ := entries_cover τ hz
      have entry := (entry_rename t f τ (rename t f σ) (f p)).2 ⟨σ, p, hz, rfl, rfl⟩
      change ZFSet.pair (rename t f σ).val (t.encode (f p)) ∈ (rename t f τ).val at entry
      simpa only [ih σ p hz, codes p] using entry

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P : Type u} (s t : Presentation P)

noncomputable def presentationEquiv : Name s ≃ Name t where
  toFun := rename t id
  invFun := rename s id
  left_inv τ := by rw [rename_comp]; exact rename_id τ
  right_inv τ := by rw [rename_comp]; exact rename_id τ

theorem eval_presentationEquiv (H : Set P) (τ : Name s) :
    eval H (presentationEquiv s t τ) = eval H τ :=
  eval_rename t id H τ

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.PosetAction
open SetRealization
universe u v
variable {P : Type u} {G : Type v} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s t : Presentation P)

theorem act_presentationEquiv (g : G) (τ : Name s) :
    a.act t g (Name.presentationEquiv s t τ) = Name.presentationEquiv s t (a.act s g τ) := by
  change Name.rename t (a.iso g) (Name.rename t id τ) =
    Name.rename t id (Name.rename s (a.iso g) τ)
  rw [Name.rename_comp, Name.rename_comp]
  rfl

theorem stabilizer_presentationEquiv (τ : Name s) :
    a.stabilizer t (Name.presentationEquiv s t τ) = a.stabilizer s τ := by
  apply Subgroup.ext
  intro g
  change a.act t g (Name.presentationEquiv s t τ) = Name.presentationEquiv s t τ ↔ a.act s g τ = τ
  rw [a.act_presentationEquiv]
  exact (Name.presentationEquiv s t).injective.eq_iff

end PartitionPilot.Forcing.PosetAction

namespace PartitionPilot.Forcing.HereditarilySymmetric
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} {G : Type v} [Group G] [PartialOrder P]
variable {a : PosetAction G P} {s : Presentation P} {F : NormalSubgroupFamily G}

theorem presentationEquiv (t : Presentation P) {τ : Name s}
    (hs : HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a t F (Name.presentationEquiv s t τ) := by
  induction τ using Name.inductionOn with
  | step τ ih =>
    refine .mk ?_ ?_
    · rw [a.stabilizer_presentationEquiv]
      exact hs.symmetric
    · intro ν p entry
      obtain ⟨σ, q, old, rfl, _⟩ := (Name.entry_rename t id τ ν p).1 entry
      exact ih σ q old (hs.member old)

theorem presentationEquiv_iff (t : Presentation P) (τ : Name s) :
    HereditarilySymmetric a t F (Name.presentationEquiv s t τ) ↔ HereditarilySymmetric a s F τ := by
  constructor
  · intro h
    have back := h.presentationEquiv s
    exact (Name.presentationEquiv s t).symm_apply_apply τ ▸ back
  · exact fun h => h.presentationEquiv t

end PartitionPilot.Forcing.HereditarilySymmetric

end

end OAI
