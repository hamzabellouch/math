import OAI.SetTheory.PartitionPrinciple.Forcing.OrbitPairGraphNames

namespace OAI

section

namespace PartitionPilot.SetRealization

universe u

def SetMembers (Q : ZFSet.{u}) : Type u := Shrink Q

namespace SetMembers

noncomputable def raw {Q : ZFSet.{u}} (x : SetMembers Q) : ZFSet.{u} :=
  ((equivShrink.{u} Q).symm x).val

theorem raw_mem {Q : ZFSet.{u}} (x : SetMembers Q) : raw x ∈ Q :=
  ((equivShrink.{u} Q).symm x).property

theorem raw_injective (Q : ZFSet.{u}) : Function.Injective (@raw Q) := by
  intro x y eq
  apply (equivShrink.{u} Q).symm.injective
  exact Subtype.ext eq

noncomputable def ofMem {Q : ZFSet.{u}} (x : ZFSet.{u}) (hx : x ∈ Q) : SetMembers Q :=
  equivShrink.{u} Q ⟨x, hx⟩

theorem raw_ofMem {Q : ZFSet.{u}} (x : ZFSet.{u}) (hx : x ∈ Q) : raw (ofMem x hx) = x := by
  exact congrArg Subtype.val ((equivShrink.{u} Q).symm_apply_apply ⟨x, hx⟩)

theorem ofMem_raw {Q : ZFSet.{u}} (x : SetMembers Q) : ofMem (raw x) (raw_mem x) = x :=
  (equivShrink.{u} Q).apply_symm_apply x

noncomputable def presentation (Q : ZFSet.{u}) : Presentation (SetMembers Q) where
  carrier := Q
  encode := raw
  injective := raw_injective Q
  mem_carrier x := ⟨fun hx => ⟨ofMem x hx, raw_ofMem x hx⟩,
    fun ⟨a, eq⟩ => eq ▸ raw_mem a⟩

end SetMembers

end PartitionPilot.SetRealization

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem setMember_ground {Q : ZFSet.{u}} (hQ : Q ∈ M.sets) (x : SetMembers Q) :
    SetMembers.raw x ∈ M.sets := M.transitive hQ (SetMembers.raw_mem x)

theorem setMembers_countable (small : M.sets.Countable) {Q : ZFSet.{u}} (hQ : Q ∈ M.sets) :
    Countable (SetMembers Q) := M.conditions_countable (SetMembers.presentation Q) small hQ

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

universe u

def natSetCode (n : Nat) : ZFSet.{u} := ZFSet.mk (PSet.ofNat n)

theorem natSetCode_zero : natSetCode 0 = (∅ : ZFSet.{u}) := rfl

theorem natSetCode_succ (n : Nat) :
    natSetCode (n + 1) = insert (natSetCode n) (natSetCode n) := rfl

theorem mem_omega_iff_natSetCode (x : ZFSet.{u}) :
    x ∈ ZFSet.omega ↔ ∃ n, x = natSetCode n := by
  induction x using Quotient.inductionOn with
  | h x =>
    constructor
    · rintro ⟨⟨n⟩, h⟩
      exact ⟨n, ZFSet.sound h⟩
    · rintro ⟨n, h⟩
      exact ⟨⟨n⟩, ZFSet.exact h⟩

theorem natSetCode_mem_omega (n : Nat) : natSetCode n ∈ ZFSet.omega.{u} :=
  (mem_omega_iff_natSetCode _).2 ⟨n, rfl⟩

def zeroOrSuccessor (x : ZFSet.{u}) : Prop :=
  x = ∅ ∨ ∃ y ∈ x, x = insert y y

def naturalSetProperty (x : ZFSet.{u}) : Prop :=
  setTransitive x ∧ zeroOrSuccessor x ∧
    ∀ y ∈ x, setTransitive y ∧ zeroOrSuccessor y

theorem naturalSetProperty_empty : naturalSetProperty (∅ : ZFSet.{u}) := by
  refine ⟨?_, Or.inl rfl, ?_⟩
  · intro y hy
    exact False.elim (ZFSet.notMem_empty y hy)
  · intro y hy
    exact False.elim (ZFSet.notMem_empty y hy)

theorem naturalSetProperty_succ {x : ZFSet.{u}} (h : naturalSetProperty x) :
    naturalSetProperty (insert x x) := by
  refine ⟨?_, Or.inr ⟨x, ZFSet.mem_insert x x, rfl⟩, ?_⟩
  · intro y hy z hz
    rcases ZFSet.mem_insert_iff.1 hy with rfl | hy
    · exact ZFSet.mem_insert_of_mem _ hz
    · exact ZFSet.mem_insert_of_mem x (h.1 y hy z hz)
  · intro y hy
    rcases ZFSet.mem_insert_iff.1 hy with rfl | hy
    · exact ⟨h.1, h.2.1⟩
    · exact h.2.2 y hy

theorem naturalSetProperty_member {x y : ZFSet.{u}}
    (h : naturalSetProperty x) (hy : y ∈ x) : naturalSetProperty y := by
  have facts := h.2.2 y hy
  exact ⟨facts.1, facts.2, fun z hz => h.2.2 z (h.1 y hy z hz)⟩

theorem naturalSetProperty_iff (x : ZFSet.{u}) :
    naturalSetProperty x ↔ ∃ n, x = natSetCode n := by
  constructor
  · induction x using ZFSet.inductionOn with
    | h x ih =>
      intro hx
      rcases hx.2.1 with empty | ⟨y, hy, succ⟩
      · exact ⟨0, empty⟩
      · obtain ⟨n, eq⟩ := ih y hy (naturalSetProperty_member hx hy)
        exact ⟨n + 1, by rw [succ, eq]; rfl⟩
  · rintro ⟨n, rfl⟩
    induction n with
    | zero => exact naturalSetProperty_empty
    | succ n ih => exact naturalSetProperty_succ ih

theorem naturalSetProperty_iff_mem_omega (x : ZFSet.{u}) :
    naturalSetProperty x ↔ x ∈ ZFSet.omega :=
  (naturalSetProperty_iff x).trans (mem_omega_iff_natSetCode x).symm

instance omegaMembers_countable : Countable (SetRealization.SetMembers ZFSet.omega.{u}) := by
  let f (n : Nat) := SetRealization.SetMembers.ofMem (natSetCode n) (natSetCode_mem_omega n)
  have onto : Function.Surjective f := by
    intro x
    obtain ⟨n, eq⟩ := (mem_omega_iff_natSetCode _).1 (SetRealization.SetMembers.raw_mem x)
    refine ⟨n, SetRealization.SetMembers.raw_injective _ ?_⟩
    exact (SetRealization.SetMembers.raw_ofMem _ _).trans eq.symm
  exact onto.countable

end PartitionPilot.Forcing

end

end OAI
