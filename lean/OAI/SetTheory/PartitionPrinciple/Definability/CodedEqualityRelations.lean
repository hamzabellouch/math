import OAI.SetTheory.PartitionPrinciple.Geometry.GroundEqualityStep

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

def tripleMembershipFormula {n : Nat} (p x y r : Fin n) : SetFormula n :=
  ex (.conj (orderedPairFormula 0 x.succ y.succ)
    (pairMembershipFormula p.succ 0 r.succ))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} (s : Presentation P)

def codedEqualityRelation (S : ZFSet.{u}) (p : P) (σ τ : Name s) : Prop :=
  ZFSet.pair (s.encode p) (ZFSet.pair σ.val τ.val) ∈ S

theorem codedEqualityRelation_mono {S T : ZFSet.{u}} (h : S ⊆ T) (p : P) (σ τ : Name s) :
    codedEqualityRelation s S p σ τ → codedEqualityRelation s T p σ τ :=
  fun member => h member

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_tripleMembershipFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (p x y r : Fin n) (env : Fin n → ZFSet.{u})
    (hp : env p ∈ M.sets) (hx : env x ∈ M.sets)
    (hy : env y ∈ M.sets) (hr : env r ∈ M.sets) :
    Realize M.sets (tripleMembershipFormula p x y r) env ↔
      ZFSet.pair (env p) (ZFSet.pair (env x) (env y)) ∈ env r := by
  rw [tripleMembershipFormula, realize_ex]
  constructor
  · rintro ⟨z, hz, shape, member⟩
    have eq := (M.realize_orderedPairFormula pairing 0 x.succ y.succ
      (extend z env) hz hx hy).1 shape
    have raw := (M.realize_pairMembershipFormula pairing p.succ 0 r.succ
      (extend z env) hp hz hr).1 member
    change z = ZFSet.pair (env x) (env y) at eq
    change ZFSet.pair (env p) z ∈ env r at raw
    exact eq ▸ raw
  · intro member
    have hz := M.orderedPair_mem pairing hx hy
    refine ⟨ZFSet.pair (env x) (env y), hz, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing 0 x.succ y.succ
        (extend (ZFSet.pair (env x) (env y)) env) hz hx hy).2 rfl
    · exact (M.realize_pairMembershipFormula pairing p.succ 0 r.succ
        (extend (ZFSet.pair (env x) (env y)) env) hp hz hr).2 member

variable {P : Type u} (s : Presentation P)

theorem relationMeaning_coded (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets)
    {k : Nat} (r : Fin k) (constants : Fin k → ZFSet.{u})
    (hr : constants r ∈ M.sets) :
    M.RelationMeaning s D (Name.codedEqualityRelation s (constants r))
      (tripleMembershipFormula 0 1 2 r.succ.succ.succ) constants := by
  intro p σ τ
  exact M.realize_tripleMembershipFormula pairing 0 1 2 r.succ.succ.succ _
    (M.transitive carrier (s.encode_mem p)) (ground σ.val σ.property)
    (ground τ.val τ.property) hr

theorem coded_postfixed_sound [Preorder P] (D : Name.NameDomain s) (S : ZFSet.{u})
    (post : ∀ σ ∈ D.names, ∀ τ ∈ D.names, ∀ p,
      Name.codedEqualityRelation s S p σ τ →
        Name.EqualityStep (Name.codedEqualityRelation s S) p σ τ)
    {σ τ : Name s} (hσ : σ ∈ D.names) (hτ : τ ∈ D.names) (p : P) :
    Name.codedEqualityRelation s S p σ τ → Name.ForcesEq p σ τ :=
  Name.postfixed_equality_sound D (Name.codedEqualityRelation s S) post σ hσ τ hτ p

theorem coded_fixed_iff [Preorder P] (D : Name.NameDomain s) (S : ZFSet.{u})
    (fixed : ∀ σ ∈ D.names, ∀ τ ∈ D.names, ∀ p,
      Name.codedEqualityRelation s S p σ τ ↔
        Name.EqualityStep (Name.codedEqualityRelation s S) p σ τ)
    {σ τ : Name s} (hσ : σ ∈ D.names) (hτ : τ ∈ D.names) (p : P) :
    Name.codedEqualityRelation s S p σ τ ↔ Name.ForcesEq p σ τ :=
  Name.fixed_equality_iff D (Name.codedEqualityRelation s S) fixed hσ hτ p

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
