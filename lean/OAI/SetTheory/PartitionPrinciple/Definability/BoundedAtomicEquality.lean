import OAI.SetTheory.PartitionPrinciple.Forcing.GroundFixedPoints
import OAI.SetTheory.PartitionPrinciple.Geometry.RawEqualitySteps

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

def orderedTripleFormula {n : Nat} (z p x y : Fin n) : SetFormula n :=
  ex (.conj (orderedPairFormula 0 x.succ y.succ)
    (orderedPairFormula z.succ p.succ 0))

def codedRelationFormula : SetFormula 6 := tripleMembershipFormula 0 1 2 3

def equalityStateFormula : SetFormula 4 :=
  exConditions 2 <| ex <| ex <|
    .conj (orderedTripleFormula 3 2 1 0)
      (equalityStepFormula codedRelationFormula 1 2 (fun j => j.succ.succ.succ.succ) 2 1 0)

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_orderedTripleFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (z p x y : Fin n) (env : Fin n → ZFSet.{u})
    (hz : env z ∈ M.sets) (hp : env p ∈ M.sets)
    (hx : env x ∈ M.sets) (hy : env y ∈ M.sets) :
    Realize M.sets (orderedTripleFormula z p x y) env ↔
      env z = ZFSet.pair (env p) (ZFSet.pair (env x) (env y)) := by
  rw [orderedTripleFormula, realize_ex]
  constructor
  · rintro ⟨w, hw, inner, outer⟩
    have wi := (M.realize_orderedPairFormula pairing 0 x.succ y.succ
      (extend w env) hw hx hy).1 inner
    have zo := (M.realize_orderedPairFormula pairing z.succ p.succ 0
      (extend w env) hz hp hw).1 outer
    change w = ZFSet.pair (env x) (env y) at wi
    change env z = ZFSet.pair (env p) w at zo
    exact wi ▸ zo
  · intro eq
    have hw := M.orderedPair_mem pairing hx hy
    exact ⟨ZFSet.pair (env x) (env y), hw,
      (M.realize_orderedPairFormula pairing 0 x.succ y.succ
        (extend (ZFSet.pair (env x) (env y)) env) hw hx hy).2 rfl,
      (M.realize_orderedPairFormula pairing z.succ p.succ 0
        (extend (ZFSet.pair (env x) (env y)) env) hz hp hw).2 eq⟩

variable {P : Type u} [Preorder P] (s : Presentation P)

noncomputable def equalityParameters : Fin 2 → ZFSet.{u} :=
  extend s.carrier (extend s.conditionOrder Fin.elim0)

def RawCodedRelation (S : ZFSet.{u}) (p : P) (x y : ZFSet.{u}) : Prop :=
  ZFSet.pair (s.encode p) (ZFSet.pair x y) ∈ S

theorem rawRelationMeaning_coded
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (S : ZFSet.{u}) (hS : S ∈ M.sets) :
    M.RawRelationMeaning s (RawCodedRelation s S) codedRelationFormula
      (extend S (equalityParameters s)) := by
  intro p x hx y hy
  exact M.realize_tripleMembershipFormula pairing 0 1 2 3 _
    (M.transitive carrier (s.encode_mem p)) hx hy hS

theorem realize_equalityState
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (z S : ZFSet.{u}) (hz : z ∈ M.sets) (hS : S ∈ M.sets) :
    Realize M.sets equalityStateFormula (extend z (extend S (equalityParameters s))) ↔
      ∃ p x, x ∈ M.sets ∧ ∃ y, y ∈ M.sets ∧
        z = ZFSet.pair (s.encode p) (ZFSet.pair x y) ∧
        M.RawEqualityStep s (RawCodedRelation s S) p x y := by
  let env := extend z (extend S (equalityParameters s))
  rw [equalityStateFormula, M.realize_exConditions s 2 _ env carrier rfl]
  apply exists_congr
  intro p
  rw [realize_ex]
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  rw [realize_ex]
  apply exists_congr
  intro y
  apply and_congr_right
  intro hy
  let e := extend y (extend x (extend (s.encode p) env))
  change (Realize M.sets _ e ∧ Realize M.sets _ e) ↔ _
  rw [M.realize_orderedTripleFormula pairing 3 2 1 0 e hz
    (M.transitive carrier (s.encode_mem p)) hx hy,
    M.realize_rawEqualityStep s (RawCodedRelation s S) pairing carrier order
      codedRelationFormula 1 2 (fun j => j.succ.succ.succ.succ) 2 1 0 e rfl rfl
      (M.rawRelationMeaning_coded s pairing carrier S hS) p rfl hx hy]
  rfl

theorem equalityState_mono
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {z S T : ZFSet.{u}} (hz : z ∈ M.sets) (hS : S ∈ M.sets) (hT : T ∈ M.sets)
    (sub : S ⊆ T) :
    Realize M.sets equalityStateFormula (extend z (extend S (equalityParameters s))) →
      Realize M.sets equalityStateFormula (extend z (extend T (equalityParameters s))) := by
  rw [M.realize_equalityState s pairing carrier order z S hz hS,
    M.realize_equalityState s pairing carrier order z T hz hT]
  rintro ⟨p, x, hx, y, hy, shape, step⟩
  exact ⟨p, x, hx, y, hy, shape, M.rawEqualityStep_mono s (fun _ _ _ h => sub h) step⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem rawEqualityStep_names (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (S : ZFSet.{u}) (hS : S ∈ M.sets) (p : P) (σ τ : D.names) :
    M.RawEqualityStep s (RawCodedRelation s S) p σ.val.val τ.val.val ↔
      Name.EqualityStep (Name.codedEqualityRelation s S) p σ.val τ.val := by
  let constants := extend S (equalityParameters s)
  let env := extend (s.encode p) (extend σ.val.val (extend τ.val.val constants))
  have raw := M.realize_rawEqualityStep s (RawCodedRelation s S) pairing carrier order
    codedRelationFormula 1 2 (fun j => j.succ.succ.succ) 0 1 2 env rfl rfl
    (M.rawRelationMeaning_coded s pairing carrier S hS) p rfl
    (ground σ.val σ.property) (ground τ.val τ.property)
  have named := M.realize_equalityStep s D (Name.codedEqualityRelation s S)
    ground pairing carrier order codedRelationFormula 1 2 (fun j => j.succ.succ.succ)
    0 1 2 env rfl rfl (M.relationMeaning_coded s D ground pairing carrier 0 constants hS)
    p σ τ rfl rfl rfl
  exact raw.symm.trans named

theorem realize_equalityState_names (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (S : ZFSet.{u}) (hS : S ∈ M.sets) (p : P) (σ τ : D.names) :
    Realize M.sets equalityStateFormula
      (extend (ZFSet.pair (s.encode p) (ZFSet.pair σ.val.val τ.val.val))
        (extend S (equalityParameters s))) ↔
      Name.EqualityStep (Name.codedEqualityRelation s S) p σ.val τ.val := by
  have hz := M.orderedPair_mem pairing (M.transitive carrier (s.encode_mem p))
    (M.orderedPair_mem pairing (ground σ.val σ.property) (ground τ.val τ.property))
  rw [M.realize_equalityState s pairing carrier order _ S hz hS]
  constructor
  · rintro ⟨q, x, _, y, _, shape, step⟩
    obtain ⟨pq, xy⟩ := ZFSet.pair_inj.1 shape
    have peq := s.injective pq
    obtain ⟨sx, ty⟩ := ZFSet.pair_inj.1 xy
    subst q
    subst x
    subst y
    exact (M.rawEqualityStep_names s D ground pairing carrier order S hS p σ τ).1 step
  · intro step
    exact ⟨p, σ.val.val, ground σ.val σ.property, τ.val.val, ground τ.val τ.property, rfl,
      (M.rawEqualityStep_names s D ground pairing carrier order S hS p σ τ).2 step⟩

theorem exists_bounded_atomicEquality (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (B : ZFSet.{u}) (hB : B ∈ M.sets)
    (bound : ∀ p (σ τ : D.names), ZFSet.pair (s.encode p) (ZFSet.pair σ.val.val τ.val.val) ∈ B) :
    ∃ S ∈ M.sets, S ⊆ B ∧ ∀ p (σ τ : D.names),
      Name.codedEqualityRelation s S p σ.val τ.val ↔ Name.ForcesEq p σ.val τ.val := by
  have members : ∀ i, equalityParameters s i ∈ M.sets :=
    Fin.cases carrier (Fin.cases order (fun i => Fin.elim0 i))
  have mono : ∀ S ∈ M.sets, ∀ T ∈ M.sets, S ⊆ B → T ⊆ B → S ⊆ T →
      definableOperator M.sets equalityStateFormula (equalityParameters s) B S ⊆
        definableOperator M.sets equalityStateFormula (equalityParameters s) B T := by
    intro S hS T hT _ _ sub z hz
    obtain ⟨hzB, step⟩ := ZFSet.mem_sep.1 hz
    exact ZFSet.mem_sep.2 ⟨hzB,
      M.equalityState_mono s pairing carrier order (M.transitive hB hzB) hS hT sub step⟩
  obtain ⟨S, hS, hSB, fixed, _⟩ := M.exists_greatest_definable_fixedPoint unions powers separation
    equalityStateFormula (equalityParameters s) members hB mono
  have step : ∀ σ ∈ D.names, ∀ τ ∈ D.names, ∀ p,
      Name.codedEqualityRelation s S p σ τ ↔ Name.EqualityStep (Name.codedEqualityRelation s S) p σ τ := by
    intro σ hσ τ hτ p
    change ZFSet.pair (s.encode p) (ZFSet.pair σ.val τ.val) ∈ S ↔ _
    calc
      _ ↔ ZFSet.pair (s.encode p) (ZFSet.pair σ.val τ.val) ∈
          definableOperator M.sets equalityStateFormula (equalityParameters s) B S := by rw [fixed]
      _ ↔ _ := by
        rw [definableOperator, ZFSet.mem_sep,
          M.realize_equalityState_names s D ground pairing carrier order S hS p ⟨σ, hσ⟩ ⟨τ, hτ⟩]
        exact and_iff_right (bound p ⟨σ, hσ⟩ ⟨τ, hτ⟩)
  exact ⟨S, hS, hSB, fun p σ τ =>
    Name.fixed_equality_iff D (Name.codedEqualityRelation s S) step σ.property τ.property p⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
