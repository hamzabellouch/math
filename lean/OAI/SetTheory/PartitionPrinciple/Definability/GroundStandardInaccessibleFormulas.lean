import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStandardInaccessible

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula

def groundCardinalFormula {n} (k : Fin n) : SetFormula n :=
  .conj (BoundedFormula.ordinalFormula k).toFormula
    (.all (imp (.mem 0 k.succ) (.neg (hasInjectionFormula k.succ 0))))

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_groundCardinalFormula {n} (k : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (groundCardinalFormula k) env ↔ GroundCardinal M (env k) := by
  simp only [groundCardinalFormula, realize_imp, Realize]
  have ord := (BoundedFormula.realize_ordinalFormula M k env members).trans
    (ordinalSetProperty_iff (env k)).symm
  constructor
  · rintro ⟨ordinal, minimal⟩
    refine ⟨ord.1 ordinal, fun β hβ embedding => ?_⟩
    have hβM := M.transitive (members k) hβ
    exact minimal β hβM hβ
      ((M.realize_hasInjectionFormula k.succ 0 (extend β env)
        (Fin.cases hβM members)).2 embedding)
  · rintro ⟨ordinal, minimal⟩
    refine ⟨ord.2 ordinal, fun β hβM hβ witness => ?_⟩
    exact minimal β hβ ((M.realize_hasInjectionFormula k.succ 0 (extend β env)
      (Fin.cases hβM members)).1 witness)

end TransitiveGround

namespace BoundedFormula

def cofinalFunctionFormula {n} (a k f : Fin n) : BoundedFormula n :=
  .conj (functionFormula a k f)
    (.allMem k (exMem a.succ (exMem k.succ.succ
      (.conj (pairMembershipFormula 1 0 f.succ.succ.succ)
        (.disj (.equal 2 0) (.mem 2 0))))))

theorem truth_cofinalFunctionFormula {n} (a k f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (cofinalFunctionFormula a k f) env ↔
      CofinalFunctionCode (env a) (env k) (env f) := by
  simp only [cofinalFunctionFormula, Truth, truth_functionFormula, truth_exMem,
    truth_pairMembershipFormula, truth_disj]
  rfl

theorem realize_cofinalFunctionFormula (M : TransitiveGround.{u}) {n}
    (a k f : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (cofinalFunctionFormula a k f).toFormula env ↔
      CofinalFunctionCode (env a) (env k) (env f) :=
  (realize_toFormula M _ env members).trans (truth_cofinalFunctionFormula a k f env)

end BoundedFormula

namespace SetFormula

def groundCofinalRegularFormula {n} (k : Fin n) : SetFormula n :=
  .all (imp (.mem 0 k.succ)
    (.all (.neg (BoundedFormula.cofinalFunctionFormula 1 k.succ.succ 0).toFormula)))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_groundCofinalRegularFormula {n} (k : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (groundCofinalRegularFormula k) env ↔ GroundCofinalRegular M (env k) := by
  simp only [groundCofinalRegularFormula, realize_imp, Realize]
  constructor
  · intro property α hα f hf cofinal
    have hαM := M.transitive (members k) hα
    exact property α hαM hα f hf
      ((BoundedFormula.realize_cofinalFunctionFormula M 1 k.succ.succ 0
        (extend f (extend α env)) (Fin.cases hf (Fin.cases hαM members))).2 cofinal)
  · intro property α hαM hα f hf cofinal
    exact property α hα f hf
      ((BoundedFormula.realize_cofinalFunctionFormula M 1 k.succ.succ 0
        (extend f (extend α env)) (Fin.cases hf (Fin.cases hαM members))).1 cofinal)

theorem realize_groundCofinalRegularFormula_iff_regular {n} (k : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (ordinal : ordinalSetProperty (env k)) :
    Realize M.sets (groundCofinalRegularFormula k) env ↔ GroundRegular M (env k) :=
  (M.realize_groundCofinalRegularFormula k env members).trans
    (GroundCofinalRegular.iff_regular ordinal)

end TransitiveGround

namespace SetFormula

def groundCardinalStrongLimitFormula {n} (k : Fin n) : SetFormula n :=
  .all (imp (.mem 0 k.succ) (imp (groundCardinalFormula 0)
    (ex (.conj (relativePowerFormula 1 0) (groundBelowFormula 0 k.succ.succ)))))

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_groundCardinalStrongLimitFormula
    (powers : Realize M.sets powerSet Fin.elim0)
    {n} (k : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (groundCardinalStrongLimitFormula k) env ↔
      GroundCardinalStrongLimit M (env k) := by
  simp only [groundCardinalStrongLimitFormula, realize_imp, realize_ex, Realize]
  constructor
  · intro property κ hκ cardinal
    have hκM := M.transitive (members k) hκ
    have card := (M.realize_groundCardinalFormula 0 (extend κ env)
      (Fin.cases hκM members)).2 cardinal
    obtain ⟨p, hp, power, small⟩ := property κ hκM hκ card
    have equal := (M.realize_relativePowerFormula 1 0 (extend p (extend κ env))
      (Fin.cases hp (Fin.cases hκM members))).1 power
    have bound := (M.realize_groundBelowFormula 0 k.succ.succ (extend p (extend κ env))
      (Fin.cases hp (Fin.cases hκM members))).1 small
    exact equal ▸ bound
  · intro strong κ hκM hκ card
    have cardinal := (M.realize_groundCardinalFormula 0 (extend κ env)
      (Fin.cases hκM members)).1 card
    have hp := M.groundPower_mem powers hκM
    refine ⟨M.groundPower κ, hp, ?_, ?_⟩
    · exact (M.realize_relativePowerFormula 1 0 (extend (M.groundPower κ) (extend κ env))
        (Fin.cases hp (Fin.cases hκM members))).2 rfl
    · exact (M.realize_groundBelowFormula 0 k.succ.succ (extend (M.groundPower κ) (extend κ env))
        (Fin.cases hp (Fin.cases hκM members))).2 (strong κ hκ cardinal)

end TransitiveGround

namespace SetFormula

def groundStandardInaccessibleFormula {n} (k omega : Fin n) : SetFormula n :=
  .conj (groundCardinalFormula k)
    (.conj (.neg (hasInjectionFormula k omega))
      (.conj (groundCofinalRegularFormula k) (groundCardinalStrongLimitFormula k)))

def existsGroundStandardInaccessibleFormula {n} (omega : Fin n) : SetFormula n :=
  ex (groundStandardInaccessibleFormula 0 omega.succ)

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_groundStandardInaccessibleFormula
    (powers : Realize M.sets powerSet Fin.elim0)
    {n} (k omega : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (actualOmega : env omega = ZFSet.omega) :
    Realize M.sets (groundStandardInaccessibleFormula k omega) env ↔
      GroundStandardInaccessible M (env k) := by
  change (Realize M.sets (groundCardinalFormula k) env ∧
    (¬ Realize M.sets (hasInjectionFormula k omega) env) ∧
      Realize M.sets (groundCofinalRegularFormula k) env ∧
        Realize M.sets (groundCardinalStrongLimitFormula k) env) ↔
    (GroundCardinal M (env k) ∧ ¬ M.groundEmbeddable (env k) ZFSet.omega ∧
      GroundCofinalRegular M (env k) ∧ GroundCardinalStrongLimit M (env k))
  have injection := M.realize_hasInjectionFormula k omega env members
  rw [actualOmega] at injection
  exact and_congr (M.realize_groundCardinalFormula k env members)
    (and_congr (not_congr injection)
      (and_congr (M.realize_groundCofinalRegularFormula k env members)
        (M.realize_groundCardinalStrongLimitFormula powers k env members)))

theorem realize_existsGroundStandardInaccessibleFormula
    (powers : Realize M.sets powerSet Fin.elim0)
    {n} (omega : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (actualOmega : env omega = ZFSet.omega) :
    Realize M.sets (existsGroundStandardInaccessibleFormula omega) env ↔
      ∃ K ∈ M.sets, GroundStandardInaccessible M K := by
  rw [existsGroundStandardInaccessibleFormula, realize_ex]
  exact exists_congr (fun K => and_congr_right (fun hK =>
    M.realize_groundStandardInaccessibleFormula powers 0 omega.succ
      (extend K env) (Fin.cases hK members) actualOmega))

theorem realize_groundStandardInaccessibleFormula_iff_conditions
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {n} (k omega : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (actualOmega : env omega = ZFSet.omega) :
    Realize M.sets (groundStandardInaccessibleFormula k omega) env ↔
      GroundInaccessibleConditions M (env k) :=
  (M.realize_groundStandardInaccessibleFormula powers k omega env members actualOmega).trans
    (groundStandardInaccessible_iff_conditions M pairing unions powers separation (members k))

theorem realize_existsGroundStandardInaccessibleFormula_iff_conditions
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {n} (omega : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (actualOmega : env omega = ZFSet.omega) :
    Realize M.sets (existsGroundStandardInaccessibleFormula omega) env ↔
      ∃ K ∈ M.sets, GroundInaccessibleConditions M K :=
  (M.realize_existsGroundStandardInaccessibleFormula powers omega env members actualOmega).trans
    (exists_congr (fun K => and_congr_right (fun hK =>
      groundStandardInaccessible_iff_conditions M pairing unions powers separation (K := K) hK)))

end TransitiveGround
end PartitionPilot.Forcing

end OAI
