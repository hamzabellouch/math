import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStrongLimitPowers

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula

def relativePowerFormula {n} (a p : Fin n) : SetFormula n :=
  .all (.conj
    (imp (.mem 0 p.succ) (BoundedFormula.subsetFormula 0 a.succ).toFormula)
    (imp (BoundedFormula.subsetFormula 0 a.succ).toFormula (.mem 0 p.succ)))

def groundStrongLimitFormula {n} (k : Fin n) : SetFormula n :=
  .all (imp (.mem 0 k.succ)
    (ex (.conj (relativePowerFormula 1 0) (groundBelowFormula 0 k.succ.succ))))

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_relativePowerFormula {n} (a p : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (relativePowerFormula a p) env ↔ env p = M.groundPower (env a) := by
  simp only [relativePowerFormula, realize_imp, Realize]
  have subset (x : ZFSet.{u}) (hx : x ∈ M.sets) :=
    (BoundedFormula.realize_toFormula M (BoundedFormula.subsetFormula 0 a.succ)
      (extend x env) (Fin.cases hx members)).trans
        (BoundedFormula.truth_subsetFormula 0 a.succ (extend x env))
  constructor
  · intro property
    apply ZFSet.ext
    intro x
    rw [M.mem_groundPower]
    constructor
    · intro hx
      have hxM := M.transitive (members p) hx
      exact ⟨hxM, (subset x hxM).1 ((property x hxM).1 hx)⟩
    · rintro ⟨hxM, included⟩
      exact (property x hxM).2 ((subset x hxM).2 included)
  · intro equal x hx
    constructor
    · intro entry
      change x ∈ env p at entry
      rw [equal, M.mem_groundPower] at entry
      exact (subset x hx).2 entry.2
    · intro included
      change x ∈ env p
      rw [equal, M.mem_groundPower]
      exact ⟨hx, (subset x hx).1 included⟩

theorem realize_groundStrongLimitFormula
    (powers : Realize M.sets powerSet Fin.elim0)
    {n} (k : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (groundStrongLimitFormula k) env ↔ GroundStrongLimit M (env k) := by
  simp only [groundStrongLimitFormula, realize_imp, realize_ex, Realize]
  constructor
  · intro property α hα
    have hαM := M.transitive (members k) hα
    obtain ⟨p, hp, power, small⟩ := property α hαM hα
    have equal := (M.realize_relativePowerFormula 1 0 (extend p (extend α env))
      (Fin.cases hp (Fin.cases hαM members))).1 power
    have bound := (M.realize_groundBelowFormula 0 k.succ.succ (extend p (extend α env))
      (Fin.cases hp (Fin.cases hαM members))).1 small
    exact equal ▸ bound
  · intro strong α hαM hα
    have hp := M.groundPower_mem powers hαM
    refine ⟨M.groundPower α, hp, ?_, ?_⟩
    · exact (M.realize_relativePowerFormula 1 0 (extend (M.groundPower α) (extend α env))
        (Fin.cases hp (Fin.cases hαM members))).2 rfl
    · exact (M.realize_groundBelowFormula 0 k.succ.succ (extend (M.groundPower α) (extend α env))
        (Fin.cases hp (Fin.cases hαM members))).2 (strong α hα)

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
