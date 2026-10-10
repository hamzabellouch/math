import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCountableFunctionClosure

namespace OAI


namespace PartitionPilot.Forcing

universe u

theorem functionCode_partial {A B r : ZFSet.{u}} (func : ZFSet.IsFunc A B r) :
    PartialFunctionCode A B r := by
  refine ⟨func.1, ?_⟩
  intro x y z xy xz
  obtain ⟨v, _, unique⟩ := func.2 x (ZFSet.pair_mem_prod.1 (func.1 xy)).1
  exact (unique y xy).trans (unique z xz).symm

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem groundEmbeddable_function_image
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {A B D N r : ZFSet.{u}} (hD : D ∈ M.sets) (hB : B ∈ M.sets) (hN : N ∈ M.sets)
    (hr : r ∈ M.sets) (func : ZFSet.IsFunc A B r) (small : M.groundEmbeddable D N) :
    M.groundEmbeddable (relationImage D B r) N := by
  let rD := ZFSet.sep (fun z => z ∈ ZFSet.prod D B) r
  have hrD : rD ∈ M.sets := M.injection_restriction_mem separation hD hB hr
  have image := M.relationImage_mem separation hD hB hr
  have partialCode : PartialFunctionCode D (relationImage D B r) rD := by
    refine ⟨?_, fun x y z xy xz => (functionCode_partial func).unique x y z
      (ZFSet.mem_sep.1 xy).1 (ZFSet.mem_sep.1 xz).1⟩
    intro z hz
    obtain ⟨rel, bound⟩ := ZFSet.mem_sep.1 hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 bound
    exact ZFSet.pair_mem_prod.2 ⟨hx, (mem_relationImage D B r y).2 ⟨hy, x, hx, rel⟩⟩
  have onto : ∀ y ∈ relationImage D B r, ∃ x ∈ D, ZFSet.pair x y ∈ rD := by
    intro y hy
    obtain ⟨hyB, x, hx, rel⟩ := (mem_relationImage D B r y).1 hy
    exact ⟨x, hx, ZFSet.mem_sep.2 ⟨rel, ZFSet.pair_mem_prod.2 ⟨hx, hyB⟩⟩⟩
  obtain ⟨f, hf, code⟩ := M.groundEmbeddable_of_partial_surjection pairing unions powers separation choice
    hD image hrD partialCode onto
  obtain ⟨g, hg, gcode⟩ := small
  exact ⟨relationCompose (relationImage D B r) D N f g,
    M.relationCompose_mem pairing unions powers separation image hD hN hf hg, code.compose gcode⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundBelow
variable {M N : TransitiveGround.{u}} {A B K L : ZFSet.{u}}

theorem of_witness {β : ZFSet.{u}} (bound : β ∈ K)
    (small : M.groundEmbeddable A β) : GroundBelow M A K := ⟨β, bound, small⟩

theorem bound_mono (small : GroundBelow M A K) (subset : K ⊆ L) : GroundBelow M A L := by
  obtain ⟨β, hβ, witness⟩ := small
  exact ⟨β, subset hβ, witness⟩

theorem of_inclusion (small : GroundBelow M A K) (includes : M.sets ⊆ N.sets) :
    GroundBelow N A K := by
  obtain ⟨β, hβ, f, hf, code⟩ := small
  exact ⟨β, hβ, f, includes hf, code⟩

theorem empty_iff (hK : K ∈ M.sets) : GroundBelow M ∅ K ↔ K.Nonempty := by
  constructor
  · rintro ⟨β, hβ, _⟩
    exact ⟨β, hβ⟩
  · rintro ⟨β, hβ⟩
    exact ⟨β, hβ, M.empty_groundEmbeddable β ⟨K, hK⟩⟩

theorem restrict (small : GroundBelow M B K) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hK : K ∈ M.sets) (subset : A ⊆ B) : GroundBelow M A K := by
  obtain ⟨β, hβ, witness⟩ := small
  exact ⟨β, hβ, M.groundEmbeddable_restrict separation hA (M.transitive hK hβ) subset witness⟩

theorem of_embeddable (small : GroundBelow M B K)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hK : K ∈ M.sets)
    (embedding : M.groundEmbeddable A B) : GroundBelow M A K := by
  obtain ⟨β, hβ, g, hg, second⟩ := small
  obtain ⟨f, hf, first⟩ := embedding
  exact ⟨β, hβ, relationCompose A B β f g,
    M.relationCompose_mem pairing unions powers separation hA hB (M.transitive hK hβ) hf hg,
    first.compose second⟩

theorem function_image (small : GroundBelow M A K)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {D f : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hK : K ∈ M.sets)
    (hf : f ∈ M.sets) (function : ZFSet.IsFunc D B f) :
    GroundBelow M (relationImage A B f) K := by
  obtain ⟨β, hβ, witness⟩ := small
  exact ⟨β, hβ, M.groundEmbeddable_function_image pairing unions powers separation choice
    hA hB (M.transitive hK hβ) hf function witness⟩

end GroundBelow

namespace SetFormula

def groundBelowFormula {n} (a k : Fin n) : SetFormula n :=
  ex (.conj (.mem 0 k.succ) (hasInjectionFormula a.succ 0))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_groundBelowFormula {n} (a k : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (groundBelowFormula a k) env ↔ GroundBelow M (env a) (env k) := by
  rw [groundBelowFormula, realize_ex]
  constructor
  · rintro ⟨β, hβ, bound, witness⟩
    exact ⟨β, bound, (M.realize_hasInjectionFormula a.succ 0 (extend β env)
      (Fin.cases hβ members)).1 witness⟩
  · rintro ⟨β, bound, witness⟩
    have hβ := M.transitive (members k) bound
    exact ⟨β, hβ, bound, (M.realize_hasInjectionFormula a.succ 0 (extend β env)
      (Fin.cases hβ members)).2 witness⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

open scoped ZFSet

noncomputable def functionSourceProjection (A f : ZFSet.{u}) : ZFSet.{u} :=
  graphRestriction f (productFirst A (⋃₀ ⋃₀ f))

theorem pair_mem_functionSourceProjection (A f z x : ZFSet.{u}) :
    ZFSet.pair z x ∈ functionSourceProjection A f ↔
      z ∈ f ∧ x ∈ A ∧ ∃ y, z = ZFSet.pair x y := by
  rw [functionSourceProjection, pair_mem_graphRestriction, mem_productFirst]
  constructor
  · rintro ⟨⟨a, ha, b, _, equal⟩, hz⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hz, ha, b, rfl⟩
  · rintro ⟨hz, hx, y, rfl⟩
    exact ⟨⟨x, hx, y, pair_second_mem_doubleUnion hz, rfl⟩, hz⟩

theorem functionSourceProjection_injection {A f : ZFSet.{u}}
    (function : FunctionGraphOn A f) : InjectionCode f A (functionSourceProjection A f) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨z, hz, x, rfl, entry⟩ := mem_graphRestriction.1 hp
    have hx := (ZFSet.pair_mem_prod.1 ((productFirst_function A (⋃₀ ⋃₀ f)).1 entry)).2
    exact ZFSet.pair_mem_prod.2 ⟨hz, hx⟩
  · intro z hz
    obtain ⟨x, hx, y, rfl⟩ := function.shape z hz
    refine ⟨x, (pair_mem_functionSourceProjection _ _ _ _).2 ⟨hz, hx, y, rfl⟩, ?_⟩
    intro a entry
    obtain ⟨_, _, b, equal⟩ := (pair_mem_functionSourceProjection _ _ _ _).1 entry
    exact (ZFSet.pair_inj.1 equal).1.symm
  · intro z w x first second
    obtain ⟨hz, _, y, rfl⟩ := (pair_mem_functionSourceProjection _ _ _ _).1 first
    obtain ⟨hw, _, b, rfl⟩ := (pair_mem_functionSourceProjection _ _ _ _).1 second
    exact congrArg (ZFSet.pair x) (function.unique hz hw)

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem functionSourceProjection_mem {A f : ZFSet.{u}}
    (hA : A ∈ M.sets) (hf : f ∈ M.sets) : functionSourceProjection A f ∈ M.sets :=
  M.graphRestriction_mem unions separation hf (M.productFirst_mem pairing unions powers separation
    hA (M.union_mem unions (M.union_mem unions hf)))

theorem functionGraph_embeds_source {A f : ZFSet.{u}}
    (hA : A ∈ M.sets) (hf : f ∈ M.sets) (function : FunctionGraphOn A f) :
    M.groundEmbeddable f A :=
  ⟨functionSourceProjection A f, M.functionSourceProjection_mem pairing unions powers separation hA hf,
    functionSourceProjection_injection function⟩

end TransitiveGround

namespace GroundBelow
variable {M : TransitiveGround.{u}} {A B f K : ZFSet.{u}}

theorem functionGraphOn (small : GroundBelow M A K)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hf : f ∈ M.sets) (hK : K ∈ M.sets)
    (function : FunctionGraphOn A f) : GroundBelow M f K :=
  small.of_embeddable pairing unions powers separation hf hA hK
    (M.functionGraph_embeds_source pairing unions powers separation hA hf function)

theorem functionGraph (small : GroundBelow M A K)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hf : f ∈ M.sets) (hK : K ∈ M.sets)
    (function : ZFSet.IsFunc A B f) : GroundBelow M f K :=
  small.functionGraphOn pairing unions powers separation hA hf hK ⟨B, function⟩

end GroundBelow

end PartitionPilot.Forcing

end OAI
