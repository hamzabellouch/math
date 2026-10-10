import OAI.SetTheory.PartitionPrinciple.Definability.GroundRegularFormulas
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundBelowFamilies

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
open scoped ZFSet
universe u

noncomputable def belowWitnessRelation (R K W : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ A ∈ R, ∃ β ∈ K, ∃ f ∈ W,
    z = ZFSet.pair A (ZFSet.pair β f) ∧ InjectionCode A β f) (ZFSet.prod R (ZFSet.prod K W))

theorem pair_mem_belowWitnessRelation (R K W A β f : ZFSet.{u}) :
    ZFSet.pair A (ZFSet.pair β f) ∈ belowWitnessRelation R K W ↔
      A ∈ R ∧ β ∈ K ∧ f ∈ W ∧ InjectionCode A β f := by
  rw [belowWitnessRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, A', hA, β', hβ, f', hf, equal, code⟩
    obtain ⟨hAeq, inner⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨hβeq, hfeq⟩ := ZFSet.pair_inj.1 inner
    subst A'
    subst β'
    subst f'
    exact ⟨hA, hβ, hf, code⟩
  · rintro ⟨hA, hβ, hf, code⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hA, ZFSet.pair_mem_prod.2 ⟨hβ, hf⟩⟩,
      A, hA, β, hβ, f, hf, rfl, code⟩

theorem belowWitnessRelation_subset (R K W : ZFSet.{u}) :
    belowWitnessRelation R K W ⊆ ZFSet.prod R (ZFSet.prod K W) :=
  fun _ entry => (ZFSet.mem_sep.1 entry).1

namespace BoundedFormula

def belowWitnessEntryFormula {n} (z r k w : Fin n) : BoundedFormula n :=
  exMem r (exMem k.succ (exMem w.succ.succ
    (.conj (orderedRightTripleFormula z.succ.succ.succ 2 1 0) (injectionFormula 2 1 0))))

theorem truth_belowWitnessEntryFormula {n} (z r k w : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (belowWitnessEntryFormula z r k w) env ↔
      ∃ A ∈ env r, ∃ β ∈ env k, ∃ f ∈ env w,
        env z = ZFSet.pair A (ZFSet.pair β f) ∧ InjectionCode A β f := by
  simp only [belowWitnessEntryFormula, truth_exMem, Truth,
    truth_orderedRightTripleFormula, truth_injectionFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem belowWitnessRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {R K W : ZFSet.{u}} (hR : R ∈ M.sets) (hK : K ∈ M.sets) (hW : W ∈ M.sets) :
    belowWitnessRelation R K W ∈ M.sets := by
  let params := extend R (extend K (extend W Fin.elim0))
  have selected := M.bounded_separation_mem separation (BoundedFormula.belowWitnessEntryFormula 0 1 2 3)
    params (Fin.cases hR (Fin.cases hK (Fin.cases hW (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hR (M.prod_mem pairing unions powers separation hK hW))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.belowWitnessEntryFormula 0 1 2 3) (extend z params))
      (ZFSet.prod R (ZFSet.prod K W)) = belowWitnessRelation R K W := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, belowWitnessRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_belowWitnessEntryFormula 0 1 2 3 _)
  exact equal ▸ selected

noncomputable def groundBelowWitnesses (R B K : ZFSet.{u}) : ZFSet.{u} :=
  belowWitnessRelation R K (M.groundRelations B K)

theorem groundBelowWitnesses_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {R B K : ZFSet.{u}} (hR : R ∈ M.sets) (hB : B ∈ M.sets) (hK : K ∈ M.sets) :
    M.groundBelowWitnesses R B K ∈ M.sets :=
  M.belowWitnessRelation_mem pairing unions powers separation hR hK
    (M.groundRelations_mem pairing unions powers separation hB hK)

theorem groundBelow_iff_boundedWitness {A B K : ZFSet.{u}}
    (subset : A ⊆ B) (transitive : ∀ β ∈ K, β ⊆ K) :
    GroundBelow M A K ↔ ∃ β ∈ K, ∃ f ∈ M.groundRelations B K, InjectionCode A β f := by
  constructor
  · rintro ⟨β, hβ, f, hf, code⟩
    have bound : f ⊆ ZFSet.prod B K := by
      intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 hz)
      exact ZFSet.pair_mem_prod.2 ⟨subset hx, transitive β hβ hy⟩
    exact ⟨β, hβ, f, (M.mem_groundRelations B K f).2 ⟨hf, bound⟩, code⟩
  · rintro ⟨β, hβ, f, hf, code⟩
    exact ⟨β, hβ, f, ((M.mem_groundRelations B K f).1 hf).1, code⟩

theorem groundBelowWitnesses_total_iff {R B K : ZFSet.{u}}
    (subsets : ∀ A ∈ R, A ⊆ B) (transitive : ∀ β ∈ K, β ⊆ K) :
    (∀ A ∈ R, ∃ q ∈ ZFSet.prod K (M.groundRelations B K),
      ZFSet.pair A q ∈ M.groundBelowWitnesses R B K) ↔
        ∀ A ∈ R, GroundBelow M A K := by
  constructor
  · intro total A hA
    obtain ⟨q, hq, entry⟩ := total A hA
    obtain ⟨β, hβ, f, hf, rfl⟩ := ZFSet.mem_prod.1 hq
    have code := ((pair_mem_belowWitnessRelation R K (M.groundRelations B K) A β f).1 entry).2.2.2
    exact (M.groundBelow_iff_boundedWitness (subsets A hA) transitive).2 ⟨β, hβ, f, hf, code⟩
  · intro small A hA
    obtain ⟨β, hβ, f, hf, code⟩ :=
      (M.groundBelow_iff_boundedWitness (subsets A hA) transitive).1 (small A hA)
    exact ⟨ZFSet.pair β f, ZFSet.pair_mem_prod.2 ⟨hβ, hf⟩,
      (pair_mem_belowWitnessRelation R K (M.groundRelations B K) A β f).2 ⟨hA, hβ, hf, code⟩⟩

theorem uniform_below_witnesses
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R B K : ZFSet.{u}} (hR : R ∈ M.sets) (hB : B ∈ M.sets) (hK : K ∈ M.sets)
    (subsets : ∀ A ∈ R, A ⊆ B) (transitive : ∀ β ∈ K, β ⊆ K)
    (small : ∀ A ∈ R, GroundBelow M A K) :
    ∃ F ∈ M.sets, ZFSet.IsFunc R (ZFSet.prod K (M.groundRelations B K)) F ∧
      ∀ A q, ZFSet.pair A q ∈ F →
        ∃ β ∈ K, ∃ f ∈ M.sets, q = ZFSet.pair β f ∧ InjectionCode A β f := by
  have hW := M.groundRelations_mem pairing unions powers separation hB hK
  have relation := M.groundBelowWitnesses_mem pairing unions powers separation hR hB hK
  have total := (M.groundBelowWitnesses_total_iff subsets transitive).2 small
  obtain ⟨F, hF, function, selected⟩ := M.uniformize_relation pairing unions powers separation choice
    hR (M.prod_mem pairing unions powers separation hK hW) relation total
  refine ⟨F, hF, function, ?_⟩
  intro A q entry
  have hq := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  obtain ⟨β, hβ, f, hf, rfl⟩ := ZFSet.mem_prod.1 hq
  have code := ((pair_mem_belowWitnessRelation R K (M.groundRelations B K) A β f).1
    (selected entry)).2.2.2
  exact ⟨β, hβ, f, ((M.mem_groundRelations B K f).1 hf).1, rfl, code⟩

theorem uniform_below_family
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R K : ZFSet.{u}} (hR : R ∈ M.sets) (hK : K ∈ M.sets)
    (transitive : ∀ β ∈ K, β ⊆ K) (small : ∀ A ∈ R, GroundBelow M A K) :
    ∃ F ∈ M.sets, ZFSet.IsFunc R (ZFSet.prod K (M.groundRelations (⋃₀ R) K)) F ∧
      ∀ A q, ZFSet.pair A q ∈ F →
        ∃ β ∈ K, ∃ f ∈ M.sets, q = ZFSet.pair β f ∧ InjectionCode A β f :=
  M.uniform_below_witnesses pairing unions powers separation choice hR (M.union_mem unions hR) hK
    (fun A hA _ hx => ZFSet.mem_sUnion.2 ⟨A, hA, hx⟩) transitive small

end TransitiveGround

namespace GroundRegular
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}} (regular : GroundRegular M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include regular pairing unions powers separation

theorem bound_witnesses {R W F : ZFSet.{u}}
    (hR : R ∈ M.sets) (hK : K ∈ M.sets) (hW : W ∈ M.sets) (hF : F ∈ M.sets)
    (ordinal : ordinalSetProperty K) (small : GroundBelow M R K)
    (family : ZFSet.IsFunc R (ZFSet.prod K W) F)
    (witnesses : ∀ A β f, ZFSet.pair A (ZFSet.pair β f) ∈ F → InjectionCode A β f) :
    ∃ δ ∈ K, ∀ A β f, ZFSet.pair A (ZFSet.pair β f) ∈ F →
      β ∈ δ ∧ InjectionCode A β f ∧ InjectionCode A δ f := by
  obtain ⟨δ, hδ, bounded⟩ := regular.bound_paired pairing unions powers separation hR hK hW hF small family
  refine ⟨δ, hδ, ?_⟩
  intro A β f entry
  have hβ := bounded A β f entry
  have code := witnesses A β f entry
  refine ⟨hβ, code, ⟨⟨?_, code.function.2⟩, code.injective⟩⟩
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 hz)
  exact ZFSet.pair_mem_prod.2 ⟨hx, (ordinal.2 δ hδ) β hβ y hy⟩

end GroundRegular

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem uniform_below_common_bound
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R K : ZFSet.{u}} (hR : R ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K)
    (indices : GroundBelow M R K) (small : ∀ A ∈ R, GroundBelow M A K) :
    ∃ δ ∈ K, ∃ F ∈ M.sets,
      ZFSet.IsFunc R (ZFSet.prod K (M.groundRelations (⋃₀ R) K)) F ∧
      ∀ A β f, ZFSet.pair A (ZFSet.pair β f) ∈ F →
        f ∈ M.sets ∧ β ∈ δ ∧ InjectionCode A β f ∧ InjectionCode A δ f := by
  obtain ⟨F, hF, family, witnesses⟩ := M.uniform_below_family
    pairing unions powers separation choice hR hK ordinal.1 small
  have actual : ∀ A β f, ZFSet.pair A (ZFSet.pair β f) ∈ F →
      f ∈ M.sets ∧ InjectionCode A β f := by
    intro A β f entry
    obtain ⟨β', _, f', hf, equal, code⟩ := witnesses A (ZFSet.pair β f) entry
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hf, code⟩
  obtain ⟨δ, hδ, bounded⟩ := regular.bound_witnesses pairing unions powers separation hR hK
    (M.groundRelations_mem pairing unions powers separation (M.union_mem unions hR) hK) hF
    ordinal indices family (fun A β f entry => (actual A β f entry).2)
  exact ⟨δ, hδ, F, hF, family, fun A β f entry =>
    ⟨(actual A β f entry).1, bounded A β f entry⟩⟩

end TransitiveGround
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
open scoped ZFSet
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
include M pairing unions powers separation choice

theorem selected_union_embeds_product {R W D F : ZFSet.{u}}
    (hR : R ∈ M.sets) (hW : W ∈ M.sets) (hD : D ∈ M.sets) (hF : F ∈ M.sets)
    (family : ZFSet.IsFunc R W F)
    (codes : ∀ A f, ZFSet.pair A f ∈ F → InjectionCode A D f) :
    M.groundEmbeddable (⋃₀ R) (ZFSet.prod R D) :=
  M.groundEmbeddable_of_partial_surjection pairing unions powers separation choice
    (M.prod_mem pairing unions powers separation hR hD) (M.union_mem unions hR)
    (M.unionSizeRelation_mem pairing unions powers separation (M.union_mem unions hR) hR hW hD hF)
    (unionSizeRelation_partial family codes) (unionSizeRelation_onto family codes)

theorem paired_union_embeds_product {R K W D F : ZFSet.{u}}
    (hR : R ∈ M.sets) (hK : K ∈ M.sets) (hW : W ∈ M.sets)
    (hD : D ∈ M.sets) (hF : F ∈ M.sets)
    (family : ZFSet.IsFunc R (ZFSet.prod K W) F)
    (codes : ∀ A β f, ZFSet.pair A (ZFSet.pair β f) ∈ F → InjectionCode A D f) :
    M.groundEmbeddable (⋃₀ R) (ZFSet.prod R D) := by
  let H := relationCompose R (ZFSet.prod K W) W F (productSecond K W)
  have hH : H ∈ M.sets := M.relationCompose_mem pairing unions powers separation hR
    (M.prod_mem pairing unions powers separation hK hW) hW hF
    (M.productSecond_mem pairing unions powers separation hK hW)
  have selected : ZFSet.IsFunc R W H :=
    relationCompose_function_of_subset family (productSecond_function K W) (fun _ h => h)
  have actual : ∀ A f, ZFSet.pair A f ∈ H → InjectionCode A D f := by
    intro A f entry
    obtain ⟨_, _, q, _, aq, projection⟩ := (pair_mem_relationCompose _ _ _ _ _ A f).1 entry
    obtain ⟨β, _, g, _, equal⟩ := (mem_productSecond K W (ZFSet.pair q f)).1 projection
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact codes A β f aq
  exact M.selected_union_embeds_product pairing unions powers separation choice hR hW hD hH selected actual

theorem regular_union_embeds_product {R K : ZFSet.{u}}
    (hR : R ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K)
    (indices : GroundBelow M R K) (small : ∀ A ∈ R, GroundBelow M A K) :
    ∃ D ∈ K, M.groundEmbeddable (⋃₀ R) (ZFSet.prod R D) := by
  obtain ⟨D, hD, F, hF, family, witnesses⟩ := M.uniform_below_common_bound
    pairing unions powers separation choice hR hK ordinal regular indices small
  exact ⟨D, hD, M.paired_union_embeds_product pairing unions powers separation choice hR hK
    (M.groundRelations_mem pairing unions powers separation (M.union_mem unions hR) hK)
    (M.transitive hK hD) hF family (fun A β f entry => (witnesses A β f entry).2.2.2)⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
