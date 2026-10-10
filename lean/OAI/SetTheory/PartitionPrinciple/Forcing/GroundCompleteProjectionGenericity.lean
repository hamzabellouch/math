import OAI.SetTheory.PartitionPrinciple.Definability.CountableFormulaFamilies
import OAI.SetTheory.PartitionPrinciple.Geometry.CompleteProjectionPredensity
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundPresentedPreimages

namespace OAI


namespace PartitionPilot.Forcing

namespace TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

def codedFamily : Set (Set P) := (fun x : ZFSet.{u} => {p | s.encode p ∈ x}) '' M.sets

theorem codedFamily_countable (small : M.sets.Countable) : (M.codedFamily s).Countable :=
  small.image _

theorem codedFamily_of_code {E : Set P} (code : s.subset E ∈ M.sets) : E ∈ M.codedFamily s := by
  refine ⟨s.subset E, code, ?_⟩
  apply Set.ext
  intro p
  exact s.encode_mem_subset E p

theorem exists_ground_generic [Preorder P] (small : M.sets.Countable) (p : P) :
    ∃ H : ConditionFilter P, H.mem p ∧ H.GenericFor (M.codedFamily s) :=
  exists_generic_for_countable_family p _ (M.codedFamily_countable s small)

theorem generic_meets_coded_dense [Preorder P] (H : ConditionFilter P)
    (generic : H.GenericFor (M.codedFamily s)) {E : Set P}
    (code : s.subset E ∈ M.sets) (dense : Dense E) : H.Meets E :=
  generic E (M.codedFamily_of_code s code) dense

theorem symmetric_names_countable {G : Type v} [Group G] [PartialOrder P]
    (a : PosetAction G P) (F : NormalSubgroupFamily G) (small : M.sets.Countable) :
    (a.symmetricDomain s (M.nameDomain s) F).names.Countable :=
  (M.nameDomain_countable s small).mono (fun _ h => h.1)

theorem exists_joint_generic {G : Type v} [Group G] [PartialOrder P]
    (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (small : M.sets.Countable) (carrier : s.carrier ∈ M.sets) (p : P) :
    ∃ H : ConditionFilter P, H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
      H.GenericFor (formulaFamily (M.nameDomain s)) ∧
      H.GenericFor (formulaFamily (a.symmetricDomain s (M.nameDomain s) F)) := by
  let conditionsCountable : Countable P := M.conditions_countable s small carrier
  have ordinary := formulaFamily_countable (M.nameDomain s) (M.nameDomain_countable s small)
  have symmetric := formulaFamily_countable (a.symmetricDomain s (M.nameDomain s) F)
    (M.symmetric_names_countable s a F small)
  obtain ⟨H, hp, generic⟩ := exists_generic_for_countable_family p
    (M.codedFamily s ∪ (formulaFamily (M.nameDomain s) ∪
      formulaFamily (a.symmetricDomain s (M.nameDomain s) F)))
    ((M.codedFamily_countable s small).union (ordinary.union symmetric))
  exact ⟨H, hp, (fun E hE => generic E (Or.inl hE)),
    (fun E hE => generic E (Or.inr (Or.inl hE))),
    fun E hE => generic E (Or.inr (Or.inr hE))⟩

end TransitiveGround



namespace TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u v w
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P]
variable (s : Presentation P) {G : Type w} [Group G]

theorem exists_joint_projection_generic (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (small : M.sets.Countable) (carrier : s.carrier ∈ M.sets)
    {J : Type v} [Countable J] (Q : J → Type u) [∀ j, PartialOrder (Q j)]
    (t : ∀ j, Presentation (Q j)) (pi : ∀ j, P →o Q j) (inc : ∀ j, Q j ↪o P)
    (projection : ∀ j, CompleteProjection (pi j) (inc j)) (p : P) :
    ∃ H : ConditionFilter P, H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
      H.GenericFor (formulaFamily (M.nameDomain s)) ∧
      H.GenericFor (formulaFamily (a.symmetricDomain s (M.nameDomain s) F)) ∧
      ∀ j, ((projection j).projectedFilter H).GenericFor (M.codedFamily (t j)) ∧
        ((projection j).projectedFilter H).GenericFor (formulaFamily (M.nameDomain (t j))) := by
  let conditionsCountable : Countable P := M.conditions_countable s small carrier
  let projectedConditionsCountable (index : J) : Countable (Q index) :=
    (inc index).injective.countable
  let lower (j : J) : Set (Set (Q j)) :=
    M.codedFamily (t j) ∪ formulaFamily (M.nameDomain (t j))
  let lifted (j : J) : Set (Set P) :=
    (fun E : Set (Q j) => {q : P | pi j q ∈ E}) '' lower j
  have lowerCountable (j : J) : (lower j).Countable :=
    (M.codedFamily_countable (t j) small).union
      (formulaFamily_countable (M.nameDomain (t j)) (M.nameDomain_countable (t j) small))
  have liftedCountable : (⋃ j, lifted j).Countable :=
    Set.countable_iUnion (fun j => (lowerCountable j).image _)
  have ordinary := formulaFamily_countable (M.nameDomain s) (M.nameDomain_countable s small)
  have symmetric := formulaFamily_countable (a.symmetricDomain s (M.nameDomain s) F)
    (M.symmetric_names_countable s a F small)
  obtain ⟨H, hp, generic⟩ := exists_generic_for_countable_family p
    (M.codedFamily s ∪ (formulaFamily (M.nameDomain s) ∪
      (formulaFamily (a.symmetricDomain s (M.nameDomain s) F) ∪ ⋃ j, lifted j)))
    ((M.codedFamily_countable s small).union (ordinary.union (symmetric.union liftedCountable)))
  refine ⟨H, hp, (fun E hE => generic E (Or.inl hE)),
    (fun E hE => generic E (Or.inr (Or.inl hE))),
    (fun E hE => generic E (Or.inr (Or.inr (Or.inl hE)))), ?_⟩
  intro j
  have projected : ((projection j).projectedFilter H).GenericFor (lower j) :=
    (projection j).projectedFilter_generic H (lower j) (by
      intro E hE
      exact generic E (Or.inr (Or.inr (Or.inr (Set.mem_iUnion.2 ⟨j, hE⟩)))))
  exact ⟨(fun E hE => projected E (Or.inl hE)), fun E hE => projected E (Or.inr hE)⟩

end TransitiveGround



section
open SetRealization
universe u

namespace SetFormula
variable {P : Type u} [Preorder P] [Countable P] {s : Presentation P}

theorem forces_iff_all_generics (D : Name.NameDomain s) (small : D.names.Countable)
    {n : Nat} (phi : SetFormula n) (env : Assignment D n) (p : P) :
    Forces D phi env p ↔
      ∀ H : ConditionFilter P, H.mem p → H.GenericFor (formulaFamily D) →
        Realize (D.values {q | H.mem q}) phi (evalAssignment {q | H.mem q} env) := by
  constructor
  · intro forced H member generic
    exact forces_sound D H generic phi env member forced
  · intro truth
    by_contra bad
    obtain ⟨q, below, negative⟩ := not_forces_refine_neg D phi env bad
    obtain ⟨H, member, generic⟩ := exists_generic_formulaFamily D small q
    have yes := truth H (H.upward member below) generic
    have no := forces_sound D H generic (.neg phi) env member negative
    exact no yes

end SetFormula

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem ordinaryForces_iff_all_generics (small : M.sets.Countable)
    (carrier : s.carrier ∈ M.sets) {n : Nat} (phi : SetFormula n)
    (env : Assignment (M.nameDomain s) n) (p : P) :
    Forces (M.nameDomain s) phi env p ↔
      ∀ H : ConditionFilter P, H.mem p → H.GenericFor (formulaFamily (M.nameDomain s)) →
        Realize ((M.nameDomain s).values {q | H.mem q}) phi
          (evalAssignment {q | H.mem q} env) := by
  let conditionsCountable : Countable P := M.conditions_countable s small carrier
  exact forces_iff_all_generics (M.nameDomain s) (M.nameDomain_countable s small) phi env p

end TransitiveGround
end



namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem exists_coded_ordinary_generic (small : M.sets.Countable)
    (carrier : s.carrier ∈ M.sets) (p : P) :
    ∃ H : ConditionFilter P, H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
      H.GenericFor (formulaFamily (M.nameDomain s)) := by
  let conditionsCountable : Countable P := M.conditions_countable s small carrier
  have ordinary := formulaFamily_countable (M.nameDomain s) (M.nameDomain_countable s small)
  obtain ⟨H, member, generic⟩ := exists_generic_for_countable_family p
    (M.codedFamily s ∪ formulaFamily (M.nameDomain s))
    ((M.codedFamily_countable s small).union ordinary)
  exact ⟨H, member, (fun E hE => generic E (Or.inl hE)),
    fun E hE => generic E (Or.inr hE)⟩

theorem ordinaryForces_iff_all_joint_generics (small : M.sets.Countable)
    (carrier : s.carrier ∈ M.sets) {n : Nat} (phi : SetFormula n)
    (env : Assignment (M.nameDomain s) n) (p : P) :
    Forces (M.nameDomain s) phi env p ↔
      ∀ H : ConditionFilter P, H.mem p → H.GenericFor (M.codedFamily s) →
        H.GenericFor (formulaFamily (M.nameDomain s)) →
        Realize ((M.nameDomain s).values {q | H.mem q}) phi
          (evalAssignment {q | H.mem q} env) := by
  constructor
  · intro forced H member _ generic
    exact forces_sound (M.nameDomain s) H generic phi env member forced
  · intro truth
    by_contra bad
    obtain ⟨q, below, negative⟩ := not_forces_refine_neg (M.nameDomain s) phi env bad
    obtain ⟨H, member, coded, ordinary⟩ := M.exists_coded_ordinary_generic s small carrier q
    exact (forces_sound (M.nameDomain s) H ordinary (.neg phi) env member negative)
      (truth H (H.upward member below) coded ordinary)

end TransitiveGround



namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem ordinaryForces_congr_equalities (small : M.sets.Countable)
    (carrier : s.carrier ∈ M.sets) {n : Nat} (phi : SetFormula n)
    (env other : Assignment (M.nameDomain s) n) (p : P)
    (equal : ∀ j, Name.ForcesEq p (env j).val (other j).val) :
    Forces (M.nameDomain s) phi env p ↔ Forces (M.nameDomain s) phi other p := by
  have values (H : ConditionFilter P) (hp : H.mem p)
      (generic : H.GenericFor (formulaFamily (M.nameDomain s))) :
      evalAssignment {q | H.mem q} env = evalAssignment {q | H.mem q} other := by
    funext j
    exact Name.forcesEq_sound (M.nameDomain s) H
      (fun E hE dense => generic E (Or.inl hE) dense)
      (env j).val (env j).property (other j).val (other j).property p hp (equal j)
  rw [M.ordinaryForces_iff_all_generics s small carrier,
    M.ordinaryForces_iff_all_generics s small carrier]
  constructor
  · intro forced H hp generic
    rw [← values H hp generic]
    exact forced H hp generic
  · intro forced H hp generic
    rw [values H hp generic]
    exact forced H hp generic

theorem ordinaryForces_replace_first (small : M.sets.Countable)
    (carrier : s.carrier ∈ M.sets) {n : Nat} (phi : SetFormula (n + 1))
    (env : Assignment (M.nameDomain s) n) (sigma tau : (M.nameDomain s).names) (p : P)
    (equal : Name.ForcesEq p sigma.val tau.val) :
    Forces (M.nameDomain s) phi (extend sigma env) p ↔
      Forces (M.nameDomain s) phi (extend tau env) p :=
  M.ordinaryForces_congr_equalities s small carrier phi (extend sigma env) (extend tau env) p
    (Fin.cases equal (fun j => Name.forcesEq_refl (env j).val p))

end TransitiveGround



namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem ordinary_generic_meets_coded_dense (H : ConditionFilter P)
    (ordinary : H.GenericFor (formulaFamily (M.nameDomain s))) {E : Set P}
    (code : s.subset E ∈ M.sets) (dense : Dense E) : H.Meets E := by
  have emptyGround : (∅ : ZFSet.{u}) ∈ M.sets := M.empty_mem ⟨s.subset E, code⟩
  let witness : Name s := ⟨ZFSet.prod {∅} (s.subset E), IsName.mk
    (by
      intro z hz
      obtain ⟨x, hx, y, hy, shape⟩ := ZFSet.mem_prod.1 hz
      obtain ⟨p, _hp, rfl⟩ := (s.mem_subset E y).1 hy
      have empty : x = ∅ := ZFSet.mem_singleton.1 hx
      exact ⟨∅, p, shape.trans (congrArg (fun v => ZFSet.pair v (s.encode p)) empty)⟩)
    (by
      intro y p member
      have empty : y = ∅ := ZFSet.mem_singleton.1 (ZFSet.pair_mem_prod.1 member).1
      exact empty.symm ▸ (Name.empty s).property)⟩
  have witnessGround : witness.val ∈ M.sets := M.prod_mem pairing unions powers separation
    (by simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing emptyGround emptyGround) code
  have entries (sigma : Name s) (p : P) :
      Name.Entry sigma witness p ↔ sigma = Name.empty s ∧ p ∈ E := by
    constructor
    · intro entry
      have components : sigma.val ∈ {∅} ∧ s.encode p ∈ s.subset E :=
        ZFSet.pair_mem_prod.1 entry
      exact ⟨Subtype.ext (ZFSet.mem_singleton.1 components.1),
        (s.encode_mem_subset E p).1 components.2⟩
    · rintro ⟨rfl, member⟩
      exact ZFSet.pair_mem_prod.2
        ⟨ZFSet.mem_singleton.2 rfl, (s.encode_mem_subset E p).2 member⟩
  have forced (p : P) : Name.ForcesMem p (Name.empty s) witness := by
    apply Name.forcesMem_of_dense
    intro q _qp
    obtain ⟨r, rq, member⟩ := dense q
    exact ⟨r, rq, Name.forcesMem_entry ((entries (Name.empty s) r).2 ⟨rfl, member⟩)⟩
  obtain ⟨p, hp⟩ := H.nonempty
  have member := Name.forcesMem_sound (M.nameDomain s) H
    (fun E hE => ordinary E (Or.inl hE)) emptyGround witnessGround hp (forced p)
  obtain ⟨sigma, q, entry, hq, _equal⟩ := (Name.mem_eval {r | H.mem r} witness _).1 member
  exact ⟨q, hq, ((entries sigma q).1 entry).2⟩

theorem ordinary_generic_meets_ground_dense (H : ConditionFilter P)
    (ordinary : H.GenericFor (formulaFamily (M.nameDomain s))) {D : ZFSet.{u}}
    (ground : D ∈ M.sets) (subset : D ⊆ s.carrier)
    (dense : Dense {p | s.encode p ∈ D}) : H.Meets {p | s.encode p ∈ D} := by
  have codeEq : s.subset (fun p => s.encode p ∈ D) = D := by
    apply ZFSet.ext
    intro z
    rw [s.mem_subset]
    constructor
    · rintro ⟨p, member, rfl⟩
      exact member
    · intro member
      obtain ⟨p, same⟩ := (s.mem_carrier z).1 (subset member)
      exact ⟨p, same.symm ▸ member, same⟩
  exact M.ordinary_generic_meets_coded_dense s pairing unions powers separation H ordinary
    (codeEq.symm ▸ ground) dense

end TransitiveGround



namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {Upper Lower : Type u}
variable [PartialOrder Upper] [PartialOrder Lower]

theorem completeProjection_codedGeneric
    (upper : Presentation Upper) (lower : Presentation Lower)
    {restriction : Upper →o Lower} {inclusion : Lower ↪o Upper}
    (projection : CompleteProjection restriction inclusion)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (upperCarrier : upper.carrier ∈ M.sets) (lowerCarrier : lower.carrier ∈ M.sets)
    (graph : upper.graph lower restriction ∈ M.sets)
    (H : ConditionFilter Upper) (generic : H.GenericFor (M.codedFamily upper)) :
    (projection.projectedFilter H).GenericFor (M.codedFamily lower) := by
  intro E member dense
  obtain ⟨X, ground, rfl⟩ := member
  have preimage := M.presentedPreimage_mem upper lower restriction
    pairing unions powers separation upperCarrier lowerCarrier graph ground
  exact (projection.projectedFilter_meets_iff H _).2
    (M.generic_meets_coded_dense upper H generic preimage
      (projection.dense_preimage dense))

end TransitiveGround

end PartitionPilot.Forcing

end OAI
