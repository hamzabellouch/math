import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticRepresentedDomainEasyCases
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalStoredPreparedDensity
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalStructuralSeparationRefinements

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula

private def separationWitnessBody : BoundedFormula 12 :=
  .conj (.mem 1 6) (.conj (tripleMembershipFormula 1 3 0 10)
    (.conj (pairMembershipFormula 2 0 11)
      (.conj (pairMembershipFormula 1 4 7) (pairMembershipFormula 1 5 7))))

def separationWitnessFormula : BoundedFormula 10 :=
  exMem 7 (exMem 7 separationWitnessBody)

def localizedWitnessFormula : BoundedFormula 5 :=
  .disj (.mem 0 1) (.neg (exMem 2
    (.conj (pairMembershipFormula 0 1 4) (pairMembershipFormula 0 5 4))))

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem separationWitness_mem (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (action : a.actionGraph s t ∈ M.sets)
    (K : Subgroup G) (hK : t.subset (fun g => g ∈ K) ∈ M.sets)
    (Sep : G → G → Prop)
    (hSep : (t.product t).subset (fun gh => Sep gh.1 gh.2) ∈ M.sets)
    (p : P) (g₁ g₂ : G) : s.subset (a.SeparationWitness K Sep p g₁ g₂) ∈ M.sets := by
  let params := extend (s.encode p) (extend (t.encode g₁) (extend (t.encode g₂)
    (extend (t.subset (fun g => g ∈ K)) (extend ((t.product t).subset (fun gh => Sep gh.1 gh.2))
      (extend s.carrier (extend t.carrier (extend (a.actionGraph s t)
        (extend s.conditionOrder Fin.elim0))))))))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases (M.transitive carrier (s.encode_mem p))
      (Fin.cases (M.transitive group (t.encode_mem g₁))
        (Fin.cases (M.transitive group (t.encode_mem g₂))
          (Fin.cases hK (Fin.cases hSep (Fin.cases carrier
            (Fin.cases group (Fin.cases action (Fin.cases order (fun i => Fin.elim0 i)))))))))
  have selected := M.bounded_separation_mem separation BoundedFormula.separationWitnessFormula params members carrier
  have correct (q : P) : BoundedFormula.Truth BoundedFormula.separationWitnessFormula
      (extend (s.encode q) params) ↔ q ∈ a.SeparationWitness K Sep p g₁ g₂ := by
    simp only [BoundedFormula.separationWitnessFormula, BoundedFormula.separationWitnessBody,
      BoundedFormula.truth_exMem, BoundedFormula.Truth,
      BoundedFormula.truth_tripleMembershipFormula, BoundedFormula.truth_pairMembershipFormula]
    change (∃ h ∈ t.carrier, ∃ p' ∈ s.carrier,
      h ∈ t.subset (fun g => g ∈ K) ∧ ZFSet.pair (ZFSet.pair h (s.encode p)) p' ∈ a.actionGraph s t ∧
      ZFSet.pair (s.encode q) p' ∈ s.conditionOrder ∧
      ZFSet.pair h (t.encode g₁) ∈ (t.product t).subset (fun gh => Sep gh.1 gh.2) ∧
      ZFSet.pair h (t.encode g₂) ∈ (t.product t).subset (fun gh => Sep gh.1 gh.2)) ↔ _
    have sep (g h : G) : ZFSet.pair (t.encode g) (t.encode h) ∈
        (t.product t).subset (fun gh => Sep gh.1 gh.2) ↔ Sep g h :=
      (t.product t).encode_mem_subset _ (g,h)
    constructor
    · rintro ⟨h,hh,p',hp',fixed,acted,lower,first,second⟩
      obtain ⟨h,rfl⟩ := (t.mem_carrier h).1 hh
      obtain ⟨p',rfl⟩ := (s.mem_carrier p').1 hp'
      rw [a.triple_mem_actionGraph] at acted
      exact ⟨h,(t.encode_mem_subset _ h).1 fixed,
        acted ▸ (s.pair_mem_conditionOrder _ _).1 lower,(sep h g₁).1 first,(sep h g₂).1 second⟩
    · rintro ⟨h,fixed,lower,first,second⟩
      exact ⟨t.encode h,t.encode_mem h,s.encode (a.iso h p),s.encode_mem _,
        (t.encode_mem_subset _ h).2 fixed,(a.triple_mem_actionGraph s t h p _).2 rfl,
        (s.pair_mem_conditionOrder _ _).2 lower,(sep h g₁).2 first,(sep h g₂).2 second⟩
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.separationWitnessFormula
      (extend z params)) s.carrier = s.subset (a.SeparationWitness K Sep p g₁ g₂) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz,rel⟩
      obtain ⟨q,rfl⟩ := (s.mem_carrier z).1 hz
      exact (s.encode_mem_subset _ q).2 ((correct q).1 rel)
    · intro hz
      obtain ⟨q,hq,rfl⟩ := (s.mem_subset _ z).1 hz
      exact ⟨s.encode_mem q,(correct q).2 hq⟩
  exact eq ▸ selected

omit a t in
theorem localized_mem (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {E : Set P} (hE : s.subset E ∈ M.sets) (r : P) : s.subset (Localized r E) ∈ M.sets := by
  let params := extend (s.subset E) (extend s.carrier (extend s.conditionOrder (extend (s.encode r) Fin.elim0)))
  have members : ∀ i, params i ∈ M.sets := Fin.cases hE (Fin.cases carrier
    (Fin.cases order (Fin.cases (M.transitive carrier (s.encode_mem r)) (fun i => Fin.elim0 i))))
  have selected := M.bounded_separation_mem separation BoundedFormula.localizedWitnessFormula params members carrier
  have correct (q : P) : BoundedFormula.Truth BoundedFormula.localizedWitnessFormula
      (extend (s.encode q) params) ↔ q ∈ Localized r E := by
    simp only [BoundedFormula.localizedWitnessFormula, BoundedFormula.truth_disj, BoundedFormula.Truth,
      BoundedFormula.truth_exMem, BoundedFormula.truth_pairMembershipFormula]
    change (s.encode q ∈ s.subset E ∨ ¬ ∃ z ∈ s.carrier,
      ZFSet.pair z (s.encode q) ∈ s.conditionOrder ∧
      ZFSet.pair z (s.encode r) ∈ s.conditionOrder) ↔ _
    erw [s.encode_mem_subset]
    have compat : (∃ z ∈ s.carrier, ZFSet.pair z (s.encode q) ∈ s.conditionOrder ∧
        ZFSet.pair z (s.encode r) ∈ s.conditionOrder) ↔ Compatible q r := by
      constructor
      · rintro ⟨z,hz,hq,hr⟩
        obtain ⟨z,rfl⟩ := (s.mem_carrier z).1 hz
        exact ⟨z,(s.pair_mem_conditionOrder _ _).1 hq,(s.pair_mem_conditionOrder _ _).1 hr⟩
      · rintro ⟨z,hq,hr⟩
        exact ⟨s.encode z,s.encode_mem z,(s.pair_mem_conditionOrder _ _).2 hq,
          (s.pair_mem_conditionOrder _ _).2 hr⟩
    rw [compat]
    rfl
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.localizedWitnessFormula
      (extend z params)) s.carrier = s.subset (Localized r E) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz,rel⟩
      obtain ⟨q,rfl⟩ := (s.mem_carrier z).1 hz
      exact (s.encode_mem_subset _ q).2 ((correct q).1 rel)
    · intro hz
      obtain ⟨q,hq,rfl⟩ := (s.mem_subset _ z).1 hz
      exact ⟨s.encode_mem q,(correct q).2 hq⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
include pairing unions powers separation carrier order

theorem ordinary_generic_meets_coded_denseBelow (H : ConditionFilter P)
    (ordinary : H.GenericFor (formulaFamily (M.nameDomain s)))
    {base : P} (member : H.mem base) {E : Set P}
    (ground : s.subset E ∈ M.sets) (dense : DenseBelow base E) : H.Meets E := by
  have localized := M.localized_mem s separation carrier order ground base
  obtain ⟨q, hq, good | bad⟩ := M.ordinary_generic_meets_coded_dense s pairing unions powers
    separation H ordinary localized (localized_dense dense)
  · exact ⟨q, hq, good⟩
  · exact False.elim (bad (H.compatible hq member))

theorem ordinary_generic_candidate_witness (collection : CollectionSchema M.sets)
    {n : Nat} (phi : SetFormula (n + 1)) (env : Assignment (M.nameDomain s) n)
    (W : ZFSet.{u}) (ground : W ∈ M.sets) (valid : ∀ z ∈ W, IsName s z)
    (H : ConditionFilter P) (ordinary : H.GenericFor (formulaFamily (M.nameDomain s)))
    {base : P} (member : H.mem base)
    (dense : DenseBelow base {q | ∃ tau : (M.nameDomain s).names, tau.val.val ∈ W ∧
      Forces (M.nameDomain s) phi (extend tau env) q}) :
    ∃ tau : (M.nameDomain s).names, tau.val.val ∈ W ∧
      ∃ q, H.mem q ∧ Forces (M.nameDomain s) phi (extend tau env) q := by
  have code := M.candidateForcingSet_mem s pairing unions powers separation collection carrier order
    phi env W ground valid
  obtain ⟨q, hq, tau, candidate, forced⟩ :=
    M.ordinary_generic_meets_coded_denseBelow s pairing unions powers separation carrier order
      H ordinary member code dense
  exact ⟨tau, candidate, q, hq, forced⟩

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.SetFormula

private def rectangleOrderFormula : BoundedFormula 15 :=
  .conj (BoundedFormula.tripleMembershipFormula 3 5 1 13)
    (.conj (BoundedFormula.tripleMembershipFormula 2 5 0 13)
      (.conj (BoundedFormula.pairMembershipFormula 4 1 11)
        (BoundedFormula.pairMembershipFormula 4 0 11)))

private def rectangleBodyFormula : SetFormula 15 :=
  .conj rectangleOrderFormula.toFormula
    (.conj (atomicApplication codedNameActionFormula (extend 10 (extend 14 Fin.elim0)) 3 6 8)
      (.conj (atomicApplication codedNameActionFormula (extend 10 (extend 14 Fin.elim0)) 2 6 9)
        (ex (.conj
          (atomicApplication codedNameActionFormula (extend 11 (extend 15 Fin.elim0)) 4 8 0)
          (atomicApplication codedNameActionFormula (extend 11 (extend 15 Fin.elim0)) 3 8 0)))))

def rectangleWitnessFormula : SetFormula 11 :=
  exConditions 8 (exConditions 9 (exConditions 8 (exConditions 9 rectangleBodyFormula)))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (action : a.actionGraph s t ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
include pairing unions powers separation collection carrier order group action maps

omit order action in
private theorem coded_action (g : G) (x : Name s) (hx : x.val ∈ M.sets)
    (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets codedNameActionFormula (extend (t.encode g) (extend x.val (extend z
      (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))) ↔
      z = (a.act s g x).val := by
  rw [M.realize_codedNameActionFormula a s t pairing unions powers separation collection
    carrier group maps g x.val z hx hz]
  constructor
  · rintro ⟨y, eq, out⟩
    have same : y.val = x := Subtype.ext eq
    simpa only [same] using out
  · intro eq
    exact ⟨⟨x, hx⟩, rfl, eq⟩

private noncomputable def rectangleParameters (p : P) (x y : Name s) (g₁ g₂ : G) : Fin 10 → ZFSet.{u} :=
  extend (s.encode p) (extend x.val (extend y.val (extend (a.act s g₁ x).val
    (extend (a.act s g₂ x).val (extend s.carrier (extend s.conditionOrder
      (extend t.carrier (extend (a.actionGraph s t) (extend (a.conditionMapFamily s t) Fin.elim0)))))))))

theorem realize_rectangleWitnessFormula (p : P) (x y : Name s)
    (hx : x.val ∈ M.sets) (hy : y.val ∈ M.sets) (g₁ g₂ : G) (q : P) :
    Realize M.sets rectangleWitnessFormula
      (extend (s.encode q) (rectangleParameters a s t p x y g₁ g₂)) ↔
      q ∈ a.RectangleWitness s p x y g₁ g₂ := by
  have cp (r : P) := M.transitive carrier (s.encode_mem r)
  have cg (g : G) := M.transitive group (t.encode_mem g)
  have ax (g : G) := M.act_mem s a t pairing unions powers separation collection carrier maps g x hx
  rw [rectangleWitnessFormula, M.realize_exConditions t 8 _ _ group rfl]
  apply exists_congr
  intro h₁
  rw [M.realize_exConditions t 9 _ _ group rfl]
  apply exists_congr
  intro h₂
  rw [M.realize_exConditions s 8 _ _ carrier rfl]
  change (∃ p₁, Realize M.sets _ _) ↔ _
  have body (p₁ p₂ : P) :
      Realize M.sets rectangleBodyFormula (extend (s.encode p₂) (extend (s.encode p₁)
        (extend (t.encode h₂) (extend (t.encode h₁)
          (extend (s.encode q) (rectangleParameters a s t p x y g₁ g₂)))))) ↔
      a.iso h₁ p = p₁ ∧ a.iso h₂ p = p₂ ∧ q ≤ p₁ ∧ q ≤ p₂ ∧
        a.act s h₁ x = a.act s g₁ x ∧ a.act s h₂ x = a.act s g₂ x ∧
        a.act s h₁ y = a.act s h₂ y := by
    let env := extend (s.encode p₂) (extend (s.encode p₁) (extend (t.encode h₂)
      (extend (t.encode h₁) (extend (s.encode q) (rectangleParameters a s t p x y g₁ g₂)))))
    have members : ∀ i, env i ∈ M.sets := (Fin.cases (cp p₂) (Fin.cases (cp p₁) (Fin.cases (cg h₂) (Fin.cases (cg h₁) (Fin.cases (cp q) (Fin.cases (M.transitive carrier (s.encode_mem p)) (Fin.cases (hx) (Fin.cases (hy) (Fin.cases (ax g₁) (Fin.cases (ax g₂) (Fin.cases (carrier) (Fin.cases (order) (Fin.cases (group) (Fin.cases (action) (Fin.cases (maps) (fun i => Fin.elim0 i))))))))))))))))
    rw [rectangleBodyFormula]
    change (Realize M.sets rectangleOrderFormula.toFormula env ∧ _ ∧ _ ∧ _) ↔ _
    rw [BoundedFormula.realize_toFormula M _ _ members]
    simp only [rectangleOrderFormula, BoundedFormula.Truth,
      BoundedFormula.truth_tripleMembershipFormula, BoundedFormula.truth_pairMembershipFormula]
    change ((ZFSet.pair (ZFSet.pair (t.encode h₁) (s.encode p)) (s.encode p₁) ∈ a.actionGraph s t ∧
      ZFSet.pair (ZFSet.pair (t.encode h₂) (s.encode p)) (s.encode p₂) ∈ a.actionGraph s t ∧
      ZFSet.pair (s.encode q) (s.encode p₁) ∈ s.conditionOrder ∧
      ZFSet.pair (s.encode q) (s.encode p₂) ∈ s.conditionOrder) ∧ _ ∧ _ ∧ _) ↔ _
    rw [a.triple_mem_actionGraph, a.triple_mem_actionGraph,
      s.pair_mem_conditionOrder, s.pair_mem_conditionOrder]
    simp only [realize_ex]
    change ((_ ∧ _ ∧ _ ∧ _) ∧ _ ∧ _ ∧
      (∃ z ∈ M.sets, Realize M.sets _ _ ∧ Realize M.sets _ _)) ↔ _
    simp only [realize_atomicApplication, map_extend, map_empty]
    change ((a.iso h₁ p = p₁ ∧ a.iso h₂ p = p₂ ∧ q ≤ p₁ ∧ q ≤ p₂) ∧
      Realize M.sets codedNameActionFormula (extend (t.encode h₁) (extend x.val (extend (a.act s g₁ x).val (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))) ∧
      Realize M.sets codedNameActionFormula (extend (t.encode h₂) (extend x.val (extend (a.act s g₂ x).val (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))) ∧
      (∃ z ∈ M.sets, Realize M.sets codedNameActionFormula (extend (t.encode h₁) (extend y.val (extend z (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))) ∧
        Realize M.sets codedNameActionFormula (extend (t.encode h₂) (extend y.val (extend z (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))))) ↔ _
    rw [M.coded_action a s t pairing unions powers separation collection carrier group maps h₁ x hx _ (ax g₁),
      M.coded_action a s t pairing unions powers separation collection carrier group maps h₂ x hx _ (ax g₂)]
    have common : (∃ z ∈ M.sets,
        Realize M.sets codedNameActionFormula (extend (t.encode h₁) (extend y.val (extend z
          (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))) ∧
        Realize M.sets codedNameActionFormula (extend (t.encode h₂) (extend y.val (extend z
          (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0)))))) ↔
        a.act s h₁ y = a.act s h₂ y := by
      constructor
      · rintro ⟨z, hz, first, second⟩
        rw [M.coded_action a s t pairing unions powers separation collection carrier group maps h₁ y hy z hz] at first
        rw [M.coded_action a s t pairing unions powers separation collection carrier group maps h₂ y hy z hz] at second
        exact Subtype.ext (first.symm.trans second)
      · intro eq
        have hz := M.act_mem s a t pairing unions powers separation collection carrier maps h₁ y hy
        refine ⟨(a.act s h₁ y).val, hz, ?_, ?_⟩
        · exact (M.coded_action a s t pairing unions powers separation collection carrier group maps h₁ y hy _ hz).2 rfl
        · exact (M.coded_action a s t pairing unions powers separation collection carrier group maps h₂ y hy _ hz).2 (congrArg Subtype.val eq)
    rw [common]
    constructor
    · rintro ⟨⟨e₁,e₂,b₁,b₂⟩,x₁,x₂,yy⟩
      exact ⟨e₁,e₂,b₁,b₂,Subtype.ext x₁.symm,Subtype.ext x₂.symm,yy⟩
    · rintro ⟨e₁,e₂,b₁,b₂,x₁,x₂,yy⟩
      exact ⟨⟨e₁,e₂,b₁,b₂⟩,congrArg Subtype.val x₁.symm,congrArg Subtype.val x₂.symm,yy⟩
  constructor
  · rintro ⟨p₁, rest⟩
    obtain ⟨p₂, rest⟩ := (M.realize_exConditions s 9 _ _ carrier rfl).1 rest
    obtain ⟨rfl,rfl,b₁,b₂,x₁,x₂,yy⟩ := (body p₁ p₂).1 rest
    exact ⟨b₁,b₂,x₁,x₂,yy⟩
  · rintro ⟨b₁,b₂,x₁,x₂,yy⟩
    refine ⟨a.iso h₁ p, (M.realize_exConditions s 9 _ _ carrier rfl).2 ⟨a.iso h₂ p, ?_⟩⟩
    exact (body _ _).2 ⟨rfl,rfl,b₁,b₂,x₁,x₂,yy⟩

theorem rectangleWitness_mem (p : P) (x y : Name s)
    (hx : x.val ∈ M.sets) (hy : y.val ∈ M.sets) (g₁ g₂ : G) :
    s.subset (a.RectangleWitness s p x y g₁ g₂) ∈ M.sets := by
  let params := rectangleParameters a s t p x y g₁ g₂
  have ax (g : G) := M.act_mem s a t pairing unions powers separation collection carrier maps g x hx
  have members : ∀ i, params i ∈ M.sets := (Fin.cases (M.transitive carrier (s.encode_mem p)) (Fin.cases (hx) (Fin.cases (hy) (Fin.cases (ax g₁) (Fin.cases (ax g₂) (Fin.cases (carrier) (Fin.cases (order) (Fin.cases (group) (Fin.cases (action) (Fin.cases (maps) (fun i => Fin.elim0 i)))))))))))
  have selected := M.separation_mem separation rectangleWitnessFormula params members carrier
  have eq : ZFSet.sep (fun z => Realize M.sets rectangleWitnessFormula (extend z params)) s.carrier =
      s.subset (a.RectangleWitness s p x y g₁ g₂) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz,rel⟩
      obtain ⟨q,rfl⟩ := (s.mem_carrier z).1 hz
      exact (s.encode_mem_subset _ q).2 ((M.realize_rectangleWitnessFormula a s t pairing unions powers separation collection carrier order group action maps p x y hx hy g₁ g₂ q).1 rel)
    · intro hz
      obtain ⟨q,hq,rfl⟩ := (s.mem_subset _ z).1 hz
      exact ⟨s.encode_mem q,(M.realize_rectangleWitnessFormula a s t pairing unions powers separation collection carrier order group action maps p x y hx hy g₁ g₂ q).2 hq⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem copyWitnessFamily_coded
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (action : a.actionGraph s t ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (K : Subgroup G) (hK : t.subset (fun g => g ∈ K) ∈ M.sets)
    (Sep : G → G → Prop)
    (hSep : (t.product t).subset (fun gh => Sep gh.1 gh.2) ∈ M.sets)
    (p : P) (x y : Name s) (hx : x.val ∈ M.sets) (hy : y.val ∈ M.sets) :
    a.copyWitnessFamily s K Sep p x y ⊆ M.codedFamily s := by
  intro E member
  rcases member with ⟨r,g₁,g₂,rfl⟩ | ⟨r,g₁,g₂,rfl⟩
  · exact M.codedFamily_of_code s (M.localized_mem s separation carrier order
      (M.rectangleWitness_mem a s t pairing unions powers separation collection
        carrier order group action maps p x y hx hy g₁ g₂) r)
  · exact M.codedFamily_of_code s (M.localized_mem s separation carrier order
      (M.separationWitness_mem a s t separation carrier order group action K hK Sep hSep p g₁ g₂) r)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.GroundMainFinalGeometry
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (geometry : GroundMainFinalGeometry M C D rD)

theorem internalRow_copyWitnessFamily_coded
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets) :
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    let b := SetMembers.presentation geometry.actors
    let a := geometry.decodedAction
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    ∀ (p : SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega))
      (x y : Name c) (_hx : x.val ∈ M.sets) (_hy : y.val ∈ M.sets)
      (W d : SetMembers geometry.carrier),
      act.copyWitnessFamily c (a.principalFix W)
        (fun g h => geometry.meet.smallMeet (a.iso g d) (a.iso h d) = W) p x y ⊆ M.codedFamily c := by
  let geometryGroup := geometry.group_code.toGroup
  let geometryOrder := geometry.meet.order.toPartialOrder
  let geometryBottom := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let rowOrder := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground
    (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  dsimp only
  intro p x y hx hy W d
  have coordinateGround := M.rowCoordinate_carrier_mem s columns pairing unions powers separation
    geometry.carrier_ground hColumns
  have bits := M.natSetCode_mem separation infinite 2
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinateGround bits
  have order := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinateGround bits
  have actionGraph := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground
    (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
  have maps := M.conditionMapFamily_mem_of_actionGraph act c b pairing unions powers separation collection
    carrier geometry.actors_ground actionGraph
  have support := M.supportBasis_fiber_mem b s a.principalFix pairing separation
    geometry.actors_ground geometry.carrier_ground
    (geometry.decoded_supportBasis_ground pairing unions powers separation) W
  exact M.copyWitnessFamily_coded act c b pairing unions powers separation collection carrier order
    geometry.actors_ground actionGraph maps (a.principalFix W) support _
    (geometry.separatedActorPairs_mem pairing unions powers separation d W) p x y hx hy

theorem internalRow_copyWitness_generic
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets) :
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    let b := SetMembers.presentation geometry.actors
    let a := geometry.decodedAction
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    ∀ (p : SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega))
      (x y : Name c) (_hx : x.val ∈ M.sets) (_hy : y.val ∈ M.sets)
      (W d : SetMembers geometry.carrier),
      ∀ (H : ConditionFilter (SetMembers (M.smallPartialFunctions
          (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega))),
        H.GenericFor (M.codedFamily c) → H.GenericFor
          (act.copyWitnessFamily c (a.principalFix W)
            (fun g h => geometry.meet.smallMeet (a.iso g d) (a.iso h d) = W) p x y) := by
  let geometryGroup := geometry.group_code.toGroup
  let geometryOrder := geometry.meet.order.toPartialOrder
  let geometryBottom := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let rowOrder := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground
    (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  dsimp only
  intro p x y hx hy W d H generic E member dense
  exact generic E (geometry.internalRow_copyWitnessFamily_coded pairing unions powers separation
    collection infinite columns hColumns p x y hx hy W d member) dense

end PartitionPilot.Forcing.GroundMainFinalGeometry

end


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem forcesEq_mix_of_copy_refinements
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (small : M.sets.Countable)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (action : a.actionGraph s t ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (K : Subgroup G) (hK : t.subset (fun g => g ∈ K) ∈ M.sets)
    (Sep : G → G → Prop)
    (hSep : (t.product t).subset (fun gh => Sep gh.1 gh.2) ∈ M.sets)
    (p : P) (x y : Name s) (hx : x.val ∈ M.sets) (hy : y.val ∈ M.sets)
    (equal : Name.ForcesEq p x y)
    (rectangles : ∀ g₁ ∈ K, ∀ g₂ ∈ K, Sep g₁ g₂ → ∀ r,
      r ≤ a.iso g₁ p → r ≤ a.iso g₂ p →
        DenseBelow r (a.RectangleWitness s p x y g₁ g₂))
    (separating : ∀ g₁ ∈ K, ∀ g₂ ∈ K, ∀ r,
      r ≤ a.iso g₁ p → r ≤ a.iso g₂ p →
        DenseBelow r (a.SeparationWitness K Sep p g₁ g₂)) :
    Name.ForcesEq p x (a.mix s K p x) := by
  have groundMix := M.mix_mem a s t pairing unions powers separation collection
    carrier order group maps K hK p x hx
  have witnesses := M.copyWitnessFamily_coded a s t pairing unions powers separation
    collection carrier order group action maps K hK Sep hSep p x y hx hy
  let env : Assignment (M.nameDomain s) 2 :=
    extend ⟨x, hx⟩ (extend ⟨a.mix s K p x, groundMix⟩ Fin.elim0)
  change Forces (M.nameDomain s) (.equal 0 1) env p
  apply (M.ordinaryForces_iff_all_joint_generics s small carrier (.equal 0 1) env p).2
  intro H active coded ordinary
  change Name.eval {q | H.mem q} x = Name.eval {q | H.mem q} (a.mix s K p x)
  have copies : H.GenericFor (a.copyWitnessFamily s K Sep p x y) :=
    fun E hE => coded E (witnesses hE)
  have atomic : H.GenericFor (Name.atomicFamily (M.nameDomain s)) :=
    fun E hE => ordinary E (Or.inl hE)
  have translated : ∀ g, H.mem (a.iso g p) →
      Name.eval {q | H.mem q} (a.act s g x) =
        Name.eval {q | H.mem q} (a.act s g y) := by
    intro g member
    exact Name.forcesEq_sound (M.nameDomain s) H atomic _
      (M.act_mem s a t pairing unions powers separation collection carrier maps g x hx) _
      (M.act_mem s a t pairing unions powers separation collection carrier maps g y hy)
      _ member (a.forcesEq_act s g equal)
  exact (a.mix_capture_from_refinements s K Sep p x y H copies active translated
    rectangles separating).symm

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalFulfillment level i₀)

theorem structural_mixture_forcing
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
    (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (stagesOrdinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  ∀ (p : SetMembers upperQ) (sourceRow : SetMembers c.carrier) (A : ZFSet.{u})
    (V W : SetMembers geometry.carrier) (x y : Name upper),
    SetMembers.raw p = ZFSet.pair (c.encode sourceRow) A →
    StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (SetMembers.raw p) →
    x.val ∈ M.sets → y.val ∈ M.sets →
    a.principalFix V ≤ upperAct.stabilizer upper x →
    a.principalFix W ≤ upperAct.stabilizer upper y →
    Name.ForcesEq p x y →
    (∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
      let subset := (And.left stagesOrdinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      ∀ (H : ConditionFilter (SetMembers Q)),
        H.GenericFor (M.codedFamily lower) → H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
          a.principalFix v ≤ localAct.stabilizer lower x.val →
          a.principalFix w ≤ localAct.stabilizer lower y.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) x.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) y.val →
          Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
          ∃ tau : (M.nameDomain lower).names,
            HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) tau.val ∧
            a.principalFix (geometry.meet.smallMeet v w) ≤ localAct.stabilizer lower tau.val ∧
            Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val) →
    Name.ForcesEq p x
      (upperAct.mix upper (a.principalFix (geometry.meet.smallMeet V W)) p x) := by
  let geometry := run.finalGeometry i₀
  let geometryGroup := geometry.group_code.toGroup
  let geometryOrder := geometry.meet.order.toPartialOrder
  let geometryBottom := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let rowOrder := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let rowTop := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let historyOrder := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  intro p sourceRow A V W x y pCode prepared hx hy sx sy equal descent
  obtain ⟨dBound, vd, wd, usedD, dataD⟩ := fulfilled.structural_bounds_with
    collection infinite choice columns hColumns hmu muOrdinal valid hLifted hSquared
    valid1 valid2 closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    p sourceRow A V W pCode
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers
    separation carrier hLifted hs hPacked omega
  have hOrder : upper.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier forcingOrder
      hLifted hs hPacked omega
  have hAssignments := (M.definable_structuralAssignments pairing unions powers separation collection).closed
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hAssignmentAction := M.structuralAssignmentActionGraph_mem pairing unions powers separation
    collection hG hL order graph supports hLifted hSquared hs hh
  have hGraph : upperAct.actionGraph upper b ∈ M.sets := by
    erw [M.semanticStructuralAction_graph]
    exact M.rawRowAssignmentActionGraph_mem pairing unions powers separation collection hG hQ
      carrier (M.union_mem unions (M.union_mem unions hQ)) hAssignments forcingAction hAssignmentAction
  have maps := M.conditionMapFamily_mem_of_actionGraph upperAct upper b pairing unions powers separation
    collection hQ hG hGraph
  let B := geometry.meet.smallMeet V W
  have hK := M.supportBasis_fiber_mem b s a.principalFix pairing separation hG hL supports B
  have hSep := geometry.separatedActorPairs_mem pairing unions powers separation dBound B
  apply M.forcesEq_mix_of_copy_refinements upperAct upper b pairing unions powers separation
    collection small hQ hOrder hG hGraph maps (a.principalFix B) hK
    (fun g h => geometry.meet.smallMeet (a.iso g dBound) (a.iso h dBound) = B)
    hSep p x y hx hy equal
  · intro g1 fixed1 g2 fixed2 separated r ref1 ref2
    exact fulfilled.structural_rectangle_refinement
      collection infinite choice small columns hColumns hmu muOrdinal valid hLifted hSquared
      valid1 valid2 closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
      p sourceRow A dBound V W x y pCode prepared usedD dataD vd wd sx sy descent
      g1 g2 fixed1 fixed2 separated r ref1 ref2
  · intro g1 fixed1 g2 fixed2 r ref1 _ref2
    exact fulfilled.structural_separation_refinement
      collection infinite choice small columns hColumns hmu muOrdinal valid hLifted hSquared
      valid1 valid2 closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
      p sourceRow A B dBound pCode prepared usedD dataD
      (le_trans (geometry.meet.toSmallMeetOrder.meet_le_left V W) vd) descent
      g1 g2 fixed1 fixed2 r ref1

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment




namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)

theorem structural_dense_mixture_equalities
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
    (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (stagesOrdinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  ∀ (p0 : SetMembers upperQ) (V W : SetMembers geometry.carrier) (x y : Name upper),
    x.val ∈ M.sets → y.val ∈ M.sets →
    a.principalFix V ≤ upperAct.stabilizer upper x →
    a.principalFix W ≤ upperAct.stabilizer upper y →
    Name.ForcesEq p0 x y →
    (∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
      let subset := (And.left stagesOrdinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      ∀ (H : ConditionFilter (SetMembers Q)),
        H.GenericFor (M.codedFamily lower) → H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
          a.principalFix v ≤ localAct.stabilizer lower x.val →
          a.principalFix w ≤ localAct.stabilizer lower y.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) x.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) y.val →
          Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
          ∃ tau : (M.nameDomain lower).names,
            HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) tau.val ∧
            a.principalFix (geometry.meet.smallMeet v w) ≤ localAct.stabilizer lower tau.val ∧
            Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val) →
    DenseBelow p0 {p | Name.ForcesEq p x
      (upperAct.mix upper (a.principalFix (geometry.meet.smallMeet V W)) p x)} := by
  let geometry := run.finalGeometry i₀
  let geometryGroup := geometry.group_code.toGroup
  let geometryOrder := geometry.meet.order.toPartialOrder
  let geometryBottom := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let rowOrder := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let rowTop := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let historyOrder := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  intro p0 V W x y groundX groundY supportX supportY equal descent q below0
  have rowClosed := M.countable_function_internally_closed pairing unions powers separation
    infinite choice coordinates two
  obtain ⟨rawP, memberP, pq, prepared⟩ := fulfilled.exists_groundStoredPreparedStrengthening c
    collection infinite choice small smallD irreflexive rowClosed act lifted squared (c.encode ⊤)
    carrier forcingOrder forcingAction hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    topMem topRows stages history hs hh stagesOrdinal trace descent (SetMembers.raw q) (SetMembers.raw_mem q)
  let p : SetMembers upperQ := SetMembers.ofMem rawP memberP
  have pRaw : SetMembers.raw p = rawP := SetMembers.raw_ofMem _ _
  have below : p ≤ q := by
    change ZFSet.pair (SetMembers.raw p) (SetMembers.raw q) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder lifted stages packed
    rw [pRaw]
    exact pq
  have preparedP : StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier
      (SetMembers.raw p) := by
    rw [pRaw]
    exact prepared
  obtain ⟨sourceRow, A, _, pCode⟩ := exists_presentedRowAssignmentCoordinates c
    (M.refinementHistoryForcing_shape c.carrier lifted stages packed) (SetMembers.raw_mem p)
  refine ⟨p, below, ?_⟩
  exact fulfilled.toFinalFulfillment.structural_mixture_forcing
    collection infinite choice small columns hColumns hmu muOrdinal valid hLifted hSquared
    valid1 valid2 closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    p sourceRow A V W x y pCode preparedP groundX groundY supportX supportY
    (Name.forcesEq_mono equal (le_trans below below0)) descent






theorem structural_common_support
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
    (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (stagesOrdinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  ∀ (H : ConditionFilter (SetMembers upperQ))
    (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain upper)))
    (V W : SetMembers geometry.carrier) (x y : Name upper),
    x.val ∈ M.sets → y.val ∈ M.sets →
    a.principalFix V ≤ upperAct.stabilizer upper x →
    a.principalFix W ≤ upperAct.stabilizer upper y →
    HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) x →
    Name.eval {p | H.mem p} x = Name.eval {p | H.mem p} y →
    (∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
      let subset := (And.left stagesOrdinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      ∀ (H : ConditionFilter (SetMembers Q)),
        H.GenericFor (M.codedFamily lower) → H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
          a.principalFix v ≤ localAct.stabilizer lower x.val →
          a.principalFix w ≤ localAct.stabilizer lower y.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) x.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) y.val →
          Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
          ∃ tau : (M.nameDomain lower).names,
            HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) tau.val ∧
            a.principalFix (geometry.meet.smallMeet v w) ≤ localAct.stabilizer lower tau.val ∧
            Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val) →
    ∃ z : Name upper, z.val ∈ M.sets ∧
      HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) z ∧
      a.principalFix (geometry.meet.smallMeet V W) ≤ upperAct.stabilizer upper z ∧
      Name.nameRank z ≤ Name.nameRank x ∧
      Name.eval {p | H.mem p} z = Name.eval {p | H.mem p} x := by
  let geometry := run.finalGeometry i₀
  let geometryGroup := geometry.group_code.toGroup
  let geometryOrder := geometry.meet.order.toPartialOrder
  let geometryBottom := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let rowOrder := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let rowTop := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let historyOrder := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  intro H genericFormula V W x y groundX groundY supportX supportY symmetric values descent
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have recursive := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let historyTop := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
    recursive.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
  have upperCarrier : upper.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hLifted hs hPacked omega
  have upperOrder : upper.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier forcingOrder
      hLifted hs hPacked omega
  have upperGraph : upperAct.actionGraph upper b ∈ M.sets := by
    erw [M.semanticStructuralAction_graph]
    exact M.structuralForcingActionGraph_mem pairing unions powers separation collection
      carrier forcingAction hG hL order graph supports hLifted hSquared hs hh omega
  have upperMaps := M.conditionMapFamily_mem_of_actionGraph upperAct upper b
    pairing unions powers separation collection upperCarrier hG upperGraph
  have atoms : H.GenericFor (Name.atomicFamily (M.nameDomain upper)) :=
    fun E member => genericFormula E (Or.inl member)
  obtain ⟨p0, active, equal⟩ :=
    (Name.eval_eq_iff_forcesEq (M.nameDomain upper) H atoms groundX groundY).1 values
  have dense := fulfilled.structural_dense_mixture_equalities collection infinite choice small
    smallD irreflexive columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2
    closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    p0 V W x y groundX groundY supportX supportY equal descent
  obtain ⟨z, _candidate, groundZ, hsZ, supportZ, rankZ, valueZ⟩ :=
    M.exists_mixtureCandidate_of_dense upperAct upper b s a.principalFix
      pairing unions powers separation collection upperCarrier upperOrder hG hL supports upperMaps
      (a.principalSupportFamily ⊥ directed) (geometry.meet.smallMeet V W)
      ⟨geometry.meet.smallMeet V W, le_rfl⟩ x groundX symmetric p0 dense H genericFormula active
  exact ⟨z, groundZ, hsZ, supportZ, rankZ, valueZ⟩






theorem structural_common_support_all_stages
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
    (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (stagesOrdinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  ∀ (H : ConditionFilter (SetMembers upperQ))
    (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain upper)))
    (V W : SetMembers geometry.carrier) (x y : Name upper),
    x.val ∈ M.sets → y.val ∈ M.sets →
    a.principalFix V ≤ upperAct.stabilizer upper x →
    a.principalFix W ≤ upperAct.stabilizer upper y →
    HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) x →
    Name.eval {p | H.mem p} x = Name.eval {p | H.mem p} y →
    ∃ z : Name upper, z.val ∈ M.sets ∧
      HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) z ∧
      a.principalFix (geometry.meet.smallMeet V W) ≤ upperAct.stabilizer upper z ∧
      Name.nameRank z ≤ Name.nameRank x ∧
      Name.eval {p | H.mem p} z = Name.eval {p | H.mem p} x := by
  let geometry := run.finalGeometry i₀
  let geometryGroup := geometry.group_code.toGroup
  let geometryOrder := geometry.meet.order.toPartialOrder
  let geometryBottom := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let rowOrder := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let rowTop := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2 stages
  induction stages using ZFSet.inductionOn with
  | h stages ih =>
    intro history hs hh stagesOrdinal trace
    let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
    let two := M.natSetCode_mem separation infinite 2
    let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
    let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
    let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
    let omega := M.omega_mem separation infinite
    let topMem := c.encode_mem ⊤
    let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
      fun r hr => by
        obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
        exact (c.pair_mem_conditionOrder r ⊤).2 le_top
    let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
      (supportBasisCode s b a.principalFix) lifted squared stages history
    let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
    let historyOrder := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
    let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
      topMem topRows hs hh stagesOrdinal trace
    let upper := SetMembers.presentation upperQ
    intro H genericFormula V W x y groundX groundY supportX supportY symmetric values
    apply fulfilled.structural_common_support collection infinite choice small smallD irreflexive
      columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
      children1 children2 stages history hs hh stagesOrdinal trace
      H genericFormula V W x y groundX groundY supportX supportY symmetric values
    intro alpha member
    let hAlpha := M.transitive hs member
    let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
    let subset := (And.left stagesOrdinal) alpha member
    let Property : ∀ (Q : ZFSet.{u}) (orderQ : PartialOrder (SetMembers Q)),
        @PosetAction (SetMembers geometry.actors) _ (SetMembers Q) orderQ → Prop :=
      fun Q orderQ actionQ =>
        letI := orderQ
        let presentation := SetMembers.presentation Q
        ∀ (filter : ConditionFilter (SetMembers Q)),
          filter.GenericFor (formulaFamily (M.nameDomain presentation)) →
          ∀ (v w : SetMembers geometry.carrier) (first second : Name presentation),
            first.val ∈ M.sets → second.val ∈ M.sets →
            a.principalFix v ≤ actionQ.stabilizer presentation first →
            a.principalFix w ≤ actionQ.stabilizer presentation second →
            HereditarilySymmetric actionQ presentation (a.principalSupportFamily ⊥ directed) first →
            Name.eval {q | filter.mem q} first = Name.eval {q | filter.mem q} second →
            ∃ z : Name presentation, z.val ∈ M.sets ∧
              HereditarilySymmetric actionQ presentation (a.principalSupportFamily ⊥ directed) z ∧
              a.principalFix (geometry.meet.smallMeet v w) ≤ actionQ.stabilizer presentation z ∧
              Name.nameRank z ≤ Name.nameRank first ∧
              Name.eval {q | filter.mem q} z = Name.eval {q | filter.mem q} first
    have earlier := ih alpha member (graphRestriction alpha history) hAlpha
      (M.graphRestriction_mem unions separation hAlpha hh) cutOrdinal
      (trace.restrict cutOrdinal subset)
    have transferred := (M.semanticStructuralPrefixAction_restricted_property c act b s a ⊥
      directed lifted squared (c.encode ⊤) pairing unions powers separation collection
      carrier forcingOrder forcingAction hG hL order graph nodeMaps supports hLifted hSquared
      omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows
      hh trace hAlpha cutOrdinal subset Property).1 earlier
    dsimp only
    intro lowerH _coded ordinary v w first second firstSupport secondSupport firstHS _secondHS equal
    obtain ⟨z, groundZ, symmetricZ, supportZ, _rankZ, valueZ⟩ := transferred lowerH ordinary
      v w first.val second.val first.property second.property firstSupport secondSupport firstHS equal
    exact ⟨⟨z, groundZ⟩, symmetricZ, supportZ, valueZ⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
