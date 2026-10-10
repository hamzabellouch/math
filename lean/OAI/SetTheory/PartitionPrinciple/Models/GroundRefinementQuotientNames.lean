import OAI.SetTheory.PartitionPrinciple.Definability.GroundRefinementPairClassGraphs
import OAI.SetTheory.PartitionPrinciple.Forcing.ActiveNameImageSymmetry
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundIndexedClassInclusions

namespace OAI


namespace PartitionPilot.Forcing

universe u

noncomputable def refinementQuotientMap (U Rf Rc : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose (equivalenceClasses U Rf) U (equivalenceClasses U Rc)
    (relationConverse U (equivalenceClasses U Rf) (equivalenceClassifier U Rf))
    (equivalenceClassifier U Rc)

theorem refinementQuotientMap_subset (U Rf Rc : ZFSet.{u}) :
    refinementQuotientMap U Rf Rc ⊆
      ZFSet.prod (equivalenceClasses U Rf) (equivalenceClasses U Rc) := by
  intro z hz
  rw [refinementQuotientMap, relationCompose, ZFSet.mem_sep] at hz
  exact hz.1

theorem pair_mem_refinementQuotientMap (U Rf Rc C D : ZFSet.{u}) :
    ZFSet.pair C D ∈ refinementQuotientMap U Rf Rc ↔
      ∃ x ∈ U, C = equivalenceClass U Rf x ∧ D = equivalenceClass U Rc x := by
  rw [refinementQuotientMap, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, x, hx, first, second⟩
    exact ⟨x, hx,
      ((pair_mem_equivalenceClassifier U Rf x C).1
        ((pair_mem_relationConverse _ _ _ x C).1 first).2.2).2,
      ((pair_mem_equivalenceClassifier U Rc x D).1 second).2⟩
  · rintro ⟨x, hx, rfl, rfl⟩
    have hf := equivalenceClass_mem (E := Rf) hx
    have hc := equivalenceClass_mem (E := Rc) hx
    exact ⟨hf, hc, x, hx, (pair_mem_relationConverse _ _ _ x _).2
      ⟨hx, hf, (pair_mem_equivalenceClassifier U Rf x _).2 ⟨hx, rfl⟩⟩,
      (pair_mem_equivalenceClassifier U Rc x _).2 ⟨hx, rfl⟩⟩

theorem mem_refinementQuotientMap (U Rf Rc z : ZFSet.{u}) :
    z ∈ refinementQuotientMap U Rf Rc ↔
      ∃ x ∈ U, z = ZFSet.pair (equivalenceClass U Rf x) (equivalenceClass U Rc x) := by
  constructor
  · intro hz
    obtain ⟨C, _, D, _, rfl⟩ := ZFSet.mem_prod.1 (refinementQuotientMap_subset U Rf Rc hz)
    obtain ⟨x, hx, rfl, rfl⟩ := (pair_mem_refinementQuotientMap U Rf Rc C D).1 hz
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (pair_mem_refinementQuotientMap U Rf Rc _ _).2 ⟨x, hx, rfl, rfl⟩

theorem refinementQuotientMap_class_entry {U Rf Rc x : ZFSet.{u}} (hx : x ∈ U) :
    ZFSet.pair (equivalenceClass U Rf x) (equivalenceClass U Rc x) ∈
      refinementQuotientMap U Rf Rc :=
  (pair_mem_refinementQuotientMap U Rf Rc _ _).2 ⟨x, hx, rfl, rfl⟩

theorem equivalenceClass_refinement_subset {U Rf Rc x : ZFSet.{u}}
    (refinement : Rf ⊆ Rc) : equivalenceClass U Rf x ⊆ equivalenceClass U Rc x := by
  intro y hy
  obtain ⟨hy, related⟩ := (mem_equivalenceClass U Rf x y).1 hy
  exact (mem_equivalenceClass U Rc x y).2 ⟨hy, refinement related⟩

theorem refinementQuotientMap_value_iff {U Rf Rc x D : ZFSet.{u}}
    (fine : EquivalenceRelationCode U Rf) (coarse : EquivalenceRelationCode U Rc)
    (refinement : Rf ⊆ Rc) (hx : x ∈ U) :
    ZFSet.pair (equivalenceClass U Rf x) D ∈ refinementQuotientMap U Rf Rc ↔
      D = equivalenceClass U Rc x := by
  constructor
  · intro entry
    obtain ⟨y, hy, equal, rfl⟩ :=
      (pair_mem_refinementQuotientMap U Rf Rc _ D).1 entry
    exact ((coarse.class_eq_iff hx hy).2
      (refinement ((fine.class_eq_iff hx hy).1 equal))).symm
  · rintro rfl
    exact refinementQuotientMap_class_entry hx

theorem refinementQuotientMap_function {U Rf Rc : ZFSet.{u}}
    (fine : EquivalenceRelationCode U Rf) (coarse : EquivalenceRelationCode U Rc)
    (refinement : Rf ⊆ Rc) :
    ZFSet.IsFunc (equivalenceClasses U Rf) (equivalenceClasses U Rc)
      (refinementQuotientMap U Rf Rc) := by
  refine ⟨refinementQuotientMap_subset U Rf Rc, ?_⟩
  intro C hC
  obtain ⟨x, hx, rfl⟩ := (mem_equivalenceClasses U Rf C).1 hC
  exact ⟨equivalenceClass U Rc x, refinementQuotientMap_class_entry hx,
    fun D entry => (refinementQuotientMap_value_iff fine coarse refinement hx).1 entry⟩

theorem refinementQuotientMap_onto {U Rf Rc D : ZFSet.{u}}
    (hD : D ∈ equivalenceClasses U Rc) :
    ∃ C ∈ equivalenceClasses U Rf, ZFSet.pair C D ∈ refinementQuotientMap U Rf Rc := by
  obtain ⟨x, hx, rfl⟩ := (mem_equivalenceClasses U Rc D).1 hD
  exact ⟨equivalenceClass U Rf x, equivalenceClass_mem hx,
    refinementQuotientMap_class_entry hx⟩

theorem refinementQuotientMap_entry_iff_subset {U Rf Rc C D : ZFSet.{u}}
    (fine : EquivalenceRelationCode U Rf) (coarse : EquivalenceRelationCode U Rc)
    (refinement : Rf ⊆ Rc) :
    ZFSet.pair C D ∈ refinementQuotientMap U Rf Rc ↔
      C ∈ equivalenceClasses U Rf ∧ D ∈ equivalenceClasses U Rc ∧ C ⊆ D := by
  constructor
  · intro entry
    obtain ⟨x, hx, rfl, rfl⟩ := (pair_mem_refinementQuotientMap U Rf Rc C D).1 entry
    exact ⟨equivalenceClass_mem hx, equivalenceClass_mem hx,
      equivalenceClass_refinement_subset refinement⟩
  · rintro ⟨hC, hD, subset⟩
    obtain ⟨x, hx, rfl⟩ := (mem_equivalenceClasses U Rf C).1 hC
    obtain ⟨y, hy, rfl⟩ := (mem_equivalenceClasses U Rc D).1 hD
    have related := ((mem_equivalenceClass U Rc y x).1 (subset (fine.class_self hx))).2
    exact (refinementQuotientMap_value_iff fine coarse refinement hx).2
      ((coarse.class_eq_iff hx hy).2 related).symm

theorem refinementQuotientMap_member_value {U Rf Rc C D x : ZFSet.{u}}
    (fine : EquivalenceRelationCode U Rf) (coarse : EquivalenceRelationCode U Rc)
    (refinement : Rf ⊆ Rc) (entry : ZFSet.pair C D ∈ refinementQuotientMap U Rf Rc)
    (hx : x ∈ C) : D = equivalenceClass U Rc x := by
  obtain ⟨y, hy, rfl, rfl⟩ := (pair_mem_refinementQuotientMap U Rf Rc C D).1 entry
  obtain ⟨hx, xy⟩ := (mem_equivalenceClass U Rf y x).1 hx
  have classEqual := (fine.class_eq_iff hx hy).2 xy
  exact (refinementQuotientMap_value_iff fine coarse refinement hx).1
    (classEqual.symm ▸ refinementQuotientMap_class_entry (Rf := Rf) (Rc := Rc) hy)

theorem refinementQuotientMap_triangle {U Rf Rc : ZFSet.{u}}
    (fine : EquivalenceRelationCode U Rf) (coarse : EquivalenceRelationCode U Rc)
    (refinement : Rf ⊆ Rc) :
    relationCompose U (equivalenceClasses U Rf) (equivalenceClasses U Rc)
      (equivalenceClassifier U Rf) (refinementQuotientMap U Rf Rc) =
      equivalenceClassifier U Rc := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, C, _, D, _, rfl, first, second⟩ := (mem_relationCompose _ _ _ _ _ z).1 hz
    have equal := ((pair_mem_equivalenceClassifier U Rf x C).1 first).2
    subst C
    exact (pair_mem_equivalenceClassifier U Rc x D).2
      ⟨hx, (refinementQuotientMap_value_iff fine coarse refinement hx).1 second⟩
  · intro hz
    obtain ⟨x, hx, rfl⟩ := (mem_equivalenceClassifier U Rc z).1 hz
    exact (pair_mem_relationCompose _ _ _ _ _ x _).2
      ⟨hx, equivalenceClass_mem hx, equivalenceClass U Rf x, equivalenceClass_mem hx,
        (pair_mem_equivalenceClassifier U Rf x _).2 ⟨hx, rfl⟩,
        refinementQuotientMap_class_entry hx⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u

variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem refinementQuotientMap_mem
    {U Rf Rc : ZFSet.{u}} (hU : U ∈ M.sets) (hf : Rf ∈ M.sets) (hc : Rc ∈ M.sets) :
    refinementQuotientMap U Rf Rc ∈ M.sets := by
  have fineClasses := M.equivalenceClasses_mem powers separation hU hf
  have coarseClasses := M.equivalenceClasses_mem powers separation hU hc
  have fineClassifier := M.equivalenceClassifier_mem pairing unions
    powers separation hU hf
  have coarseClassifier := M.equivalenceClassifier_mem pairing unions
    powers separation hU hc
  have converse := M.relationConverse_mem pairing unions powers
    separation hU fineClasses fineClassifier
  exact M.relationCompose_mem pairing unions powers separation
    fineClasses hU coarseClasses converse coarseClassifier

theorem refinementQuotientMap_spec
    {U Rf Rc : ZFSet.{u}} (hU : U ∈ M.sets) (hf : Rf ∈ M.sets) (hc : Rc ∈ M.sets)
    (fine : EquivalenceRelationCode U Rf) (coarse : EquivalenceRelationCode U Rc)
    (refinement : Rf ⊆ Rc) :
    equivalenceClasses U Rf ∈ M.sets ∧ equivalenceClasses U Rc ∈ M.sets ∧
      refinementQuotientMap U Rf Rc ∈ M.sets ∧
      ZFSet.IsFunc (equivalenceClasses U Rf) (equivalenceClasses U Rc)
        (refinementQuotientMap U Rf Rc) ∧
      (∀ D ∈ equivalenceClasses U Rc, ∃ C ∈ equivalenceClasses U Rf,
        ZFSet.pair C D ∈ refinementQuotientMap U Rf Rc) ∧
      (∀ C D, ZFSet.pair C D ∈ refinementQuotientMap U Rf Rc ↔
        C ∈ equivalenceClasses U Rf ∧ D ∈ equivalenceClasses U Rc ∧ C ⊆ D) :=
  ⟨M.equivalenceClasses_mem powers separation hU hf,
    M.equivalenceClasses_mem powers separation hU hc,
    M.refinementQuotientMap_mem pairing unions powers separation hU hf hc,
    refinementQuotientMap_function fine coarse refinement,
    fun _ hD => refinementQuotientMap_onto hD,
    fun _ _ => refinementQuotientMap_entry_iff_subset fine coarse refinement⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem equivalenceClass_eq_of_carrier_subset {T U R : ZFSet.{u}}
    (subset : U ⊆ T) (shape : R ⊆ ZFSet.prod U U) (x : ZFSet.{u}) :
    equivalenceClass T R x = equivalenceClass U R x := by
  apply ZFSet.ext
  intro y
  rw [mem_equivalenceClass, mem_equivalenceClass]
  exact ⟨fun h => ⟨(ZFSet.pair_mem_prod.1 (shape h.2)).1, h.2⟩,
    fun h => ⟨subset h.1, h.2⟩⟩

namespace Name
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

noncomputable def refinementQuotient (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U R : Name s) : Name s :=
  activeImage T valid U (refinementClass T valid R)

noncomputable def refinementNaturalMap (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U Rf Rc : Name s) : Name s :=
  activeImage T valid U (fun w =>
    orderedPair ⊤ (refinementClass T valid Rf w) (refinementClass T valid Rc w))

theorem entry_refinementQuotient (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U R σ : Name s) (p : P) :
    Entry σ (refinementQuotient T valid U R) p ↔
      ∃ w : Name s, w.val ∈ T ∧ ForcesMem p w U ∧ refinementClass T valid R w = σ :=
  entry_activeImage T valid U _ σ p

theorem entry_refinementNaturalMap (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U Rf Rc σ : Name s) (p : P) :
    Entry σ (refinementNaturalMap T valid U Rf Rc) p ↔
      ∃ w : Name s, w.val ∈ T ∧ ForcesMem p w U ∧
        orderedPair ⊤ (refinementClass T valid Rf w) (refinementClass T valid Rc w) = σ :=
  entry_activeImage T valid U _ σ p

theorem eval_refinementQuotient (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D))
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (U R : Name s)
    (hU : U ∈ D.names) (hR : R ∈ D.names)
    (terms : ∀ w : Name s, w.val ∈ T → w ∈ D.names)
    (pairs : ∀ z w : Name s, z.val ∈ T → w.val ∈ T → orderedPair ⊤ z w ∈ D.names)
    (subset : eval {p | H.mem p} U ⊆ eval {p | H.mem p} (familySet ⊤ T valid))
    (shape : eval {p | H.mem p} R ⊆ ZFSet.prod (eval {p | H.mem p} U) (eval {p | H.mem p} U)) :
    eval {p | H.mem p} (refinementQuotient T valid U R) =
      equivalenceClasses (eval {p | H.mem p} U) (eval {p | H.mem p} R) := by
  have value (w : Name s) (hw : w.val ∈ T) :=
    (eval_refinementClass D H generic T valid R w hR (fun z hz => pairs z w hz hw)).trans
      (equivalenceClass_eq_of_carrier_subset subset shape (eval {p | H.mem p} w))
  apply ZFSet.ext
  intro C
  rw [refinementQuotient, mem_eval_activeImage D H generic T valid U _ hU terms,
    mem_equivalenceClasses]
  constructor
  · rintro ⟨w, hw, active, equal⟩
    exact ⟨eval {p | H.mem p} w, active, equal.symm.trans (value w hw)⟩
  · rintro ⟨x, hx, equal⟩
    obtain ⟨w, hw, rfl⟩ :=
      (mem_eval_familySet {p | H.mem p} ⊤ H.top_mem T valid x).1 (subset hx)
    exact ⟨w, hw, hx, (value w hw).trans equal.symm⟩

theorem eval_refinementNaturalMap (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D))
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (U Rf Rc : Name s)
    (hU : U ∈ D.names) (hRf : Rf ∈ D.names) (hRc : Rc ∈ D.names)
    (terms : ∀ w : Name s, w.val ∈ T → w ∈ D.names)
    (pairs : ∀ z w : Name s, z.val ∈ T → w.val ∈ T → orderedPair ⊤ z w ∈ D.names)
    (subset : eval {p | H.mem p} U ⊆ eval {p | H.mem p} (familySet ⊤ T valid))
    (fine : eval {p | H.mem p} Rf ⊆ ZFSet.prod (eval {p | H.mem p} U) (eval {p | H.mem p} U))
    (coarse : eval {p | H.mem p} Rc ⊆ ZFSet.prod (eval {p | H.mem p} U) (eval {p | H.mem p} U)) :
    eval {p | H.mem p} (refinementNaturalMap T valid U Rf Rc) =
      refinementQuotientMap (eval {p | H.mem p} U) (eval {p | H.mem p} Rf) (eval {p | H.mem p} Rc) := by
  have value (w : Name s) (hw : w.val ∈ T) :
      eval {p | H.mem p} (orderedPair ⊤ (refinementClass T valid Rf w) (refinementClass T valid Rc w)) =
      ZFSet.pair (equivalenceClass (eval {p | H.mem p} U) (eval {p | H.mem p} Rf) (eval {p | H.mem p} w))
        (equivalenceClass (eval {p | H.mem p} U) (eval {p | H.mem p} Rc) (eval {p | H.mem p} w)) := by
    rw [eval_orderedPair {p | H.mem p} ⊤ H.top_mem,
      eval_refinementClass D H generic T valid Rf w hRf (fun z hz => pairs z w hz hw),
      eval_refinementClass D H generic T valid Rc w hRc (fun z hz => pairs z w hz hw),
      equivalenceClass_eq_of_carrier_subset subset fine,
      equivalenceClass_eq_of_carrier_subset subset coarse]
  apply ZFSet.ext
  intro z
  rw [refinementNaturalMap, mem_eval_activeImage D H generic T valid U _ hU terms,
    mem_refinementQuotientMap]
  constructor
  · rintro ⟨w, hw, active, equal⟩
    exact ⟨eval {p | H.mem p} w, active, equal.symm.trans (value w hw)⟩
  · rintro ⟨x, hx, equal⟩
    obtain ⟨w, hw, rfl⟩ :=
      (mem_eval_familySet {p | H.mem p} ⊤ H.top_mem T valid x).1 (subset hx)
    exact ⟨w, hw, hx, (value w hw).trans equal.symm⟩

end Name

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}
variable {G : Type v} [Group G] (a : PosetAction G P)
variable (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
include closed

theorem act_refinementQuotient (g : G) (U R : Name s) :
    a.act s g (refinementQuotient T valid U R) =
      refinementQuotient T valid (a.act s g U) (a.act s g R) := by
  apply act_activeImage a T valid closed g U
  intro w _
  exact act_refinementClass a T valid closed g R w

theorem act_refinementNaturalMap (g : G) (U Rf Rc : Name s) :
    a.act s g (refinementNaturalMap T valid U Rf Rc) =
      refinementNaturalMap T valid (a.act s g U) (a.act s g Rf) (a.act s g Rc) := by
  apply act_activeImage a T valid closed g U
  intro w _
  change rename s (a.iso g) (orderedPair ⊤ _ _) = _
  rw [rename_orderedPair, (a.iso g).map_top]
  change orderedPair ⊤ (a.act s g (refinementClass T valid Rf w))
    (a.act s g (refinementClass T valid Rc w)) = _
  rw [act_refinementClass a T valid closed, act_refinementClass a T valid closed]

theorem refinementQuotient_support (U R : Name s) (K : Subgroup G)
    (activity : K ≤ a.stabilizer s U) (relation : K ≤ a.stabilizer s R) :
    K ≤ a.stabilizer s (refinementQuotient T valid U R) := by
  intro g hg
  change a.act s g _ = _
  rw [act_refinementQuotient a T valid closed, activity hg, relation hg]

theorem refinementNaturalMap_support (U Rf Rc : Name s) (K : Subgroup G)
    (activity : K ≤ a.stabilizer s U) (fine : K ≤ a.stabilizer s Rf)
    (coarse : K ≤ a.stabilizer s Rc) :
    K ≤ a.stabilizer s (refinementNaturalMap T valid U Rf Rc) := by
  intro g hg
  change a.act s g _ = _
  rw [act_refinementNaturalMap a T valid closed, activity hg, fine hg, coarse hg]

theorem refinementClass_hs_of_hs (F : NormalSubgroupFamily G)
    (children : ∀ w : Name s, w.val ∈ T → HereditarilySymmetric a s F w)
    (R w : Name s) (relation : HereditarilySymmetric a s F R)
    (representative : HereditarilySymmetric a s F w) :
    HereditarilySymmetric a s F (refinementClass T valid R w) :=
  refinementClass_hs a F T valid closed children R w
    (a.stabilizer s R ⊓ a.stabilizer s w) (F.inf relation.symmetric representative.symmetric)
    (fun _ hg => hg.1) (fun _ hg => hg.2)

theorem refinementQuotient_hs (F : NormalSubgroupFamily G)
    (children : ∀ w : Name s, w.val ∈ T → HereditarilySymmetric a s F w)
    (U R : Name s) (activity : HereditarilySymmetric a s F U)
    (relation : HereditarilySymmetric a s F R) :
    HereditarilySymmetric a s F (refinementQuotient T valid U R) := by
  refine HereditarilySymmetric.mk
    (F.upward (F.inf activity.symmetric relation.symmetric)
      (refinementQuotient_support a T valid closed U R
        (a.stabilizer s U ⊓ a.stabilizer s R) (fun _ hg => hg.1) (fun _ hg => hg.2))) ?_
  intro σ p entry
  obtain ⟨w, hw, _, rfl⟩ := (entry_refinementQuotient T valid U R σ p).1 entry
  exact refinementClass_hs_of_hs a T valid closed F children R w relation (children w hw)

theorem refinementNaturalMap_hs (F : NormalSubgroupFamily G)
    (children : ∀ w : Name s, w.val ∈ T → HereditarilySymmetric a s F w)
    (U Rf Rc : Name s) (activity : HereditarilySymmetric a s F U)
    (fine : HereditarilySymmetric a s F Rf) (coarse : HereditarilySymmetric a s F Rc) :
    HereditarilySymmetric a s F (refinementNaturalMap T valid U Rf Rc) := by
  refine HereditarilySymmetric.mk
    (F.upward (F.inf activity.symmetric (F.inf fine.symmetric coarse.symmetric))
      (refinementNaturalMap_support a T valid closed U Rf Rc
        (a.stabilizer s U ⊓ (a.stabilizer s Rf ⊓ a.stabilizer s Rc))
        (fun _ hg => hg.1) (fun _ hg => hg.2.1) (fun _ hg => hg.2.2))) ?_
  intro σ p entry
  obtain ⟨w, hw, _, rfl⟩ := (entry_refinementNaturalMap T valid U Rf Rc σ p).1 entry
  exact (refinementClass_hs_of_hs a T valid closed F children Rf w fine (children w hw)).orderedPair
    (refinementClass_hs_of_hs a T valid closed F children Rc w coarse (children w hw))

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include pairing unions powers separation collection carrier order in
theorem refinementQuotient_mem {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U R : Name s)
    (hU : U.val ∈ M.sets) (hR : R.val ∈ M.sets) :
    (Name.refinementQuotient T valid U R).val ∈ M.sets :=
  M.activeImage_mem s pairing unions powers separation collection carrier order hT valid U hU
    (Name.refinementClass T valid R) (Name.refinementClassGraph T valid R T valid)
    (M.refinementClassGraph_mem s pairing unions powers separation collection carrier order
      hT hT valid valid R hR)
    (Name.pair_mem_refinementClassGraph T valid R T valid)

include pairing unions powers separation collection carrier order in
theorem refinementNaturalMap_mem {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U Rf Rc : Name s)
    (hU : U.val ∈ M.sets) (hRf : Rf.val ∈ M.sets) (hRc : Rc.val ∈ M.sets) :
    (Name.refinementNaturalMap T valid U Rf Rc).val ∈ M.sets :=
  M.activeImage_mem s pairing unions powers separation collection carrier order hT valid U hU
    (fun w => Name.orderedPair ⊤ (Name.refinementClass T valid Rf w) (Name.refinementClass T valid Rc w))
    (Name.refinementPairClassGraph T valid Rf Rc T valid)
    (M.refinementPairClassGraph_mem s pairing unions powers separation collection carrier order
      hT hT valid valid Rf Rc hRf hRc)
    (Name.pair_mem_refinementPairClassGraph T valid Rf Rc T valid)

end TransitiveGround
end PartitionPilot.Forcing

end OAI
