import OAI.SetTheory.PartitionPrinciple.Definability.GroundAssignmentClassGraphs
import OAI.SetTheory.PartitionPrinciple.Definability.GroundQuantifiedGraphFormulas
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRowAssignmentCuts
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStageOneAssignmentUnions

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace SetFormula

def stageOneForcingFormula {n : Nat} (phi : SetFormula n) : SetFormula (n + 3) :=
  forcingTranslation (ordinaryGroundPrimitives (0 : Fin 2) 1) phi
    (extend 1 (extend 2 Fin.elim0)) 0 (fun j => j.succ.succ.succ)

def stageOneForcingAt {n m : Nat} (phi : SetFormula m) (p P r : Fin n)
    (names : Fin m → Fin n) : SetFormula n :=
  reindex (extend p (extend P (extend r names))) (stageOneForcingFormula phi)

def stageOneClassAt {n : Nat} (c T R w P r top : Fin n) : SetFormula n :=
  reindex (extend c (extend T (extend R (extend w
    (extend P (extend r (extend top Fin.elim0))))))) refinementClassCodeFormula

end SetFormula

def stageOneRawForces (M : TransitiveGround.{u}) (P r p : ZFSet.{u})
    {n : Nat} (phi : SetFormula n) (names : Fin n → ZFSet.{u}) : Prop :=
  Realize M.sets (stageOneForcingFormula phi) (extend p (extend P (extend r names)))

def stageOneRawClass (M : TransitiveGround.{u}) (T P r top R w c : ZFSet.{u}) : Prop :=
  Realize M.sets refinementClassCodeFormula
    (extend c (extend T (extend R (extend w (extend P (extend r (extend top Fin.elim0)))))))

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_stageOneForcingAt {n m : Nat} (phi : SetFormula m) (p P r : Fin n)
    (names : Fin m → Fin n) (env : Fin n → ZFSet.{u}) :
    Realize M.sets (stageOneForcingAt phi p P r names) env ↔
      stageOneRawForces M (env P) (env r) (env p) phi (fun j => env (names j)) := by
  rw [stageOneForcingAt, realize_reindex, map_extend, map_extend, map_extend]
  rfl

theorem realize_stageOneClassAt {n : Nat} (c T R w P r top : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Realize M.sets (stageOneClassAt c T R w P r top) env ↔
      stageOneRawClass M (env T) (env P) (env r) (env top) (env R) (env w) (env c) := by
  rw [stageOneClassAt, stageOneRawClass, realize_reindex]
  simp only [map_extend]
  have empty : (fun j : Fin 0 => env (Fin.elim0 j)) = Fin.elim0 := funext (fun j => Fin.elim0 j)
  rw [empty]

theorem stageOneRawForces_iff {P : Type u} [Preorder P] (s : Presentation P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {n : Nat} (phi : SetFormula n) (p : P) (names : Assignment (M.nameDomain s) n) :
    stageOneRawForces M s.carrier s.conditionOrder (s.encode p) phi
      (fun j => (names j).val.val) ↔ Forces (M.nameDomain s) phi names p := by
  exact M.realize_ordinaryGroundForcing s pairing unions powers separation collection carrier order
    (0 : Fin 2) 1 phi (extend 1 (extend 2 Fin.elim0)) 0 (fun j => j.succ.succ.succ)
    _ rfl rfl p names rfl (fun _ => rfl)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

def PreparationForcingCode (M : TransitiveGround.{u})
    (P order q nodes visibility z F f : ZFSet.{u}) : Prop :=
  (∀ v V, ZFSet.pair v V ∈ visibility → v ∈ nodes →
    (v ∈ F → stageOneRawForces M P order q (.mem 0 1 : SetFormula 2) ![z, V]) ∧
    (v ∉ F → stageOneRawForces M P order q (.neg (.mem 0 1) : SetFormula 2) ![z, V])) ∧
  ∀ v tau, ZFSet.pair v tau ∈ f →
    stageOneRawForces M P order q (.equal 0 1 : SetFormula 2) ![z, tau]

namespace SetFormula

def preparationForcingFormula {n} (P order q nodes visibility z F f : Fin n) : SetFormula n :=
  .conj
    (allGraphFields visibility
      (imp (.mem 1 nodes.succ.succ)
        (.conj
          (imp (.mem 1 F.succ.succ)
            (stageOneForcingAt (.mem 0 1 : SetFormula 2) q.succ.succ P.succ.succ
              order.succ.succ ![z.succ.succ, 0]))
          (imp (.neg (.mem 1 F.succ.succ))
            (stageOneForcingAt (.neg (.mem 0 1) : SetFormula 2) q.succ.succ P.succ.succ
              order.succ.succ ![z.succ.succ, 0])))))
    (allGraphFields f
      (stageOneForcingAt (.equal 0 1 : SetFormula 2) q.succ.succ P.succ.succ
        order.succ.succ ![z.succ.succ, 0]))

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_preparationForcingFormula {n} (P order q nodes visibility z F f : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (preparationForcingFormula P order q nodes visibility z F f) env ↔
      PreparationForcingCode M (env P) (env order) (env q) (env nodes)
        (env visibility) (env z) (env F) (env f) := by
  rw [preparationForcingFormula, Realize, M.realize_allGraphFields _ _ env members,
    M.realize_allGraphFields _ _ env members]
  simp only [realize_imp, Realize, M.realize_stageOneForcingAt]
  have names (x y : ZFSet.{u}) :
      (fun j : Fin 2 => extend y (extend x env) (![z.succ.succ, 0] j)) = ![env z, y] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)) j
  simp only [names]
  rfl

end TransitiveGround

end PartitionPilot.Forcing


section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include pairing unions powers separation collection carrier order

theorem stageOneRawForces_condition_mono {n : Nat} (phi : SetFormula n)
    (names : Assignment (M.nameDomain s) n) {p q : P} (qp : q ≤ p)
    (forced : stageOneRawForces M s.carrier s.conditionOrder (s.encode p) phi
      (fun j => (names j).val.val)) :
    stageOneRawForces M s.carrier s.conditionOrder (s.encode q) phi
      (fun j => (names j).val.val) := by
  apply (M.stageOneRawForces_iff s pairing unions powers separation collection
    carrier order phi q names).2
  exact forces_mono (M.nameDomain s) phi names
    ((M.stageOneRawForces_iff s pairing unions powers separation collection
      carrier order phi p names).1 forced) qp

private theorem rawForces_pair_condition_mono
    (phi : SetFormula 2) (z tau : (M.nameDomain s).names) {p q : P} (qp : q ≤ p)
    (forced : stageOneRawForces M s.carrier s.conditionOrder (s.encode p) phi
      ![z.val.val, tau.val.val]) :
    stageOneRawForces M s.carrier s.conditionOrder (s.encode q) phi
      ![z.val.val, tau.val.val] := by
  have fields : (fun j : Fin 2 => (![z, tau] j).val.val) =
      ![z.val.val, tau.val.val] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)) j
  have moved := M.stageOneRawForces_condition_mono s pairing unions powers separation
    collection carrier order phi ![z, tau] qp
  rw [fields] at moved
  exact moved forced

theorem preparationForcingCode_condition_mono
    (nodes N visibility : ZFSet.{u})
    (graphGround : visibility ∈ M.sets)
    (graphNames : ∀ v V, ZFSet.pair v V ∈ visibility → v ∈ nodes → IsName s V)
    (namesGround : N ∈ M.sets) (validN : ∀ tau ∈ N, IsName s tau)
    (z : (M.nameDomain s).names) (F f : ZFSet.{u})
    (range : f ⊆ ZFSet.prod nodes N) {p q : P} (qp : q ≤ p)
    (code : PreparationForcingCode M s.carrier s.conditionOrder (s.encode p)
      nodes visibility z.val.val F f) :
    PreparationForcingCode M s.carrier s.conditionOrder (s.encode q)
      nodes visibility z.val.val F f := by
  constructor
  · intro v V entry member
    let name : (M.nameDomain s).names :=
      ⟨⟨V, graphNames v V entry member⟩, M.pair_right (M.transitive graphGround entry)⟩
    have decisions := code.1 v V entry member
    exact ⟨fun yes => rawForces_pair_condition_mono M s pairing unions powers separation
      collection carrier order (.mem 0 1) z name qp (decisions.1 yes),
      fun no => rawForces_pair_condition_mono M s pairing unions powers separation
        collection carrier order (.neg (.mem 0 1)) z name qp (decisions.2 no)⟩
  · intro v tau entry
    have htau := (ZFSet.pair_mem_prod.1 (range entry)).2
    let name : (M.nameDomain s).names :=
      ⟨⟨tau, validN tau htau⟩, M.transitive namesGround htau⟩
    exact rawForces_pair_condition_mono M s pairing unions powers separation collection
      carrier order (.equal 0 1) z name qp (code.2 v tau entry)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]

theorem preparationForcingCode_nice_condition_mono
    (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
    (T : ZFSet.{u}) (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (N : ZFSet.{u}) (graphGround : M.niceVisibilityGraph a s b T K ∈ M.sets)
    (namesGround : N ∈ M.sets) (validN : ∀ tau ∈ N, IsName s tau)
    (z : (M.nameDomain s).names) (F f : ZFSet.{u})
    (range : f ⊆ ZFSet.prod b.carrier N) {p q : P} (qp : q ≤ p)
    (code : PreparationForcingCode M s.carrier s.conditionOrder (s.encode p)
      b.carrier (M.niceVisibilityGraph a s b T K) z.val.val F f) :
    PreparationForcingCode M s.carrier s.conditionOrder (s.encode q)
      b.carrier (M.niceVisibilityGraph a s b T K) z.val.val F f := by
  apply M.preparationForcingCode_condition_mono s pairing unions powers separation collection
    carrier order b.carrier N (M.niceVisibilityGraph a s b T K) graphGround
    _ namesGround validN z F f range qp code
  intro v V entry member
  obtain ⟨i, rfl⟩ := (b.mem_carrier v).1 member
  rw [(M.pair_mem_niceVisibilityGraph a s b T K i V).1 entry]
  exact (M.niceVisibilityName a s T (K i)).property

end PartitionPilot.Forcing.TransitiveGround

end



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

private def representedReuseFormula {n : Nat}
    (A q P order T idx cu classes : Fin n) : SetFormula n :=
  let old := suffixIndex n 3
  let v := prefixIndex n 3
  exBlock 3 (.conj (.mem (v 0) (old T))
    (.conj (.mem (v 1) (old T))
      (.conj (tripleMembershipFormula (old idx) (v 0) (v 1) (old A))
        (.conj (pairMembershipFormula (v 0) (v 2) (old classes))
          (stageOneForcingAt (.equal 0 1 : SetFormula 2) (old q) (old P)
            (old order) ![old cu, v 2])))))

private theorem realize_representedReuseFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (A q P order T idx cu classes : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (representedReuseFormula A q P order T idx cu classes) env ↔
      ∃ v ∈ env T, ∃ w ∈ env T, ∃ z,
        stageOneAssignment (env idx) v w ∈ env A ∧
        ZFSet.pair v z ∈ env classes ∧
        stageOneRawForces M (env P) (env order) (env q)
          (.equal 0 1 : SetFormula 2) ![env cu, z] := by
  rw [representedReuseFormula, realize_exBlock]
  have actual (f : Fin 3 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (.conj (.mem (prefixIndex n 3 0) (suffixIndex n 3 T))
        (.conj (.mem (prefixIndex n 3 1) (suffixIndex n 3 T))
          (.conj (tripleMembershipFormula (suffixIndex n 3 idx) (prefixIndex n 3 0)
            (prefixIndex n 3 1) (suffixIndex n 3 A))
            (.conj (pairMembershipFormula (prefixIndex n 3 0) (prefixIndex n 3 2)
              (suffixIndex n 3 classes))
              (stageOneForcingAt (.equal 0 1 : SetFormula 2) (suffixIndex n 3 q)
                (suffixIndex n 3 P) (suffixIndex n 3 order)
                ![suffixIndex n 3 cu, prefixIndex n 3 2]))))) (extendMany 3 f env) ↔
      f 0 ∈ env T ∧ f 1 ∈ env T ∧
      stageOneAssignment (env idx) (f 0) (f 1) ∈ env A ∧
      ZFSet.pair (f 0) (f 2) ∈ env classes ∧
      stageOneRawForces M (env P) (env order) (env q)
        (.equal 0 1 : SetFormula 2) ![env cu, f 2] := by
    have allGround := extendMany_members 3 f env ground members
    simp only [Realize]
    rw [M.realize_tripleMembershipFormula pairing _ _ _ _ _
      (allGround _) (allGround _) (allGround _) (allGround _),
      M.realize_pairMembershipFormula pairing _ _ _ _ (allGround _) (allGround _) (allGround _),
      M.realize_stageOneForcingAt]
    have values (x y : Fin (n + 3)) :
        (fun j : Fin 2 => extendMany 3 f env (![x, y] j)) =
          ![extendMany 3 f env x, extendMany 3 f env y] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) j
    rw [values]
    simp only [extendMany_prefix, extendMany_suffix, stageOneAssignment]
  constructor
  · rintro ⟨f, ground, body⟩
    obtain ⟨hv, hw, literal, entry, forced⟩ := (actual f ground).1 body
    exact ⟨f 0, hv, f 1, hw, f 2, literal, entry, forced⟩
  · rintro ⟨v, hv, w, hw, z, literal, entry, forced⟩
    have ground : ∀ j, (![v, w, z] : Fin 3 → ZFSet.{u}) j ∈ M.sets :=
      Fin.cases (M.transitive (members T) hv) (Fin.cases (M.transitive (members T) hw)
        (Fin.cases (M.pair_right (M.transitive (members classes) entry)) (fun j => Fin.elim0 j)))
    exact ⟨![v, w, z], ground, (actual ![v, w, z] ground).2 ⟨hv, hw, literal, entry, forced⟩⟩

private def representedEntryFormula {n : Nat}
    (p P order cut T idx u U cu classes : Fin n) : SetFormula n :=
  let old := suffixIndex n 3
  let v := prefixIndex n 3
  exBlock 3 (.conj (BoundedFormula.orderedPairFormula (old p) (v 0) (v 1)).toFormula
    (.conj (pairMembershipFormula (old p) (v 2) (old cut))
      (disj (stageOneForcingAt (.neg (.mem 0 1) : SetFormula 2) (v 2) (old P)
        (old order) ![old u, old U])
        (.conj (stageOneForcingAt (.mem 0 1 : SetFormula 2) (v 2) (old P)
          (old order) ![old u, old U])
          (representedReuseFormula (v 1) (v 2) (old P) (old order) (old T)
            (old idx) (old cu) (old classes))))))

private theorem realize_representedEntryFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (p P order cut T idx u U cu classes : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (representedEntryFormula p P order cut T idx u U cu classes) env ↔
      ∃ row A q, env p = ZFSet.pair row A ∧ ZFSet.pair (env p) q ∈ env cut ∧
        (stageOneRawForces M (env P) (env order) q
          (.neg (.mem 0 1) : SetFormula 2) ![env u, env U] ∨
        (stageOneRawForces M (env P) (env order) q (.mem 0 1 : SetFormula 2) ![env u, env U] ∧
          ∃ v ∈ env T, ∃ w ∈ env T, ∃ z,
            stageOneAssignment (env idx) v w ∈ A ∧ ZFSet.pair v z ∈ env classes ∧
            stageOneRawForces M (env P) (env order) q
              (.equal 0 1 : SetFormula 2) ![env cu, z])) := by
  rw [representedEntryFormula, realize_exBlock]
  have actual (f : Fin 3 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (.conj (BoundedFormula.orderedPairFormula (suffixIndex n 3 p)
        (prefixIndex n 3 0) (prefixIndex n 3 1)).toFormula
        (.conj (pairMembershipFormula (suffixIndex n 3 p) (prefixIndex n 3 2) (suffixIndex n 3 cut))
          (disj (stageOneForcingAt (.neg (.mem 0 1) : SetFormula 2) (prefixIndex n 3 2)
            (suffixIndex n 3 P) (suffixIndex n 3 order) ![suffixIndex n 3 u, suffixIndex n 3 U])
            (.conj (stageOneForcingAt (.mem 0 1 : SetFormula 2) (prefixIndex n 3 2)
              (suffixIndex n 3 P) (suffixIndex n 3 order) ![suffixIndex n 3 u, suffixIndex n 3 U])
              (representedReuseFormula (prefixIndex n 3 1) (prefixIndex n 3 2)
                (suffixIndex n 3 P) (suffixIndex n 3 order) (suffixIndex n 3 T)
                (suffixIndex n 3 idx) (suffixIndex n 3 cu) (suffixIndex n 3 classes))))))
        (extendMany 3 f env) ↔
      env p = ZFSet.pair (f 0) (f 1) ∧ ZFSet.pair (env p) (f 2) ∈ env cut ∧
        (stageOneRawForces M (env P) (env order) (f 2)
          (.neg (.mem 0 1) : SetFormula 2) ![env u, env U] ∨
        (stageOneRawForces M (env P) (env order) (f 2) (.mem 0 1 : SetFormula 2) ![env u, env U] ∧
          ∃ v ∈ env T, ∃ w ∈ env T, ∃ z,
            stageOneAssignment (env idx) v w ∈ f 1 ∧ ZFSet.pair v z ∈ env classes ∧
            stageOneRawForces M (env P) (env order) (f 2)
              (.equal 0 1 : SetFormula 2) ![env cu, z])) := by
    have allGround := extendMany_members 3 f env ground members
    rw [Realize, BoundedFormula.realize_toFormula M _ _ allGround,
      BoundedFormula.truth_orderedPairFormula, Realize,
      M.realize_pairMembershipFormula pairing _ _ _ _ (allGround _) (allGround _) (allGround _),
      realize_disj, M.realize_stageOneForcingAt, Realize, M.realize_stageOneForcingAt,
      realize_representedReuseFormula M pairing _ _ _ _ _ _ _ _ _ allGround]
    have values (x y : Fin (n + 3)) :
        (fun j : Fin 2 => extendMany 3 f env (![x, y] j)) =
          ![extendMany 3 f env x, extendMany 3 f env y] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) j
    rw [values]
    simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, body⟩
    exact ⟨f 0, f 1, f 2, (actual f ground).1 body⟩
  · rintro ⟨row, A, q, shape, cutEntry, code⟩
    have ground : ∀ j, (![row, A, q] : Fin 3 → ZFSet.{u}) j ∈ M.sets :=
      Fin.cases (M.pair_left (shape ▸ members p)) (Fin.cases (M.pair_right (shape ▸ members p))
        (Fin.cases (M.pair_right (M.transitive (members cut) cutEntry)) (fun j => Fin.elim0 j)))
    exact ⟨![row, A, q], ground, (actual ![row, A, q] ground).2 ⟨shape, cutEntry, code⟩⟩

variable {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)

noncomputable def representedDomainConditions (upper levels alpha T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (idx : ZFSet.{u}) (U Rc u : (M.nameDomain s).names) : ZFSet.{u} :=
  let cut := rowAssignmentCutGraph upper s.carrier levels alpha
  let classes := Name.refinementClassGraph T valid Rc.val T valid
  let cu := (Name.refinementClass T valid Rc.val u.val).val
  let params : Fin 9 → ZFSet.{u} := ![s.carrier, s.conditionOrder, cut, T, idx, u.val.val, U.val.val, cu, classes]
  ZFSet.sep (fun p => Realize M.sets (representedEntryFormula 0 1 2 3 4 5 6 7 8 9)
    (extend p params)) upper

theorem representedDomainConditions_subset (upper levels alpha T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (idx : ZFSet.{u}) (U Rc u : (M.nameDomain s).names) :
    M.representedDomainConditions s upper levels alpha T valid idx U Rc u ⊆ upper :=
by
  intro z member
  rw [representedDomainConditions, ZFSet.mem_sep] at member
  exact member.1

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include pairing unions powers separation collection carrier order in
private theorem representedParams_ground {upper levels alpha T : ZFSet.{u}}
    (hUpper : upper ∈ M.sets) (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) {idx : ZFSet.{u}} (hIdx : idx ∈ M.sets)
    (U Rc u : (M.nameDomain s).names) :
    ∀ j, (![s.carrier, s.conditionOrder, rowAssignmentCutGraph upper s.carrier levels alpha,
      T, idx, u.val.val, U.val.val, (Name.refinementClass T valid Rc.val u.val).val,
      Name.refinementClassGraph T valid Rc.val T valid] : Fin 9 → ZFSet.{u}) j ∈ M.sets :=
  Fin.cases carrier (Fin.cases order
    (Fin.cases (M.rowAssignmentCutGraph_mem pairing unions powers separation hUpper carrier hLevels hAlpha)
      (Fin.cases hT (Fin.cases hIdx (Fin.cases u.property (Fin.cases U.property
        (Fin.cases (M.refinementClass_mem s pairing unions powers separation collection carrier order
          hT valid Rc.val u.val Rc.property u.property)
          (Fin.cases (M.refinementClassGraph_mem s pairing unions powers separation collection carrier order
            hT hT valid valid Rc.val Rc.property) (fun j => Fin.elim0 j)))))))))

include pairing unions powers separation collection carrier order in
theorem representedDomainConditions_mem {upper levels alpha T : ZFSet.{u}}
    (hUpper : upper ∈ M.sets) (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) {idx : ZFSet.{u}} (hIdx : idx ∈ M.sets)
    (U Rc u : (M.nameDomain s).names) :
    M.representedDomainConditions s upper levels alpha T valid idx U Rc u ∈ M.sets :=
  M.separation_mem separation (representedEntryFormula 0 1 2 3 4 5 6 7 8 9) _
    (representedParams_ground M s pairing unions powers separation collection carrier order
      hUpper hLevels hAlpha hT valid hIdx U Rc u) hUpper

include pairing unions powers separation collection carrier order in
theorem pair_mem_representedDomainConditions {upper levels alpha T : ZFSet.{u}}
    (hUpper : upper ∈ M.sets) (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) {idx : ZFSet.{u}} (hIdx : idx ∈ M.sets)
    (U Rc u : (M.nameDomain s).names) (row A : ZFSet.{u}) (q : P)
    (cut : s.encode q = ZFSet.pair row (assignmentCut levels alpha A)) :
    ZFSet.pair row A ∈ M.representedDomainConditions s upper levels alpha T valid idx U Rc u ↔
      ZFSet.pair row A ∈ upper ∧
      ((∀ r : P, r ≤ q → ¬ Name.ForcesMem r u.val U.val) ∨
        (Name.ForcesMem q u.val U.val ∧ ∃ v w : Name s,
          v.val ∈ T ∧ w.val ∈ T ∧ stageOneAssignment idx v.val w.val ∈ A ∧
          Name.ForcesEq q (Name.refinementClass T valid Rc.val u.val)
            (Name.refinementClass T valid Rc.val v))) := by
  let params : Fin 9 → ZFSet.{u} := ![s.carrier, s.conditionOrder,
    rowAssignmentCutGraph upper s.carrier levels alpha, T, idx, u.val.val, U.val.val,
    (Name.refinementClass T valid Rc.val u.val).val, Name.refinementClassGraph T valid Rc.val T valid]
  have paramsGround := representedParams_ground M s pairing unions powers separation collection carrier order
    hUpper hLevels hAlpha hT valid hIdx U Rc u
  have raw (phi : SetFormula 2) (x y : (M.nameDomain s).names) :
      stageOneRawForces M s.carrier s.conditionOrder (s.encode q) phi ![x.val.val, y.val.val] ↔
        Forces (M.nameDomain s) phi ![x, y] q := by
    have fields : (fun j : Fin 2 => (![x, y] j).val.val) = ![x.val.val, y.val.val] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) j
    have result := M.stageOneRawForces_iff s pairing unions powers separation collection carrier order phi q ![x, y]
    rw [fields] at result
    exact result
  let className (v : (M.nameDomain s).names) : (M.nameDomain s).names :=
    ⟨Name.refinementClass T valid Rc.val v.val,
      M.refinementClass_mem s pairing unions powers separation collection carrier order hT valid
        Rc.val v.val Rc.property v.property⟩
  rw [representedDomainConditions, ZFSet.mem_sep]
  change (ZFSet.pair row A ∈ upper ∧ Realize M.sets (representedEntryFormula 0 1 2 3 4 5 6 7 8 9)
    (extend (ZFSet.pair row A) params)) ↔ _
  apply and_congr_right
  intro member
  rw [realize_representedEntryFormula M pairing _ _ _ _ _ _ _ _ _ _ _
    (Fin.cases (M.transitive hUpper member) paramsGround)]
  change (∃ row' A' q', ZFSet.pair row A = ZFSet.pair row' A' ∧
    ZFSet.pair (ZFSet.pair row A) q' ∈ rowAssignmentCutGraph upper s.carrier levels alpha ∧
    (stageOneRawForces M s.carrier s.conditionOrder q' (.neg (.mem 0 1) : SetFormula 2) ![u.val.val, U.val.val] ∨
      (stageOneRawForces M s.carrier s.conditionOrder q' (.mem 0 1 : SetFormula 2) ![u.val.val, U.val.val] ∧
        ∃ v ∈ T, ∃ w ∈ T, ∃ z, stageOneAssignment idx v w ∈ A' ∧
          ZFSet.pair v z ∈ Name.refinementClassGraph T valid Rc.val T valid ∧
          stageOneRawForces M s.carrier s.conditionOrder q' (.equal 0 1 : SetFormula 2)
            ![(className u).val.val, z]))) ↔ _
  constructor
  · rintro ⟨row', A', q', same, entry, branch⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 same
    have equal := ((pair_mem_rowAssignmentCutGraph upper s.carrier levels alpha row A q').1 entry).2.2
    have eq : q' = s.encode q := equal.trans cut.symm
    rw [eq] at branch
    rcases branch with inactive | ⟨active, v, hv, w, hw, z, literal, classEntry, equal⟩
    · exact Or.inl ((raw (.neg (.mem 0 1)) u U).1 inactive)
    · let vName : (M.nameDomain s).names := ⟨⟨v, valid v hv⟩, M.transitive hT hv⟩
      have classEqual := (Name.pair_mem_refinementClassGraph T valid Rc.val T valid vName.val z).1 classEntry |>.2
      rw [classEqual] at equal
      exact Or.inr ⟨(raw (.mem 0 1) u U).1 active, vName.val, ⟨w, valid w hw⟩,
        hv, hw, literal, (raw (.equal 0 1) (className u) (className vName)).1 equal⟩
  · intro branch
    refine ⟨row, A, s.encode q, rfl,
      (pair_mem_rowAssignmentCutGraph upper s.carrier levels alpha row A (s.encode q)).2
        ⟨member, s.encode_mem q, cut⟩, ?_⟩
    rcases branch with inactive | ⟨active, v, w, hv, hw, literal, equal⟩
    · exact Or.inl ((raw (.neg (.mem 0 1)) u U).2 inactive)
    · let vName : (M.nameDomain s).names := ⟨v, M.transitive hT hv⟩
      exact Or.inr ⟨(raw (.mem 0 1) u U).2 active, v.val, hv, w.val, hw,
        (className vName).val.val, literal,
        (Name.pair_mem_refinementClassGraph T valid Rc.val T valid v _).2 ⟨hv, rfl⟩,
        (raw (.equal 0 1) (className u) (className vName)).2 equal⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
