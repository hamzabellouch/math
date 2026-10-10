import OAI.SetTheory.PartitionPrinciple.Models.GroundRefinementQuotientNames

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace SetFormula

def refinementClassCodeFormula : SetFormula 7 :=
  exactSetFormula 0 (reindex (extend 0 (fun j : Fin 6 => j.succ.succ)) refinementClassEntryFormula)

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)

theorem realize_refinementClassCodeFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (R w : Name s) (hR : R.val ∈ M.sets) (hw : w.val ∈ M.sets)
    (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets refinementClassCodeFormula
      (extend z (extend T (extend R.val (extend w.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0))))))) ↔
      z = (Name.refinementClass T valid R w).val := by
  have ground := M.refinementClass_mem s pairing unions powers separation collection carrier order hT valid R w hR hw
  apply M.realize_exactSetFormula 0 _ _ hz (fun _ h => M.transitive ground h)
  intro x hx
  rw [realize_reindex, map_extend]
  exact M.realize_refinementClassEntryFormula s pairing unions powers separation collection
    carrier order hT valid R w hR hw x hx

end TransitiveGround

private def assignmentClassGraphFormula (side : Fin 2) : SetFormula 7 :=
  let w := prefixIndex 7 6
  let old := suffixIndex 7 6
  let representative := Fin.cases (w 3) (fun _ => w 4) side
  exBlock 6 (.conj (.mem (w 0) (old 1))
    (.conj (BoundedFormula.orderedPairFormula (old 0) (w 0) (w 1)).toFormula
      (.conj (BoundedFormula.stageOneAssignmentFormula (w 0) (w 2) (w 3) (w 4)).toFormula
        (.conj (BoundedFormula.pairMembershipFormula (w 2) (w 5) (old 2)).toFormula
          (reindex ![w 1, old 3, w 5, representative, old 4, old 5, old 6]
            refinementClassCodeFormula)))))

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def assignmentClassGraph (side : Fin 2)
    (A field T P order top : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => Realize M.sets (assignmentClassGraphFormula side)
    (extend z ![A, field, T, P, order, top])) (ZFSet.prod A (M.groundRelations T P))

theorem assignmentClassGraph_mem (side : Fin 2)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A field T P order top : ZFSet.{u}}
    (hA : A ∈ M.sets) (hField : field ∈ M.sets) (hT : T ∈ M.sets)
    (hP : P ∈ M.sets) (hOrder : order ∈ M.sets) (hTop : top ∈ M.sets) :
    M.assignmentClassGraph side A field T P order top ∈ M.sets :=
  M.separation_mem separation (assignmentClassGraphFormula side) _
    (Fin.cases hA (Fin.cases hField (Fin.cases hT (Fin.cases hP
      (Fin.cases hOrder (Fin.cases hTop (fun j => Fin.elim0 j)))))))
    (M.prod_mem pairing unions powers separation hA
      (M.groundRelations_mem pairing unions powers separation hT hP))

private theorem realize_assignmentClassGraphFormula (side : Fin 2)
    (env : Fin 7 → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (assignmentClassGraphFormula side) env ↔
      ∃ w : Fin 6 → ZFSet.{u}, (∀ j, w j ∈ M.sets) ∧
        w 0 ∈ env 1 ∧ env 0 = ZFSet.pair (w 0) (w 1) ∧
        w 0 = stageOneAssignment (w 2) (w 3) (w 4) ∧
        ZFSet.pair (w 2) (w 5) ∈ env 2 ∧
        Realize M.sets refinementClassCodeFormula
          ![w 1, env 3, w 5, Fin.cases (w 3) (fun _ => w 4) side,
            env 4, env 5, env 6] := by
  rw [assignmentClassGraphFormula, realize_exBlock]
  apply exists_congr
  intro w
  apply and_congr_right
  intro ground
  have args : (fun j : Fin 7 => extendMany 6 w env
      (![prefixIndex 7 6 1, suffixIndex 7 6 3, prefixIndex 7 6 5,
        Fin.cases (prefixIndex 7 6 3) (fun _ => prefixIndex 7 6 4) side,
        suffixIndex 7 6 4, suffixIndex 7 6 5, suffixIndex 7 6 6] j)) =
      ![w 1, env 3, w 5, Fin.cases (w 3) (fun _ => w 4) side, env 4, env 5, env 6] := by
    funext j
    refine Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases ?_
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) j
    exact Fin.cases rfl (fun _ => rfl) side
  simp only [Realize, BoundedFormula.realize_toFormula M _ _
    (extendMany_members 6 w env ground members), BoundedFormula.truth_orderedPairFormula,
    BoundedFormula.truth_stageOneAssignmentFormula, BoundedFormula.truth_pairMembershipFormula,
    extendMany_prefix, extendMany_suffix, realize_reindex, args]

variable {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)

theorem assignmentClassGraph_entry (side : Fin 2)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {A field T : ZFSet.{u}} (hA : A ∈ M.sets) (hField : field ∈ M.sets) (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (R u w : Name s)
    (hR : R.val ∈ M.sets) (hu : u.val ∈ M.sets) (hw : w.val ∈ M.sets)
    {i : ZFSet.{u}} (member : stageOneAssignment i u.val w.val ∈ A)
    (lookup : ∀ z, ZFSet.pair i z ∈ field ↔ z = R.val) (y : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment i u.val w.val) y ∈
      M.assignmentClassGraph side A field T s.carrier s.conditionOrder (s.encode ⊤) ↔
      y = (Name.refinementClass T valid R (Fin.cases (motive := fun _ => Name s) u (fun _ => w) side)).val := by
  have hTop := M.transitive carrier (s.encode_mem ⊤)
  have hAssignment := M.transitive hA member
  have hi := M.pair_left hAssignment
  have hBound := M.groundRelations_mem pairing unions powers separation hT carrier
  have hRepresentative : (Fin.cases (motive := fun _ => Name s) u (fun _ => w) side).val ∈ M.sets :=
    Fin.cases hu (fun _ => hw) side
  have representative : (Fin.cases (motive := fun _ => Name s) u (fun _ => w) side).val =
      Fin.cases (motive := fun _ => ZFSet.{u}) u.val (fun _ => w.val) side := Fin.cases rfl (fun _ => rfl) side
  let params : Fin 6 → ZFSet.{u} := ![A, field, T, s.carrier, s.conditionOrder, s.encode ⊤]
  have hp : ∀ j, params j ∈ M.sets := Fin.cases hA (Fin.cases hField (Fin.cases hT
    (Fin.cases carrier (Fin.cases order (Fin.cases hTop (fun j => Fin.elim0 j))))))
  rw [assignmentClassGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨_, hyB⟩, recognized⟩
    have hy := M.transitive hBound hyB
    obtain ⟨v, ground, _, equal, triple, relation, output⟩ :=
      (M.realize_assignmentClassGraphFormula side (extend _ params)
        (Fin.cases (M.orderedPair_mem pairing hAssignment hy) hp)).1 recognized
    obtain ⟨key, value⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨idx, first, second⟩ := (stageOneAssignment_eq_iff _ _ _ _ _ _).1 (key.trans triple)
    have rel : v 5 = R.val := (lookup _).1 (idx.symm ▸ relation)
    dsimp only [params, extend, Matrix.cons_val_zero, Matrix.cons_val_succ] at output
    rw [← value, rel, ← first, ← second, ← representative] at output
    exact (M.realize_refinementClassCodeFormula s pairing unions powers separation collection
      carrier order hT valid R _ hR hRepresentative y hy).1 output
  · intro equal
    subst y
    have named := M.refinementClass_mem s pairing unions powers separation collection carrier order
      hT valid R _ hR hRepresentative
    have bound := (M.mem_groundRelations T s.carrier _).2
      ⟨named, Name.refinementClass_subset T valid R _⟩
    refine ⟨⟨member, bound⟩, ?_⟩
    apply (M.realize_assignmentClassGraphFormula side (extend _ params)
      (Fin.cases (M.orderedPair_mem pairing hAssignment named) hp)).2
    refine ⟨![stageOneAssignment i u.val w.val,
      (Name.refinementClass T valid R (Fin.cases (motive := fun _ => Name s) u (fun _ => w) side)).val, i, u.val, w.val, R.val],
      Fin.cases hAssignment (Fin.cases named (Fin.cases hi (Fin.cases hu
        (Fin.cases hw (Fin.cases hR (fun j => Fin.elim0 j)))))), member, rfl, rfl,
      (lookup _).2 rfl, ?_⟩
    have realizing := (M.realize_refinementClassCodeFormula s pairing unions powers separation collection
      carrier order hT valid R _ hR hRepresentative _ named).2 rfl
    rw [representative] at realizing
    exact realizing

end TransitiveGround

namespace SetFormula

def refinementMapEntryFormula : SetFormula 8 :=
  ex (ex (ex (ex (ex (.conj (.mem 4 6) (.conj (.mem 0 10)
    (.conj (orderedPairFormula 5 1 0)
      (.conj (reindex ![3, 6, 8, 4, 10, 11, 12] refinementClassCodeFormula)
        (.conj (reindex ![2, 6, 9, 4, 10, 11, 12] refinementClassCodeFormula)
          (.conj (orderedPairNameCodeFormula 1 3 2 12)
            (forcingTranslation (ordinaryGroundPrimitives 0 1) (.mem 0 1)
              ![10, 11] 0 ![4, 7])))))))))))

def refinementMapCodeFormula : SetFormula 8 :=
  exactSetFormula 0 (reindex (extend 0 (fun j : Fin 7 => j.succ.succ)) refinementMapEntryFormula)

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
include pairing unions powers separation collection carrier order

theorem realize_refinementMapEntryFormula {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U Rf Rc : Name s)
    (hU : U.val ∈ M.sets) (hRf : Rf.val ∈ M.sets) (hRc : Rc.val ∈ M.sets)
    (x : ZFSet.{u}) (hx : x ∈ M.sets) :
    Realize M.sets refinementMapEntryFormula
      (extend x (extend T (extend U.val (extend Rf.val (extend Rc.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))))) ↔
      x ∈ (Name.refinementNaturalMap T valid U Rf Rc).val := by
  let env := extend x (extend T (extend U.val (extend Rf.val (extend Rc.val
    (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))))
  have members : ∀ j, env j ∈ M.sets :=
    Fin.cases hx (Fin.cases hT (Fin.cases hU (Fin.cases hRf (Fin.cases hRc
      (Fin.cases carrier (Fin.cases order (Fin.cases (M.transitive carrier (s.encode_mem ⊤))
        (fun j => Fin.elim0 j))))))))
  have fineArgs (w f c v q : ZFSet.{u}) :
      (fun j : Fin 7 => (extend q (extend v (extend c (extend f (extend w env)))))
        (![3, 6, 8, 4, 10, 11, 12] j)) =
        extend f (extend T (extend Rf.val (extend w
          (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) j
  have coarseArgs (w f c v q : ZFSet.{u}) :
      (fun j : Fin 7 => (extend q (extend v (extend c (extend f (extend w env)))))
        (![2, 6, 9, 4, 10, 11, 12] j)) =
        extend c (extend T (extend Rc.val (extend w
          (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) j
  change Realize M.sets refinementMapEntryFormula env ↔ _
  rw [refinementMapEntryFormula, realize_ex]
  constructor
  · rintro ⟨w, hw, body⟩
    obtain ⟨f, hf, body⟩ := (realize_ex M.sets _ _).1 body
    obtain ⟨c, hc, body⟩ := (realize_ex M.sets _ _).1 body
    obtain ⟨v, hv, body⟩ := (realize_ex M.sets _ _).1 body
    obtain ⟨q, hq, member, condition, pair, fine, coarse, named, forced⟩ := (realize_ex M.sets _ _).1 body
    change w ∈ T at member
    change q ∈ s.carrier at condition
    obtain ⟨p, rfl⟩ := (s.mem_carrier q).1 condition
    let term : Name s := ⟨w, valid w member⟩
    rw [realize_reindex, fineArgs] at fine
    rw [realize_reindex, coarseArgs] at coarse
    have feq := (M.realize_refinementClassCodeFormula s pairing unions powers separation collection
      carrier order hT valid Rf term hRf hw f hf).1 fine
    have ceq := (M.realize_refinementClassCodeFormula s pairing unions powers separation collection
      carrier order hT valid Rc term hRc hw c hc).1 coarse
    have all : ∀ j, (extend (s.encode p) (extend v (extend c (extend f (extend w env))))) j ∈ M.sets := Fin.cases hq (Fin.cases hv (Fin.cases hc (Fin.cases hf (Fin.cases hw members))))
    have veq := (M.realize_orderedPairNameCodeFormula pairing 1 3 2 12 _ all).1 named
    have equal := (M.realize_orderedPairFormula pairing 5 1 0 _ hx hv hq).1 pair
    let names : Assignment (M.nameDomain s) 2 := extend ⟨term, hw⟩ (extend ⟨U, hU⟩ Fin.elim0)
    have atom := (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
      carrier order 0 1 (.mem 0 1) ![10, 11] 0 ![4, 7] _ rfl rfl p names rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))).1 forced
    change x = ZFSet.pair v (s.encode p) at equal
    change v = orderedPairNameCode (s.encode ⊤) f c at veq
    rw [feq, ceq, ← Name.orderedPair_code] at veq
    rw [equal, veq]
    exact (Name.entry_refinementNaturalMap T valid U Rf Rc _ p).2 ⟨term, member, atom, rfl⟩
  · intro member
    obtain ⟨v, p, rfl⟩ := Name.entries_cover (Name.refinementNaturalMap T valid U Rf Rc) member
    obtain ⟨w, hwT, forced, rfl⟩ := (Name.entry_refinementNaturalMap T valid U Rf Rc v p).1 member
    have hw := M.transitive hT hwT
    have hp := M.transitive carrier (s.encode_mem p)
    have hf := M.refinementClass_mem s pairing unions powers separation collection carrier order hT valid Rf w hRf hw
    have hc := M.refinementClass_mem s pairing unions powers separation collection carrier order hT valid Rc w hRc hw
    have hv : (Name.orderedPair ⊤ (Name.refinementClass T valid Rf w) (Name.refinementClass T valid Rc w)).val ∈ M.sets := by
      rw [Name.orderedPair_code]
      exact M.orderedPairNameCode_mem pairing (M.transitive carrier (s.encode_mem ⊤)) hf hc
    refine ⟨w.val, hw, ?_⟩
    rw [realize_ex]
    refine ⟨(Name.refinementClass T valid Rf w).val, hf, ?_⟩
    rw [realize_ex]
    refine ⟨(Name.refinementClass T valid Rc w).val, hc, ?_⟩
    rw [realize_ex]
    refine ⟨(Name.orderedPair ⊤ (Name.refinementClass T valid Rf w) (Name.refinementClass T valid Rc w)).val, hv, ?_⟩
    rw [realize_ex]
    refine ⟨s.encode p, hp, hwT, s.encode_mem p, ?_, ?_, ?_, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing 5 1 0 _ hx hv hp).2 rfl
    · rw [realize_reindex, fineArgs]
      exact (M.realize_refinementClassCodeFormula s pairing unions powers separation collection
        carrier order hT valid Rf w hRf hw _ hf).2 rfl
    · rw [realize_reindex, coarseArgs]
      exact (M.realize_refinementClassCodeFormula s pairing unions powers separation collection
        carrier order hT valid Rc w hRc hw _ hc).2 rfl
    · exact (M.realize_orderedPairNameCodeFormula pairing 1 3 2 12 _
        (Fin.cases hp (Fin.cases hv (Fin.cases hc (Fin.cases hf (Fin.cases hw members)))))).2
        (Name.orderedPair_code ⊤ _ _)
    · let names : Assignment (M.nameDomain s) 2 := extend ⟨w, hw⟩ (extend ⟨U, hU⟩ Fin.elim0)
      exact (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
        carrier order 0 1 (.mem 0 1) ![10, 11] 0 ![4, 7] _ rfl rfl p names rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))).2 forced

theorem realize_refinementMapCodeFormula {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U Rf Rc : Name s)
    (hU : U.val ∈ M.sets) (hRf : Rf.val ∈ M.sets) (hRc : Rc.val ∈ M.sets)
    (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets refinementMapCodeFormula
      (extend z (extend T (extend U.val (extend Rf.val (extend Rc.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))))) ↔
      z = (Name.refinementNaturalMap T valid U Rf Rc).val := by
  have ground := M.refinementNaturalMap_mem s pairing unions powers separation collection
    carrier order hT valid U Rf Rc hU hRf hRc
  apply M.realize_exactSetFormula 0 _ _ hz (fun _ h => M.transitive ground h)
  intro x hx
  rw [realize_reindex, map_extend]
  exact M.realize_refinementMapEntryFormula s pairing unions powers separation collection
    carrier order hT valid U Rf Rc hU hRf hRc x hx

end TransitiveGround

namespace SetFormula

def refinementQuotientEntryFormula : SetFormula 7 :=
  ex (ex (ex (.conj (.mem 2 4) (.conj (.mem 0 7)
    (.conj (orderedPairFormula 3 1 0)
      (.conj (reindex ![1, 4, 6, 2, 7, 8, 9] refinementClassCodeFormula)
        (forcingTranslation (ordinaryGroundPrimitives 0 1) (.mem 0 1)
          ![7, 8] 0 ![2, 5])))))))

def refinementQuotientCodeFormula : SetFormula 7 :=
  exactSetFormula 0 (reindex (extend 0 (fun j : Fin 6 => j.succ.succ)) refinementQuotientEntryFormula)

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
include pairing unions powers separation collection carrier order

theorem realize_refinementQuotientEntryFormula {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U R : Name s) (hU : U.val ∈ M.sets) (hR : R.val ∈ M.sets)
    (x : ZFSet.{u}) (hx : x ∈ M.sets) :
    Realize M.sets refinementQuotientEntryFormula
      (extend x (extend T (extend U.val (extend R.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0))))))) ↔
      x ∈ (Name.refinementQuotient T valid U R).val := by
  let env := extend x (extend T (extend U.val (extend R.val
    (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0))))))
  have classArgs (w c q : ZFSet.{u}) :
      (fun j : Fin 7 => (extend q (extend c (extend w env))) (![1, 4, 6, 2, 7, 8, 9] j)) =
        extend c (extend T (extend R.val (extend w
          (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) j
  change Realize M.sets refinementQuotientEntryFormula env ↔ _
  rw [refinementQuotientEntryFormula, realize_ex]
  constructor
  · rintro ⟨w, hw, body⟩
    obtain ⟨c, hc, body⟩ := (realize_ex M.sets _ _).1 body
    obtain ⟨q, hq, member, condition, pair, recognized, forced⟩ := (realize_ex M.sets _ _).1 body
    change w ∈ T at member
    change q ∈ s.carrier at condition
    obtain ⟨p, rfl⟩ := (s.mem_carrier q).1 condition
    let term : Name s := ⟨w, valid w member⟩
    rw [realize_reindex, classArgs] at recognized
    have code := (M.realize_refinementClassCodeFormula s pairing unions powers separation collection
      carrier order hT valid R term hR hw c hc).1 recognized
    have equal := (M.realize_orderedPairFormula pairing 3 1 0 _ hx hc hq).1 pair
    let names : Assignment (M.nameDomain s) 2 := extend ⟨term, hw⟩ (extend ⟨U, hU⟩ Fin.elim0)
    have atom := (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
      carrier order 0 1 (.mem 0 1) ![7, 8] 0 ![2, 5] _ rfl rfl p names rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))).1 forced
    change x = ZFSet.pair c (s.encode p) at equal
    rw [equal, code]
    exact (Name.entry_refinementQuotient T valid U R _ p).2 ⟨term, member, atom, rfl⟩
  · intro member
    obtain ⟨c, p, rfl⟩ := Name.entries_cover (Name.refinementQuotient T valid U R) member
    obtain ⟨w, hwT, forced, rfl⟩ := (Name.entry_refinementQuotient T valid U R c p).1 member
    have hw := M.transitive hT hwT
    have hp := M.transitive carrier (s.encode_mem p)
    have hc := M.refinementClass_mem s pairing unions powers separation collection carrier order hT valid R w hR hw
    refine ⟨w.val, hw, ?_⟩
    rw [realize_ex]
    refine ⟨(Name.refinementClass T valid R w).val, hc, ?_⟩
    rw [realize_ex]
    refine ⟨s.encode p, hp, hwT, s.encode_mem p, ?_, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing 3 1 0 _ hx hc hp).2 rfl
    · rw [realize_reindex, classArgs]
      exact (M.realize_refinementClassCodeFormula s pairing unions powers separation collection
        carrier order hT valid R w hR hw _ hc).2 rfl
    · let names : Assignment (M.nameDomain s) 2 := extend ⟨w, hw⟩ (extend ⟨U, hU⟩ Fin.elim0)
      exact (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
        carrier order 0 1 (.mem 0 1) ![7, 8] 0 ![2, 5] _ rfl rfl p names rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))).2 forced

theorem realize_refinementQuotientCodeFormula {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U R : Name s) (hU : U.val ∈ M.sets) (hR : R.val ∈ M.sets)
    (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets refinementQuotientCodeFormula
      (extend z (extend T (extend U.val (extend R.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0))))))) ↔
      z = (Name.refinementQuotient T valid U R).val := by
  have ground := M.refinementQuotient_mem s pairing unions powers separation collection carrier order hT valid U R hU hR
  apply M.realize_exactSetFormula 0 _ _ hz (fun _ h => M.transitive ground h)
  intro x hx
  rw [realize_reindex, map_extend]
  exact M.realize_refinementQuotientEntryFormula s pairing unions powers separation collection
    carrier order hT valid U R hU hR x hx

end TransitiveGround
end PartitionPilot.Forcing

end OAI
