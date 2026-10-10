import OAI.SetTheory.PartitionPrinciple.Definability.EquivalenceClassCodes
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundNiceNameNormalization
import OAI.SetTheory.PartitionPrinciple.Transfinite.StageOneDataBoundLaws

namespace OAI


namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

noncomputable def refinementClass (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (R w : Name s) : Name s :=
  selectName (fun z p => ForcesMem p (orderedPair ⊤ z w) R) (familySet ⊤ T valid)

theorem entry_refinementClass (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (R w z : Name s) (p : P) :
    Entry z (refinementClass T valid R w) p ↔
      z.val ∈ T ∧ ForcesMem p (orderedPair ⊤ z w) R := by
  rw [refinementClass, entry_selectName]
  constructor
  · rintro ⟨r, entry, _, forced⟩
    exact ⟨((entry_familySet ⊤ T valid z r).1 entry).1, forced⟩
  · rintro ⟨member, forced⟩
    exact ⟨⊤, (entry_familySet ⊤ T valid z ⊤).2 ⟨member, rfl⟩, le_top, forced⟩

theorem refinementClass_subset (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (R w : Name s) : (refinementClass T valid R w).val ⊆ ZFSet.prod T s.carrier := by
  intro x member
  obtain ⟨z, p, rfl⟩ := entries_cover (refinementClass T valid R w) member
  exact ZFSet.pair_mem_prod.2
    ⟨((entry_refinementClass T valid R w z p).1 member).1, s.encode_mem p⟩

theorem eval_refinementClass (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D))
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (R w : Name s)
    (hR : R ∈ D.names)
    (pairs : ∀ z : Name s, z.val ∈ T → orderedPair ⊤ z w ∈ D.names) :
    eval {p | H.mem p} (refinementClass T valid R w) =
      equivalenceClass (eval {p | H.mem p} (familySet ⊤ T valid))
        (eval {p | H.mem p} R) (eval {p | H.mem p} w) := by
  apply ZFSet.ext
  intro x
  rw [mem_eval, mem_equivalenceClass]
  constructor
  · rintro ⟨z, p, entry, hp, rfl⟩
    obtain ⟨member, forced⟩ := (entry_refinementClass T valid R w z p).1 entry
    have related := forcesMem_sound D H generic (pairs z member) hR hp forced
    rw [eval_orderedPair {p | H.mem p} ⊤ H.top_mem z w] at related
    exact ⟨(mem_eval_familySet {p | H.mem p} ⊤ H.top_mem T valid _).2 ⟨z, member, rfl⟩, related⟩
  · rintro ⟨member, related⟩
    obtain ⟨z, hz, rfl⟩ := (mem_eval_familySet {p | H.mem p} ⊤ H.top_mem T valid x).1 member
    have named : eval {p | H.mem p} (orderedPair ⊤ z w) ∈ eval {p | H.mem p} R := by
      rw [eval_orderedPair {p | H.mem p} ⊤ H.top_mem z w]
      exact related
    obtain ⟨p, hp, forced⟩ := (eval_mem_iff_forcesMem D H generic (pairs z hz) hR).1 named
    exact ⟨z, p, (entry_refinementClass T valid R w z p).2 ⟨hz, forced⟩, hp, rfl⟩

variable {G : Type v} [Group G] (a : PosetAction G P)

theorem act_refinementClass (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
    (g : G) (R w : Name s) :
    a.act s g (refinementClass T valid R w) =
      refinementClass T valid (a.act s g R) (a.act s g w) := by
  unfold refinementClass
  rw [a.act_selectName s g _ (fun z p => ForcesMem p (orderedPair ⊤ z (a.act s g w)) (a.act s g R))]
  · rw [act_familySet a T valid closed]
  · intro z p
    have paired : a.act s g (orderedPair ⊤ z w) =
        orderedPair ⊤ (a.act s g z) (a.act s g w) := by
      change rename s (a.iso g) _ = _
      rw [rename_orderedPair, (a.iso g).map_top]
      rfl
    rw [← paired]
    exact a.forcesMem_act_iff s g p (orderedPair ⊤ z w) R

theorem refinementClass_support (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
    (R w : Name s) (K : Subgroup G)
    (relation : K ≤ a.stabilizer s R) (representative : K ≤ a.stabilizer s w) :
    K ≤ a.stabilizer s (refinementClass T valid R w) := by
  intro g hg
  change a.act s g _ = _
  rw [act_refinementClass a T valid closed, relation hg, representative hg]

theorem refinementClass_hs (F : NormalSubgroupFamily G)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
    (children : ∀ z : Name s, z.val ∈ T → HereditarilySymmetric a s F z)
    (R w : Name s) (K : Subgroup G) (member : F.mem K)
    (relation : K ≤ a.stabilizer s R) (representative : K ≤ a.stabilizer s w) :
    HereditarilySymmetric a s F (refinementClass T valid R w) :=
  HereditarilySymmetric.mk
    (F.upward member (refinementClass_support a T valid closed R w K relation representative))
    (fun z p entry => children z ((entry_refinementClass T valid R w z p).1 entry).1)

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace SetFormula

def refinementClassEntryFormula : SetFormula 7 :=
  ex (ex (ex (.conj (.mem 2 4) (.conj (.mem 1 7)
    (.conj (orderedPairFormula 3 2 1)
      (.conj (orderedPairNameCodeFormula 0 2 6 9)
        (forcingTranslation (ordinaryGroundPrimitives 0 1) (.mem 0 1)
          ![7, 8] 1 ![0, 5])))))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include pairing unions powers separation collection carrier order in
theorem realize_refinementClassEntryFormula {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (R w : Name s) (hR : R.val ∈ M.sets) (hw : w.val ∈ M.sets)
    (x : ZFSet.{u}) (hx : x ∈ M.sets) :
    Realize M.sets refinementClassEntryFormula
      (extend x (extend T (extend R.val (extend w.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0))))))) ↔
      x ∈ (Name.refinementClass T valid R w).val := by
  let env := extend x (extend T (extend R.val (extend w.val
    (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0))))))
  have hone := M.transitive carrier (s.encode_mem ⊤)
  have members : ∀ j, env j ∈ M.sets :=
    Fin.cases hx (Fin.cases hT (Fin.cases hR (Fin.cases hw
      (Fin.cases carrier (Fin.cases order (Fin.cases hone (fun j => Fin.elim0 j)))))))
  change Realize M.sets refinementClassEntryFormula env ↔ _
  rw [refinementClassEntryFormula, realize_ex]
  constructor
  · rintro ⟨z, hz, body⟩
    obtain ⟨q, hq, body⟩ := (realize_ex M.sets _ _).1 body
    obtain ⟨v, hv, member, hqP, entry, pairName, forced⟩ := (realize_ex M.sets _ _).1 body
    change z ∈ T at member
    change q ∈ s.carrier at hqP
    obtain ⟨p, rfl⟩ := (s.mem_carrier q).1 hqP
    let σ : Name s := ⟨z, valid z member⟩
    have hpGround := M.transitive carrier (s.encode_mem p)
    have all : ∀ j, (extend v (extend (s.encode p) (extend z env))) j ∈ M.sets :=
      Fin.cases hv (Fin.cases hpGround (Fin.cases hz members))
    have entryEq := (M.realize_orderedPairFormula pairing 3 2 1 _ hx hz hpGround).1 entry
    change x = ZFSet.pair z (s.encode p) at entryEq
    have pairEq := (M.realize_orderedPairNameCodeFormula pairing 0 2 6 9 _ all).1 pairName
    have named : v = (Name.orderedPair ⊤ σ w).val :=
      pairEq.trans (Name.orderedPair_code ⊤ σ w).symm
    have hpair : (Name.orderedPair ⊤ σ w).val ∈ M.sets := named ▸ hv
    let names : Assignment (M.nameDomain s) 2 :=
      extend ⟨Name.orderedPair ⊤ σ w, hpair⟩ (extend ⟨R, hR⟩ Fin.elim0)
    have atom := (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
      carrier order 0 1 (.mem 0 1) ![7, 8] 1 ![0, 5] _ rfl rfl p names rfl
      (Fin.cases named (Fin.cases rfl (fun j => Fin.elim0 j)))).1 forced
    rw [entryEq]
    exact (Name.entry_refinementClass T valid R w σ p).2 ⟨member, atom⟩
  · intro member
    obtain ⟨σ, p, rfl⟩ := Name.entries_cover (Name.refinementClass T valid R w) member
    obtain ⟨hσT, forced⟩ := (Name.entry_refinementClass T valid R w σ p).1 member
    have hσ := M.transitive hT hσT
    have hp := M.transitive carrier (s.encode_mem p)
    have hpair : (Name.orderedPair ⊤ σ w).val ∈ M.sets := by
      rw [Name.orderedPair_code]
      exact M.orderedPairNameCode_mem pairing hone hσ hw
    refine ⟨σ.val, hσ, ?_⟩
    rw [realize_ex]
    refine ⟨s.encode p, hp, ?_⟩
    rw [realize_ex]
    refine ⟨(Name.orderedPair ⊤ σ w).val, hpair, hσT, s.encode_mem p, ?_, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing 3 2 1 _ hx hσ hp).2 rfl
    · exact (M.realize_orderedPairNameCodeFormula pairing 0 2 6 9 _
        (Fin.cases hpair (Fin.cases hp (Fin.cases hσ members)))).2
        (Name.orderedPair_code ⊤ σ w)
    · let names : Assignment (M.nameDomain s) 2 :=
        extend ⟨Name.orderedPair ⊤ σ w, hpair⟩ (extend ⟨R, hR⟩ Fin.elim0)
      exact (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
        carrier order 0 1 (.mem 0 1) ![7, 8] 1 ![0, 5] _ rfl rfl p names rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))).2 forced

include pairing unions powers separation collection carrier order in
theorem refinementClass_eq_selection {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (R w : Name s) (hR : R.val ∈ M.sets) (hw : w.val ∈ M.sets) :
    (Name.refinementClass T valid R w).val =
      ZFSet.sep (fun x => Realize M.sets refinementClassEntryFormula
        (extend x (extend T (extend R.val (extend w.val
          (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0))))))))
        (ZFSet.prod T s.carrier) := by
  have bound := M.prod_mem pairing unions powers separation hT carrier
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_sep]
  constructor
  · intro member
    have hx := Name.refinementClass_subset T valid R w member
    exact ⟨hx, (M.realize_refinementClassEntryFormula s pairing unions powers separation collection
      carrier order hT valid R w hR hw x (M.transitive bound hx)).2 member⟩
  · rintro ⟨hx, formula⟩
    exact (M.realize_refinementClassEntryFormula s pairing unions powers separation collection
      carrier order hT valid R w hR hw x (M.transitive bound hx)).1 formula

include pairing unions powers separation collection carrier order in
theorem refinementClass_mem {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (R w : Name s) (hR : R.val ∈ M.sets) (hw : w.val ∈ M.sets) :
    (Name.refinementClass T valid R w).val ∈ M.sets := by
  rw [M.refinementClass_eq_selection s pairing unions powers separation collection carrier order
    hT valid R w hR hw]
  exact M.separation_mem separation refinementClassEntryFormula _
    (Fin.cases hT (Fin.cases hR (Fin.cases hw (Fin.cases carrier (Fin.cases order
      (Fin.cases (M.transitive carrier (s.encode_mem ⊤)) (fun j => Fin.elim0 j)))))))
    (M.prod_mem pairing unions powers separation hT carrier)

include pairing carrier in
theorem eval_refinementClass {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (R w : Name s) (hR : R.val ∈ M.sets) (hw : w.val ∈ M.sets)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s))) :
    Name.eval {p | H.mem p} (Name.refinementClass T valid R w) =
      equivalenceClass (Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
        (Name.eval {p | H.mem p} R) (Name.eval {p | H.mem p} w) := by
  apply Name.eval_refinementClass (M.nameDomain s) H (fun E hE dense => generic E (Or.inl hE) dense)
    T valid R w hR
  intro z hz
  change (Name.orderedPair ⊤ z w).val ∈ M.sets
  rw [Name.orderedPair_code]
  exact M.orderedPairNameCode_mem pairing (M.transitive carrier (s.encode_mem ⊤))
    (M.transitive hT hz) hw

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P Q : Type u} [PartialOrder P] [OrderTop P]
variable {s : Presentation P} (upper : Presentation Q) (incl : P → Q) (one : Q)

noncomputable def refinementAssignmentLabel (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (idx : ZFSet.{u}) (Rf Rc : Name s) : Name upper :=
  assemble
    (fun a : {a : (T × T) × Q //
        ∃ row A, upper.encode a.2 = ZFSet.pair row A ∧
          stageOneAssignment idx a.1.1.val a.1.2.val ∈ A} =>
      orderedPair one
        (rename upper incl (refinementClass T valid Rc
          ⟨a.val.1.1.val, valid _ a.val.1.1.property⟩))
        (rename upper incl (refinementClass T valid Rf
          ⟨a.val.1.2.val, valid _ a.val.1.2.property⟩)))
    (fun a => a.val.2)

theorem entry_refinementAssignmentLabel (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (idx : ZFSet.{u}) (Rf Rc : Name s)
    (sigma : Name upper) (p : Q) :
    Entry sigma (refinementAssignmentLabel upper incl one T valid idx Rf Rc) p ↔
      ∃ v w : Name s, v.val ∈ T ∧ w.val ∈ T ∧
        (∃ row A, upper.encode p = ZFSet.pair row A ∧ stageOneAssignment idx v.val w.val ∈ A) ∧
        orderedPair one (rename upper incl (refinementClass T valid Rc v))
          (rename upper incl (refinementClass T valid Rf w)) = sigma := by
  rw [refinementAssignmentLabel, entry_assemble]
  constructor
  · rintro ⟨a, equal, condition⟩
    refine ⟨⟨a.val.1.1.val, valid _ a.val.1.1.property⟩,
      ⟨a.val.1.2.val, valid _ a.val.1.2.property⟩,
      a.val.1.1.property, a.val.1.2.property, ?_, equal⟩
    exact condition ▸ a.property
  · rintro ⟨v, w, hv, hw, literal, equal⟩
    exact ⟨⟨((⟨v.val, hv⟩, ⟨w.val, hw⟩), p), literal⟩, equal, rfl⟩

theorem mem_eval_refinementAssignmentLabel (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (idx : ZFSet.{u}) (Rf Rc : Name s)
    (H : Set Q) (hone : one ∈ H) (z : ZFSet.{u}) :
    z ∈ eval H (refinementAssignmentLabel upper incl one T valid idx Rf Rc) ↔
      ∃ (p : Q) (v w : Name s), p ∈ H ∧ v.val ∈ T ∧ w.val ∈ T ∧
        (∃ row A, upper.encode p = ZFSet.pair row A ∧ stageOneAssignment idx v.val w.val ∈ A) ∧
        ZFSet.pair (eval {q | incl q ∈ H} (refinementClass T valid Rc v))
          (eval {q | incl q ∈ H} (refinementClass T valid Rf w)) = z := by
  rw [mem_eval]
  constructor
  · rintro ⟨sigma, p, entry, hp, equal⟩
    obtain ⟨v, w, hv, hw, literal, rfl⟩ :=
      (entry_refinementAssignmentLabel upper incl one T valid idx Rf Rc sigma p).1 entry
    refine ⟨p, v, w, hp, hv, hw, literal, ?_⟩
    simpa only [eval_orderedPair H one hone, eval_rename] using equal
  · rintro ⟨p, v, w, hp, hv, hw, literal, equal⟩
    refine ⟨_, p, (entry_refinementAssignmentLabel upper incl one T valid idx Rf Rc _ p).2
      ⟨v, w, hv, hw, literal, rfl⟩, hp, ?_⟩
    simpa only [eval_orderedPair H one hone, eval_rename] using equal

end PartitionPilot.Forcing.Name

end OAI
