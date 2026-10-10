import OAI.SetTheory.PartitionPrinciple.Forcing.GroundNiceNameNormalization
import OAI.SetTheory.PartitionPrinciple.Geometry.RefinementValidityReindex

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization SetFormula
universe u

namespace SetFormula

def sharedConditionFormula {n : Nat} (phi : SetFormula n) (i : Fin n) :
    SetFormula (n + 1) :=
  .conj (reindex Fin.succ phi) (.mem 0 i.succ)

theorem realize_sharedConditionFormula (U : Set ZFSet.{u}) {n : Nat}
    (phi : SetFormula n) (i : Fin n) (env : Fin n → ZFSet.{u}) (x : ZFSet.{u}) :
    Realize U (sharedConditionFormula phi i) (extend x env) ↔
      Realize U phi env ∧ x ∈ env i := by
  change (Realize U (reindex Fin.succ phi) (extend x env) ∧ x ∈ env i) ↔ _
  rw [realize_reindex]
  rfl

end SetFormula

namespace Name
variable {P : Type u} [Preorder P] [OrderTop P] {s : Presentation P}

noncomputable def sharedConditionName (D : NameDomain s) {n : Nat}
    (phi : SetFormula n) (env : Assignment D n) (i : Fin n)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) : Name s :=
  separationName D (sharedConditionFormula phi i) env (familySet ⊤ T valid)

theorem entry_sharedConditionName (D : NameDomain s) {n : Nat}
    (phi : SetFormula n) (env : Assignment D n) (i : Fin n)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (sigma : Name s) (p : P) :
    Entry sigma (sharedConditionName D phi env i T valid) p ↔
      sigma.val ∈ T ∧ ∃ h : sigma ∈ D.names,
        Forces D (sharedConditionFormula phi i) (extend ⟨sigma, h⟩ env) p := by
  rw [sharedConditionName, entry_separationName]
  constructor
  · rintro ⟨r, entry, _, forced⟩
    exact ⟨((entry_familySet ⊤ T valid sigma r).1 entry).1, forced⟩
  · rintro ⟨member, forced⟩
    exact ⟨⊤, (entry_familySet ⊤ T valid sigma ⊤).2 ⟨member, rfl⟩, le_top, forced⟩

theorem sharedConditionName_subset (D : NameDomain s) {n : Nat}
    (phi : SetFormula n) (env : Assignment D n) (i : Fin n)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) :
    (sharedConditionName D phi env i T valid).val ⊆ ZFSet.prod T s.carrier := by
  intro z member
  obtain ⟨sigma, p, rfl⟩ := entries_cover (sharedConditionName D phi env i T valid) member
  exact ZFSet.pair_mem_prod.2
    ⟨((entry_sharedConditionName D phi env i T valid sigma p).1 member).1, s.encode_mem p⟩

end Name
end

namespace Name
open SetRealization SetFormula
universe u
variable {P : Type u} [Preorder P] [OrderTop P] {s : Presentation P}

theorem eval_sharedConditionName (D : NameDomain s) {n : Nat}
    (phi : SetFormula n) (env : Assignment D n) (i : Fin n)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (family : familySet ⊤ T valid ∈ D.names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D)) :
    eval {p | H.mem p} (sharedConditionName D phi env i T valid) =
      ZFSet.sep (fun x => Realize (D.values {p | H.mem p}) phi
        (evalAssignment {p | H.mem p} env) ∧ x ∈ eval {p | H.mem p} (env i).val)
        (eval {p | H.mem p} (familySet ⊤ T valid)) := by
  rw [sharedConditionName, eval_separationName D H generic
    (sharedConditionFormula phi i) env family]
  apply ZFSet.ext
  intro x
  simp only [ZFSet.mem_sep, realize_sharedConditionFormula]
  rfl

theorem eval_sharedConditionName_of_true (D : NameDomain s) {n : Nat}
    (phi : SetFormula n) (env : Assignment D n) (i : Fin n)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (family : familySet ⊤ T valid ∈ D.names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D))
    (truth : Realize (D.values {p | H.mem p}) phi
      (evalAssignment {p | H.mem p} env)) :
    eval {p | H.mem p} (sharedConditionName D phi env i T valid) =
      eval {p | H.mem p} (env i).val ∩ eval {p | H.mem p} (familySet ⊤ T valid) := by
  rw [eval_sharedConditionName D phi env i T valid family H generic]
  apply ZFSet.ext
  intro x
  simp only [ZFSet.mem_sep, ZFSet.mem_inter, truth, true_and]
  exact and_comm

theorem eval_sharedConditionName_of_subset (D : NameDomain s) {n : Nat}
    (phi : SetFormula n) (env : Assignment D n) (i : Fin n)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (family : familySet ⊤ T valid ∈ D.names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D))
    (truth : Realize (D.values {p | H.mem p}) phi
      (evalAssignment {p | H.mem p} env))
    (subset : eval {p | H.mem p} (env i).val ⊆
      eval {p | H.mem p} (familySet ⊤ T valid)) :
    eval {p | H.mem p} (sharedConditionName D phi env i T valid) =
      eval {p | H.mem p} (env i).val := by
  rw [eval_sharedConditionName_of_true D phi env i T valid family H generic truth]
  apply ZFSet.ext
  intro x
  exact ⟨fun member => (ZFSet.mem_inter.1 member).1,
    fun member => ZFSet.mem_inter.2 ⟨member, subset member⟩⟩

theorem eval_sharedConditionName_of_false (D : NameDomain s) {n : Nat}
    (phi : SetFormula n) (env : Assignment D n) (i : Fin n)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (family : familySet ⊤ T valid ∈ D.names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D))
    (falsehood : ¬ Realize (D.values {p | H.mem p}) phi
      (evalAssignment {p | H.mem p} env)) :
    eval {p | H.mem p} (sharedConditionName D phi env i T valid) = ∅ := by
  rw [eval_sharedConditionName D phi env i T valid family H generic]
  apply ZFSet.ext
  intro x
  simp [falsehood]

end Name

namespace Name
open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}
variable {G : Type v} [Group G] (a : PosetAction G P)
variable (D : NameDomain s)
variable (closed : ∀ g sigma, sigma ∈ D.names → a.act s g sigma ∈ D.names)
variable {n : Nat} (phi : SetFormula n) (env : Assignment D n) (i : Fin n)
variable (J : ZFSet.{u}) (valid : ∀ z ∈ J, IsName s z)
variable (terms : ∀ g (sigma : Name s), sigma.val ∈ J → (a.act s g sigma).val ∈ J)
include closed terms

theorem sharedConditionName_act (g : G) :
    a.act s g (sharedConditionName D phi env i J valid) =
      sharedConditionName D phi (a.actAssignment s D closed g env) i J valid := by
  unfold sharedConditionName
  rw [a.act_separationName s D closed, act_familySet a J valid terms]

theorem sharedConditionName_nice (K : Subgroup G)
    (fixed : ∀ j, K ≤ a.stabilizer s (env j).val) :
    NiceNameCode a s J K (sharedConditionName D phi env i J valid).val := by
  apply (niceNameCode_iff a s _).2
  refine ⟨sharedConditionName_subset D phi env i J valid, ?_⟩
  intro g hg
  change a.act s g (sharedConditionName D phi env i J valid) = _
  rw [sharedConditionName_act a D closed phi env i J valid terms]
  have equal : a.actAssignment s D closed g env = env := by
    funext j
    apply Subtype.ext
    exact fixed j hg
  rw [equal]

theorem sharedConditionName_hs (K : Subgroup G)
    (fixed : ∀ j, K ≤ a.stabilizer s (env j).val)
    (F : NormalSubgroupFamily G) (member : F.mem K)
    (children : ∀ sigma : Name s, sigma.val ∈ J → HereditarilySymmetric a s F sigma) :
    HereditarilySymmetric a s F (sharedConditionName D phi env i J valid) :=
  niceNameCode_hs a s F member children
    (sharedConditionName_nice a D closed phi env i J valid terms K fixed)

end Name

namespace TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
include pairing unions powers separation collection carrier order

theorem sharedConditionName_mem {n : Nat} (phi : SetFormula n)
    (env : Assignment (M.nameDomain s) n) (i : Fin n)
    {J : ZFSet.{u}} (hJ : J ∈ M.sets) (valid : ∀ z ∈ J, IsName s z) :
    (Name.sharedConditionName (M.nameDomain s) phi env i J valid).val ∈ M.sets := by
  have family := M.familySet_mem s ⊤ pairing unions powers separation hJ
    (M.transitive carrier (s.encode_mem ⊤)) valid
  exact M.ordinarySeparationName_mem s pairing unions powers separation collection carrier order
    (sharedConditionFormula phi i) env ⟨Name.familySet ⊤ J valid, family⟩

theorem sharedConditionName_spec {G : Type u} [Group G]
    (a : PosetAction G P) (t : Presentation G)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    {n : Nat} (phi : SetFormula n) (env : Assignment (M.nameDomain s) n) (i : Fin n)
    {J : ZFSet.{u}} (hJ : J ∈ M.sets) (valid : ∀ z ∈ J, IsName s z)
    (terms : ∀ g (sigma : Name s), sigma.val ∈ J → (a.act s g sigma).val ∈ J)
    (K : Subgroup G) (fixed : ∀ j, K ≤ a.stabilizer s (env j).val)
    (F : NormalSubgroupFamily G) (member : F.mem K)
    (children : ∀ sigma : Name s, sigma.val ∈ J → HereditarilySymmetric a s F sigma) :
    (Name.sharedConditionName (M.nameDomain s) phi env i J valid).val ∈ M.sets ∧
      NiceNameCode a s J K (Name.sharedConditionName (M.nameDomain s) phi env i J valid).val ∧
      HereditarilySymmetric a s F (Name.sharedConditionName (M.nameDomain s) phi env i J valid) := by
  have closed : ∀ g sigma, sigma ∈ (M.nameDomain s).names →
      a.act s g sigma ∈ (M.nameDomain s).names :=
    fun g sigma h => M.act_mem s a t pairing unions powers separation collection carrier maps g sigma h
  exact ⟨M.sharedConditionName_mem s pairing unions powers separation collection carrier order phi env i hJ valid,
    Name.sharedConditionName_nice a (M.nameDomain s) closed phi env i J valid terms K fixed,
    Name.sharedConditionName_hs a (M.nameDomain s) closed phi env i J valid terms K fixed F member children⟩

end TransitiveGround

namespace Name
open SetRealization SetFormula
universe u
variable {P : Type u} [Preorder P] [OrderTop P] {s : Presentation P}

noncomputable def refinementConditionNames (D : NameDomain s)
    (env : Assignment D 4) (T : Fin 3 → ZFSet.{u})
    (valid : ∀ i, ∀ z ∈ T i, IsName s z) : Fin 3 → Name s :=
  fun i => sharedConditionName D BoundedFormula.refinementValidityFormula.toFormula
    env i.castSucc (T i) (valid i)

theorem eval_refinementConditionNames_coherent (D : NameDomain s)
    (env : Assignment D 4) (T : Fin 3 → ZFSet.{u})
    (valid : ∀ i, ∀ z ∈ T i, IsName s z)
    (family : ∀ i, familySet ⊤ (T i) (valid i) ∈ D.names)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily D))
    (shape : ∀ i : Fin 3, (env i.castSucc).val.val ⊆ ZFSet.prod (T i) s.carrier) :
    (Realize (D.values {p | H.mem p}) BoundedFormula.refinementValidityFormula.toFormula
      (evalAssignment {p | H.mem p} env) ∧
      ∀ i : Fin 3, eval {p | H.mem p} (refinementConditionNames D env T valid i) =
        eval {p | H.mem p} (env i.castSucc).val) ∨
    (¬ Realize (D.values {p | H.mem p}) BoundedFormula.refinementValidityFormula.toFormula
      (evalAssignment {p | H.mem p} env) ∧
      ∀ i : Fin 3, eval {p | H.mem p} (refinementConditionNames D env T valid i) = ∅) := by
  classical
  by_cases truth : Realize (D.values {p | H.mem p})
      BoundedFormula.refinementValidityFormula.toFormula (evalAssignment {p | H.mem p} env)
  · refine Or.inl ⟨truth, ?_⟩
    intro i
    exact eval_sharedConditionName_of_subset D BoundedFormula.refinementValidityFormula.toFormula
      env i.castSucc (T i) (valid i) (family i) H generic truth
      (eval_subset_familySet_of_code_subset H (T i) (valid i) (env i.castSucc).val (shape i))
  · refine Or.inr ⟨truth, ?_⟩
    intro i
    exact eval_sharedConditionName_of_false D BoundedFormula.refinementValidityFormula.toFormula
      env i.castSucc (T i) (valid i) (family i) H generic truth

theorem eval_refinementConditionNames_valid (D : NameDomain s)
    (env : Assignment D 4) (T : Fin 3 → ZFSet.{u})
    (valid : ∀ i, ∀ z ∈ T i, IsName s z)
    (family : ∀ i, familySet ⊤ (T i) (valid i) ∈ D.names)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily D))
    (shape : ∀ i : Fin 3, (env i.castSucc).val.val ⊆ ZFSet.prod (T i) s.carrier) :
    RefinementValidityCode (eval {p | H.mem p} (env 3).val)
      (eval {p | H.mem p} (refinementConditionNames D env T valid 0))
      (eval {p | H.mem p} (refinementConditionNames D env T valid 1))
      (eval {p | H.mem p} (refinementConditionNames D env T valid 2)) := by
  let evaluated : TransitiveGround.{u} :=
    ⟨D.values {p | H.mem p}, D.values_transitive {p | H.mem p}⟩
  rcases eval_refinementConditionNames_coherent D env T valid family H generic shape with
    ⟨truth, equal⟩ | ⟨_, equal⟩
  · rw [equal 0, equal 1, equal 2]
    exact (evaluated.realize_refinementValidityFormula
      (evalAssignment {p | H.mem p} env) (fun i => ⟨env i, rfl⟩)).1 truth
  · rw [equal 0, equal 1, equal 2]
    exact refinementValidity_empty _

theorem eval_refinementConditionNames_of_valid (D : NameDomain s)
    (env : Assignment D 4) (T : Fin 3 → ZFSet.{u})
    (valid : ∀ i, ∀ z ∈ T i, IsName s z)
    (family : ∀ i, familySet ⊤ (T i) (valid i) ∈ D.names)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily D))
    (shape : ∀ i : Fin 3, (env i.castSucc).val.val ⊆ ZFSet.prod (T i) s.carrier)
    (oldValid : RefinementValidityCode (eval {p | H.mem p} (env 3).val)
      (eval {p | H.mem p} (env 0).val) (eval {p | H.mem p} (env 1).val)
      (eval {p | H.mem p} (env 2).val)) :
    ∀ i : Fin 3, eval {p | H.mem p} (refinementConditionNames D env T valid i) =
      eval {p | H.mem p} (env i.castSucc).val := by
  let evaluated : TransitiveGround.{u} :=
    ⟨D.values {p | H.mem p}, D.values_transitive {p | H.mem p}⟩
  have truth := (evaluated.realize_refinementValidityFormula
    (evalAssignment {p | H.mem p} env) (fun i => ⟨env i, rfl⟩)).2 oldValid
  intro i
  exact eval_sharedConditionName_of_subset D BoundedFormula.refinementValidityFormula.toFormula
    env i.castSucc (T i) (valid i) (family i) H generic truth
    (eval_subset_familySet_of_code_subset H (T i) (valid i) (env i.castSucc).val (shape i))

end Name

end PartitionPilot.Forcing

end OAI
