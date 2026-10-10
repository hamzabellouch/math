import OAI.SetTheory.PartitionPrinciple.Forcing.UniformGroundNames

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

def ordinaryGroundPrimitives {k : Nat} (c o : Fin k) : ForcingPrimitives k :=
  withGroundEquality c o (liftedNameFormula c)

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_ordinaryGroundForcing
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k n m : Nat} (c o : Fin k) (φ : SetFormula n)
    (params : Fin k → Fin m) (pi : Fin m) (names : Fin n → Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params c) = s.carrier) (ho : env (params o) = s.conditionOrder)
    (p : P) (nameEnv : Assignment (M.nameDomain s) n) (hp : env pi = s.encode p)
    (hnames : ∀ i, env (names i) = (nameEnv i).val.val) :
    Realize M.sets (forcingTranslation (ordinaryGroundPrimitives c o) φ params pi names) env ↔
      Forces (M.nameDomain s) φ nameEnv p :=
  M.realize_forcingWithGroundEquality s (M.nameDomain s) (fun _ h => h) pairing unions powers
    separation collection carrier order c o (liftedNameFormula c) φ params pi names env hc ho
    (M.domainMeaning_liftedNames s pairing unions powers separation collection carrier c _ hc)
    p nameEnv hp hnames

theorem ordinaryForcingSet_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {n : Nat} (φ : SetFormula n) (nameEnv : Assignment (M.nameDomain s) n) :
    s.subset (fun p => Forces (M.nameDomain s) φ nameEnv p) ∈ M.sets := by
  let context := extend s.carrier (extend s.conditionOrder (fun i => (nameEnv i).val.val))
  let params : Fin 2 → Fin (n + 2) := extend 0 (extend 1 Fin.elim0)
  have members : ∀ i, context i ∈ M.sets :=
    Fin.cases carrier (Fin.cases order (fun i => (nameEnv i).property))
  apply M.forcingSet_mem_withGroundEquality s (M.nameDomain s) (fun _ h => h) pairing unions powers
    separation collection carrier order 0 1 (liftedNameFormula 0) φ params (fun i => i.succ.succ)
    context members rfl rfl
  · exact M.domainMeaning_liftedNames s pairing unions powers separation collection carrier 0 _ rfl
  · exact fun _ => rfl

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.SetFormula

def candidateForcingFormula {n : Nat} (phi : SetFormula (n + 1)) : SetFormula (n + 4) :=
  ex (.conj (.mem 0 2)
    (forcingTranslation (ordinaryGroundPrimitives (0 : Fin 2) 1) phi
      (extend 3 (extend 4 Fin.elim0)) 1
      (extend 0 (fun i => i.succ.succ.succ.succ.succ))))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
include pairing unions powers separation collection carrier order

theorem realize_candidateForcingFormula {n : Nat} (phi : SetFormula (n + 1))
    (env : Assignment (M.nameDomain s) n) (W : ZFSet.{u})
    (valid : ∀ z ∈ W, IsName s z) (p : P) :
    Realize M.sets (candidateForcingFormula phi)
      (extend (s.encode p) (extend W (extend s.carrier
        (extend s.conditionOrder (fun i => (env i).val.val))))) ↔
      ∃ tau : (M.nameDomain s).names, tau.val.val ∈ W ∧
        Forces (M.nameDomain s) phi (extend tau env) p := by
  let params := extend (s.encode p) (extend W (extend s.carrier
    (extend s.conditionOrder (fun i => (env i).val.val))))
  change Realize M.sets (candidateForcingFormula phi) params ↔ _
  rw [candidateForcingFormula, realize_ex]
  constructor
  · rintro ⟨z, hz, member, forced⟩
    change z ∈ W at member
    let tau : (M.nameDomain s).names := ⟨⟨z, valid z member⟩, hz⟩
    refine ⟨tau, member, ?_⟩
    exact (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
      carrier order 0 1 phi (extend 3 (extend 4 Fin.elim0)) 1
      (extend 0 (fun i => i.succ.succ.succ.succ.succ)) (extend z params)
      rfl rfl p (extend tau env) rfl (Fin.cases rfl (fun _ => rfl))).1 forced
  · rintro ⟨tau, member, forced⟩
    refine ⟨tau.val.val, tau.property, member, ?_⟩
    exact (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
      carrier order 0 1 phi (extend 3 (extend 4 Fin.elim0)) 1
      (extend 0 (fun i => i.succ.succ.succ.succ.succ)) (extend tau.val.val params)
      rfl rfl p (extend tau env) rfl (Fin.cases rfl (fun _ => rfl))).2 forced

theorem candidateForcingSet_mem {n : Nat} (phi : SetFormula (n + 1))
    (env : Assignment (M.nameDomain s) n) (W : ZFSet.{u}) (ground : W ∈ M.sets)
    (valid : ∀ z ∈ W, IsName s z) :
    s.subset (fun p => ∃ tau : (M.nameDomain s).names, tau.val.val ∈ W ∧
      Forces (M.nameDomain s) phi (extend tau env) p) ∈ M.sets := by
  let params := extend W (extend s.carrier (extend s.conditionOrder (fun i => (env i).val.val)))
  have equal : s.subset (fun p => ∃ tau : (M.nameDomain s).names, tau.val.val ∈ W ∧
      Forces (M.nameDomain s) phi (extend tau env) p) =
      ZFSet.sep (fun z => Realize M.sets (candidateForcingFormula phi) (extend z params)) s.carrier := by
    apply ZFSet.ext
    intro z
    rw [s.mem_subset, ZFSet.mem_sep]
    constructor
    · rintro ⟨p, forced, rfl⟩
      exact ⟨s.encode_mem p, (M.realize_candidateForcingFormula s pairing unions powers separation
        collection carrier order phi env W valid p).2 forced⟩
    · rintro ⟨member, truth⟩
      obtain ⟨p, rfl⟩ := (s.mem_carrier z).1 member
      exact ⟨p, (M.realize_candidateForcingFormula s pairing unions powers separation collection
        carrier order phi env W valid p).1 truth, rfl⟩
  rw [equal]
  exact M.separation_mem separation (candidateForcingFormula phi) params
    (Fin.cases ground (Fin.cases carrier (Fin.cases order (fun i => (env i).property)))) carrier

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

def RenameStep (f : P → P) (R : Name s → Name s → Prop) (σ τ : Name s) : Prop :=
  (∀ ν p, Entry ν σ p → ∃ ρ, Entry ρ τ (f p) ∧ R ν ρ) ∧
  (∀ ρ q, Entry ρ τ q → ∃ ν p, Entry ν σ p ∧ f p = q ∧ R ν ρ)

theorem rename_eq_step (f : P → P) (σ τ : Name s) :
    rename s f σ = τ ↔ RenameStep f (fun ν ρ => rename s f ν = ρ) σ τ := by
  constructor
  · intro eq
    constructor
    · intro ν p entry
      refine ⟨rename s f ν, ?_, rfl⟩
      rw [← eq, entry_rename]
      exact ⟨ν, p, entry, rfl, rfl⟩
    · intro ρ q entry
      rw [← eq, entry_rename] at entry
      obtain ⟨ν, p, old, image, condition⟩ := entry
      exact ⟨ν, p, old, condition, image⟩
  · rintro ⟨left, right⟩
    apply ext
    intro ρ q
    rw [entry_rename]
    constructor
    · rintro ⟨ν, p, entry, image, condition⟩
      obtain ⟨χ, matched, hχ⟩ := left ν p entry
      have eq : χ = ρ := hχ.symm.trans image
      simpa only [eq, condition] using matched
    · intro entry
      obtain ⟨ν, p, old, condition, image⟩ := right ρ q entry
      exact ⟨ν, p, old, image, condition⟩

theorem rename_postfixed_sound (D : NameDomain s) (f : P → P) (R : Name s → Name s → Prop)
    (post : ∀ σ ∈ D.names, ∀ τ ∈ D.names, R σ τ → RenameStep f R σ τ) :
    ∀ σ ∈ D.names, ∀ τ ∈ D.names, R σ τ → rename s f σ = τ := by
  intro σ
  induction σ using inductionOn with
  | step σ ih =>
    intro hσ τ hτ rel
    obtain ⟨left, right⟩ := post σ hσ τ hτ rel
    apply (rename_eq_step f σ τ).2
    constructor
    · intro ν p entry
      obtain ⟨ρ, matched, child⟩ := left ν p entry
      exact ⟨ρ, matched, ih ν p entry (D.children hσ entry) ρ (D.children hτ matched) child⟩
    · intro ρ q entry
      obtain ⟨ν, p, old, condition, child⟩ := right ρ q entry
      exact ⟨ν, p, old, condition, ih ν p old (D.children hσ old) ρ (D.children hτ entry) child⟩

theorem rename_prefixed_complete (D : NameDomain s) (f : P → P) (R : Name s → Name s → Prop)
    (pre : ∀ σ ∈ D.names, ∀ τ ∈ D.names, RenameStep f R σ τ → R σ τ) :
    ∀ σ ∈ D.names, ∀ τ ∈ D.names, rename s f σ = τ → R σ τ := by
  intro σ
  induction σ using inductionOn with
  | step σ ih =>
    intro hσ τ hτ eq
    obtain ⟨left, right⟩ := (rename_eq_step f σ τ).1 eq
    apply pre σ hσ τ hτ
    constructor
    · intro ν p entry
      obtain ⟨ρ, matched, child⟩ := left ν p entry
      exact ⟨ρ, matched, ih ν p entry (D.children hσ entry) ρ (D.children hτ matched) child⟩
    · intro ρ q entry
      obtain ⟨ν, p, old, condition, child⟩ := right ρ q entry
      exact ⟨ν, p, old, condition, ih ν p old (D.children hσ old) ρ (D.children hτ entry) child⟩

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace SetFormula

def ordinaryEqualityDecisionFormula {n : Nat}
    (carrier order condition sigma tau : Fin n) : SetFormula n :=
  disj
    (forcingTranslation (ordinaryGroundPrimitives (0 : Fin 2) 1) (.equal 0 1)
      (extend carrier (extend order Fin.elim0)) condition (extend sigma (extend tau Fin.elim0)))
    (forcingTranslation (ordinaryGroundPrimitives (0 : Fin 2) 1) (.neg (.equal 0 1))
      (extend carrier (extend order Fin.elim0)) condition (extend sigma (extend tau Fin.elim0)))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def ordinaryEqualityDecisions (Q order sigma tau : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => Realize M.sets (ordinaryEqualityDecisionFormula 1 2 0 3 4)
    (extend p ![Q, order, sigma, tau])) Q

theorem ordinaryEqualityDecisions_subset (Q order sigma tau : ZFSet.{u}) :
    M.ordinaryEqualityDecisions Q order sigma tau ⊆ Q :=
  fun _ h => (ZFSet.mem_sep.1 h).1

variable {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_ordinaryEqualityDecisionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {n : Nat} (ci oi pi si ti : Fin n) (env : Fin n → ZFSet.{u})
    (sigma tau : (M.nameDomain s).names) (p : P)
    (hc : env ci = s.carrier) (ho : env oi = s.conditionOrder)
    (hp : env pi = s.encode p) (hs : env si = sigma.val.val) (ht : env ti = tau.val.val) :
    Realize M.sets (ordinaryEqualityDecisionFormula ci oi pi si ti) env ↔
      Name.ForcesEq p sigma.val tau.val ∨ ∀ q, q ≤ p → ¬ Name.ForcesEq q sigma.val tau.val := by
  rw [ordinaryEqualityDecisionFormula, realize_disj]
  let names : Assignment (M.nameDomain s) 2 := extend sigma (extend tau Fin.elim0)
  have meaning (phi : SetFormula 2) := M.realize_ordinaryGroundForcing s pairing unions powers
    separation collection carrier order (0 : Fin 2) 1 phi (extend ci (extend oi Fin.elim0)) pi
    (extend si (extend ti Fin.elim0)) env hc ho p names hp
    (Fin.cases hs (Fin.cases ht (fun i => Fin.elim0 i)))
  exact or_congr (meaning (.equal 0 1)) (meaning (.neg (.equal 0 1)))

theorem ordinaryEqualityDecisions_entry
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (sigma tau : (M.nameDomain s).names) (p : P) :
    s.encode p ∈ M.ordinaryEqualityDecisions s.carrier s.conditionOrder sigma.val.val tau.val.val ↔
      Name.ForcesEq p sigma.val tau.val ∨ ∀ q, q ≤ p → ¬ Name.ForcesEq q sigma.val tau.val := by
  rw [ordinaryEqualityDecisions, ZFSet.mem_sep, and_iff_right (s.encode_mem p)]
  exact M.realize_ordinaryEqualityDecisionFormula s pairing unions powers separation collection
    carrier order 1 2 0 3 4 _ sigma tau p rfl rfl rfl rfl rfl

theorem ordinaryEqualityDecisions_dense
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (sigma tau : (M.nameDomain s).names) :
    ∀ p ∈ s.carrier, ∃ q ∈ M.ordinaryEqualityDecisions s.carrier s.conditionOrder
      sigma.val.val tau.val.val, ZFSet.pair q p ∈ s.conditionOrder := by
  intro z hz
  obtain ⟨p, rfl⟩ := (s.mem_carrier z).1 hz
  obtain ⟨q, below, decided⟩ := decisionWitness_dense (M.nameDomain s) (.equal 0 1)
    (extend sigma (extend tau Fin.elim0)) p
  exact ⟨s.encode q,
    (M.ordinaryEqualityDecisions_entry s pairing unions powers separation collection carrier order
      sigma tau q).2 decided, (s.pair_mem_conditionOrder q p).2 below⟩

end TransitiveGround




namespace SetFormula

def ordinaryMembershipDecisionFormula {n : Nat}
    (carrier order condition sigma tau : Fin n) : SetFormula n :=
  disj
    (forcingTranslation (ordinaryGroundPrimitives (0 : Fin 2) 1) (.mem 0 1)
      (extend carrier (extend order Fin.elim0)) condition (extend sigma (extend tau Fin.elim0)))
    (forcingTranslation (ordinaryGroundPrimitives (0 : Fin 2) 1) (.neg (.mem 0 1))
      (extend carrier (extend order Fin.elim0)) condition (extend sigma (extend tau Fin.elim0)))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def ordinaryMembershipDecisions (Q order sigma tau : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => Realize M.sets (ordinaryMembershipDecisionFormula 1 2 0 3 4)
    (extend p ![Q, order, sigma, tau])) Q

theorem ordinaryMembershipDecisions_subset (Q order sigma tau : ZFSet.{u}) :
    M.ordinaryMembershipDecisions Q order sigma tau ⊆ Q :=
  fun _ h => (ZFSet.mem_sep.1 h).1

variable {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_ordinaryMembershipDecisionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {n : Nat} (ci oi pi si ti : Fin n) (env : Fin n → ZFSet.{u})
    (sigma tau : (M.nameDomain s).names) (p : P)
    (hc : env ci = s.carrier) (ho : env oi = s.conditionOrder)
    (hp : env pi = s.encode p) (hs : env si = sigma.val.val) (ht : env ti = tau.val.val) :
    Realize M.sets (ordinaryMembershipDecisionFormula ci oi pi si ti) env ↔
      Name.ForcesMem p sigma.val tau.val ∨ ∀ q, q ≤ p → ¬ Name.ForcesMem q sigma.val tau.val := by
  rw [ordinaryMembershipDecisionFormula, realize_disj]
  let names : Assignment (M.nameDomain s) 2 := extend sigma (extend tau Fin.elim0)
  have meaning (phi : SetFormula 2) := M.realize_ordinaryGroundForcing s pairing unions powers
    separation collection carrier order (0 : Fin 2) 1 phi (extend ci (extend oi Fin.elim0)) pi
    (extend si (extend ti Fin.elim0)) env hc ho p names hp
    (Fin.cases hs (Fin.cases ht (fun i => Fin.elim0 i)))
  exact or_congr (meaning (.mem 0 1)) (meaning (.neg (.mem 0 1)))

theorem ordinaryMembershipDecisions_entry
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (sigma tau : (M.nameDomain s).names) (p : P) :
    s.encode p ∈ M.ordinaryMembershipDecisions s.carrier s.conditionOrder sigma.val.val tau.val.val ↔
      Name.ForcesMem p sigma.val tau.val ∨ ∀ q, q ≤ p → ¬ Name.ForcesMem q sigma.val tau.val := by
  rw [ordinaryMembershipDecisions, ZFSet.mem_sep, and_iff_right (s.encode_mem p)]
  exact M.realize_ordinaryMembershipDecisionFormula s pairing unions powers separation collection
    carrier order 1 2 0 3 4 _ sigma tau p rfl rfl rfl rfl rfl

theorem ordinaryMembershipDecisions_dense
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (sigma tau : (M.nameDomain s).names) :
    ∀ p ∈ s.carrier, ∃ q ∈ M.ordinaryMembershipDecisions s.carrier s.conditionOrder
      sigma.val.val tau.val.val, ZFSet.pair q p ∈ s.conditionOrder := by
  intro z hz
  obtain ⟨p, rfl⟩ := (s.mem_carrier z).1 hz
  obtain ⟨q, below, decided⟩ := decisionWitness_dense (M.nameDomain s) (.mem 0 1)
    (extend sigma (extend tau Fin.elim0)) p
  exact ⟨s.encode q,
    (M.ordinaryMembershipDecisions_entry s pairing unions powers separation collection carrier order
      sigma tau q).2 decided, (s.pair_mem_conditionOrder q p).2 below⟩

end TransitiveGround
end PartitionPilot.Forcing

end OAI
