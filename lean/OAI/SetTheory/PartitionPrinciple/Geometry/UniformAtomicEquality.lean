import OAI.SetTheory.PartitionPrinciple.Definability.BoundedAtomicEquality

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem collection_witness (collection : CollectionSchema M.sets)
    {n : Nat} (φ : SetFormula (n + 2)) (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {a : ZFSet.{u}} (ha : a ∈ M.sets)
    (existsWitness : ∀ x ∈ a, ∃ y ∈ M.sets, Realize M.sets φ (extend x (extend y params))) :
    ∃ b ∈ M.sets, ∀ x ∈ a, ∃ y ∈ b, Realize M.sets φ (extend x (extend y params)) := by
  obtain ⟨b, hb, spec⟩ := collection φ params members a ha (fun x _ hx => existsWitness x hx)
  refine ⟨b, hb, ?_⟩
  intro x hx
  obtain ⟨y, _, hy, rel⟩ := spec x (M.transitive ha hx) hx
  exact ⟨y, hy, rel⟩

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.SetFormula

def transitiveSetFormula {n : Nat} (t : Fin n) : SetFormula n :=
  .all (imp (.mem 0 t.succ) (.all (imp (.mem 0 1) (.mem 0 t.succ.succ))))

def transitiveCoverFormula : SetFormula 2 :=
  .conj (.mem 0 1) (transitiveSetFormula 1)

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_transitiveSetFormula {n : Nat} (t : Fin n) (env : Fin n → ZFSet.{u})
    (ht : env t ∈ M.sets) :
    Realize M.sets (transitiveSetFormula t) env ↔
      ∀ x ∈ env t, ∀ y ∈ x, y ∈ env t := by
  simp only [transitiveSetFormula, realize_imp, Realize]
  constructor
  · intro h x hx y hy
    exact h x (M.transitive ht hx) hx y (M.transitive (M.transitive ht hx) hy) hy
  · intro h x _ hx y _ hy
    exact h x hx y hy

theorem realize_transitiveCoverFormula (x T : ZFSet.{u}) (hT : T ∈ M.sets) :
    Realize M.sets transitiveCoverFormula (extend x (extend T Fin.elim0)) ↔
      x ∈ T ∧ ∀ z ∈ T, ∀ y ∈ z, y ∈ T := by
  change (x ∈ T ∧ Realize M.sets (transitiveSetFormula 1) _) ↔ _
  rw [M.realize_transitiveSetFormula 1 _ hT]
  rfl

theorem exists_transitiveCover
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets) :
    ∀ x ∈ M.sets, ∃ T ∈ M.sets, x ∈ T ∧ ∀ z ∈ T, ∀ y ∈ z, y ∈ T := by
  intro x
  induction x using ZFSet.inductionOn with
  | h x ih =>
    intro hx
    have witnesses : ∀ y ∈ x, ∃ T ∈ M.sets,
        Realize M.sets transitiveCoverFormula (extend y (extend T Fin.elim0)) := by
      intro y hy
      obtain ⟨T, hT, member, trans⟩ := ih y hy (M.transitive hx hy)
      exact ⟨T, hT, (M.realize_transitiveCoverFormula y T hT).2 ⟨member, trans⟩⟩
    obtain ⟨W, hW, covers⟩ := M.collection_witness collection transitiveCoverFormula Fin.elim0
      (fun i => Fin.elim0 i) hx witnesses
    let C := ZFSet.sep (fun T => Realize M.sets (transitiveSetFormula 0) (extend T Fin.elim0)) W
    have hC : C ∈ M.sets := M.separation_mem separation (transitiveSetFormula 0) Fin.elim0
      (fun i => Fin.elim0 i) hW
    have transC : ∀ T ∈ C, ∀ z ∈ T, ∀ y ∈ z, y ∈ T := by
      intro T hTC
      obtain ⟨hTW, spec⟩ := ZFSet.mem_sep.1 hTC
      exact (M.realize_transitiveSetFormula 0 (extend T Fin.elim0) (M.transitive hW hTW)).1 spec
    have included : x ⊆ ZFSet.sUnion C := by
      intro y hy
      obtain ⟨T, hTW, spec⟩ := covers y hy
      have hT := M.transitive hW hTW
      obtain ⟨member, trans⟩ := (M.realize_transitiveCoverFormula y T hT).1 spec
      exact ZFSet.mem_sUnion.2 ⟨T, ZFSet.mem_sep.2 ⟨hTW,
        (M.realize_transitiveSetFormula 0 (extend T Fin.elim0) hT).2 trans⟩, member⟩
    have transU : ∀ z ∈ ZFSet.sUnion C, ∀ y ∈ z, y ∈ ZFSet.sUnion C := by
      intro z hz y hy
      obtain ⟨T, hTC, hzT⟩ := ZFSet.mem_sUnion.1 hz
      exact ZFSet.mem_sUnion.2 ⟨T, hTC, transC T hTC z hzT y hy⟩
    let T := ({x, x} : ZFSet.{u}) ∪ ZFSet.sUnion C
    have hT : T ∈ M.sets := M.binary_union_mem pairing unions
      (M.unorderedPair_mem pairing hx hx) (M.union_mem unions hC)
    refine ⟨T, hT, ZFSet.mem_union.2 (Or.inl (ZFSet.mem_pair.2 (Or.inl rfl))), ?_⟩
    intro z hz y hy
    apply ZFSet.mem_union.2
    apply Or.inr
    rcases ZFSet.mem_union.1 hz with hz | hz
    · rcases ZFSet.mem_pair.1 hz with rfl | rfl
      · exact included hy
      · exact included hy
    · exact transU z hz y hy

theorem exists_pair_transitiveCover
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {x y : ZFSet.{u}} (hx : x ∈ M.sets) (hy : y ∈ M.sets) :
    ∃ T ∈ M.sets, x ∈ T ∧ y ∈ T ∧ ∀ z ∈ T, ∀ w ∈ z, w ∈ T := by
  obtain ⟨T, hT, pair, trans⟩ := M.exists_transitiveCover pairing unions separation collection
    ({x, y} : ZFSet.{u}) (M.unorderedPair_mem pairing hx hy)
  exact ⟨T, hT, trans _ pair x (ZFSet.mem_pair.2 (Or.inl rfl)),
    trans _ pair y (ZFSet.mem_pair.2 (Or.inr rfl)), trans⟩

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

def EqualityMeaning (D : Name.NameDomain s) {k : Nat} (E : SetFormula (k + 3))
    (constants : Fin k → ZFSet.{u}) : Prop :=
  ∀ (p : P) (σ τ : D.names),
    Realize M.sets E (extend (s.encode p) (extend σ.val.val (extend τ.val.val constants))) ↔
      Name.ForcesEq p σ.val τ.val

theorem realize_membershipFormula (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k m : Nat} (E : SetFormula (k + 3)) (c o : Fin k) (params : Fin k → Fin m)
    (pi si ti : Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params c) = s.carrier) (ho : env (params o) = s.conditionOrder)
    (atomic : M.EqualityMeaning s D E (fun j => env (params j)))
    (p : P) (σ τ : D.names) (hp : env pi = s.encode p)
    (hσ : env si = σ.val.val) (hτ : env ti = τ.val.val) :
    Realize M.sets (membershipFormula E c o params pi si ti) env ↔
      Name.ForcesMem p σ.val τ.val := by
  have hτM : env ti ∈ M.sets := hτ ▸ ground τ.val τ.property
  rw [membershipFormula, M.realize_allConditions s _ _ env carrier hc]
  change (∀ q : P, Realize M.sets _ (extend (s.encode q) env)) ↔
    ∀ q, q ≤ p → ∃ t, t ≤ q ∧ ∃ ν r,
      Name.Entry ν τ.val r ∧ t ≤ r ∧ Name.ForcesEq t σ.val ν
  apply forall_congr'
  intro q
  rw [realize_imp, M.realize_conditionLE s pairing carrier order 0 pi.succ (params o).succ
    (extend (s.encode q) env) q p rfl hp ho]
  apply forall_congr'
  intro _
  rw [M.realize_exConditions s (params c).succ _ (extend (s.encode q) env) carrier hc]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨v, hv, rest⟩ := (realize_ex M.sets _ _).1 ht
    obtain ⟨r, entry, tq, tr, eq⟩ := (M.realize_exConditions s (params c).succ.succ.succ _
      (extend v (extend (s.encode t) (extend (s.encode q) env))) carrier hc).1 rest
    let e := extend (s.encode r) (extend v (extend (s.encode t) (extend (s.encode q) env)))
    have raw := (M.realize_pairMembershipFormula pairing 1 0 ti.succ.succ.succ.succ e
      hv (M.transitive carrier (s.encode_mem r)) hτM).1 entry
    change ZFSet.pair v (s.encode r) ∈ env ti at raw
    rw [hτ] at raw
    let ν : Name s := ⟨v, Name.isName_of_pair_mem τ.val v r raw⟩
    have hν : ν ∈ D.names := D.children τ.property raw
    have forced := (realize_atomicApplication M.sets E
      (fun j => (params j).succ.succ.succ.succ) 2 si.succ.succ.succ.succ 1 e).1 eq
    change Realize M.sets E (extend (s.encode t) (extend (env si)
      (extend v (fun j => env (params j))))) at forced
    rw [hσ] at forced
    exact ⟨t, (M.realize_conditionLE s pairing carrier order 2 3
      (params o).succ.succ.succ.succ e t q rfl rfl ho).1 tq,
      ν, r, raw, (M.realize_conditionLE s pairing carrier order 2 0
        (params o).succ.succ.succ.succ e t r rfl rfl ho).1 tr,
      (atomic t σ ⟨ν, hν⟩).1 forced⟩
  · rintro ⟨t, tq, ν, r, entry, tr, forced⟩
    have hν : ν ∈ D.names := D.children τ.property entry
    refine ⟨t, ?_⟩
    rw [realize_ex]
    refine ⟨ν.val, ground ν hν, ?_⟩
    apply (M.realize_exConditions s (params c).succ.succ.succ _
      (extend ν.val (extend (s.encode t) (extend (s.encode q) env))) carrier hc).2
    let e := extend (s.encode r) (extend ν.val (extend (s.encode t) (extend (s.encode q) env)))
    refine ⟨r, ?_, ?_, ?_, ?_⟩
    · apply (M.realize_pairMembershipFormula pairing 1 0 ti.succ.succ.succ.succ e
        (ground ν hν) (M.transitive carrier (s.encode_mem r)) hτM).2
      change ZFSet.pair ν.val (s.encode r) ∈ env ti
      rw [hτ]
      exact entry
    · exact (M.realize_conditionLE s pairing carrier order 2 3
        (params o).succ.succ.succ.succ e t q rfl rfl ho).2 tq
    · exact (M.realize_conditionLE s pairing carrier order 2 0
        (params o).succ.succ.succ.succ e t r rfl rfl ho).2 tr
    · apply (realize_atomicApplication M.sets E
        (fun j => (params j).succ.succ.succ.succ) 2 si.succ.succ.succ.succ 1 e).2
      change Realize M.sets E (extend (s.encode t) (extend (env si)
        (extend ν.val (fun j => env (params j)))))
      rw [hσ]
      exact (atomic t σ ⟨ν, hν⟩).2 forced

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable {P : Type u} (s : Presentation P)

def namesInTransitiveSet (T : ZFSet.{u})
    (trans : ∀ {x y : ZFSet.{u}}, x ∈ T → y ∈ x → y ∈ T) : Name.NameDomain s :=
  nameDomain ⟨{x | x ∈ T}, trans⟩ s

variable (M : TransitiveGround.{u}) [Preorder P]

theorem exists_transitiveCover_atomicEquality
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (T : ZFSet.{u}) (hT : T ∈ M.sets)
    (trans : ∀ {x y : ZFSet.{u}}, x ∈ T → y ∈ x → y ∈ T) :
    ∃ S ∈ M.sets, ∀ p (σ τ : Name s), σ.val ∈ T → τ.val ∈ T →
      (Name.codedEqualityRelation s S p σ τ ↔ Name.ForcesEq p σ τ) := by
  let D := namesInTransitiveSet s T trans
  have ground : ∀ τ ∈ D.names, τ.val ∈ M.sets := fun _ hτ => M.transitive hT hτ
  obtain ⟨C, hC, pairBound⟩ := M.exists_pair_bound pairing unions powers hT hT
  obtain ⟨B, hB, tripleBound⟩ := M.exists_pair_bound pairing unions powers carrier hC
  have bound : ∀ p (σ τ : D.names),
      ZFSet.pair (s.encode p) (ZFSet.pair σ.val.val τ.val.val) ∈ B := by
    intro p σ τ
    exact tripleBound (s.encode p) (s.encode_mem p) _
      (pairBound σ.val.val σ.property τ.val.val τ.property)
  obtain ⟨S, hS, _, spec⟩ := M.exists_bounded_atomicEquality s D ground pairing unions powers
    separation carrier order B hB bound
  refine ⟨S, hS, ?_⟩
  intro p σ τ hσ hτ
  exact spec p ⟨σ, hσ⟩ ⟨τ, hτ⟩

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.SetFormula

def equalityCertificateFormula : SetFormula 3 := postfixedFormula equalityStateFormula

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem equalityCertificate_sound (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (S : ZFSet.{u}) (hS : S ∈ M.sets)
    (certificate : Realize M.sets equalityCertificateFormula (extend S (equalityParameters s)))
    (p : P) (σ τ : D.names) :
    Name.codedEqualityRelation s S p σ.val τ.val → Name.ForcesEq p σ.val τ.val := by
  have post : ∀ σ ∈ D.names, ∀ τ ∈ D.names, ∀ p,
      Name.codedEqualityRelation s S p σ τ → Name.EqualityStep (Name.codedEqualityRelation s S) p σ τ := by
    intro σ hσ τ hτ p rel
    have step := (realize_imp M.sets _ _ _).1
      (certificate _ (M.transitive hS rel)) rel
    exact (M.realize_equalityState_names s D ground pairing carrier order S hS
      p ⟨σ, hσ⟩ ⟨τ, hτ⟩).1 step
  exact Name.postfixed_equality_sound D (Name.codedEqualityRelation s S) post
    σ.val σ.property τ.val τ.property p

theorem exists_equalityState_fixedPoint
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (B : ZFSet.{u}) (hB : B ∈ M.sets) :
    ∃ S ∈ M.sets, S ⊆ B ∧
      definableOperator M.sets equalityStateFormula (equalityParameters s) B S = S := by
  have members : ∀ i, equalityParameters s i ∈ M.sets :=
    Fin.cases carrier (Fin.cases order (fun i => Fin.elim0 i))
  have mono : ∀ S ∈ M.sets, ∀ T ∈ M.sets, S ⊆ B → T ⊆ B → S ⊆ T →
      definableOperator M.sets equalityStateFormula (equalityParameters s) B S ⊆
        definableOperator M.sets equalityStateFormula (equalityParameters s) B T := by
    intro S hS T hT _ _ sub z hz
    obtain ⟨hzB, step⟩ := ZFSet.mem_sep.1 hz
    exact ZFSet.mem_sep.2 ⟨hzB,
      M.equalityState_mono s pairing carrier order (M.transitive hB hzB) hS hT sub step⟩
  obtain ⟨S, hS, bound, fixed, _⟩ := M.exists_greatest_definable_fixedPoint unions powers separation
    equalityStateFormula (equalityParameters s) members hB mono
  exact ⟨S, hS, bound, fixed⟩

theorem fixedPoint_equalityCertificate {B S : ZFSet.{u}} (hS : S ∈ M.sets) (bound : S ⊆ B)
    (fixed : definableOperator M.sets equalityStateFormula (equalityParameters s) B S = S) :
    Realize M.sets equalityCertificateFormula (extend S (equalityParameters s)) := by
  apply (M.realize_postfixedFormula equalityStateFormula (equalityParameters s) hS bound).2
  rw [fixed]

theorem equality_fixedPoint_iff (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {B S : ZFSet.{u}} (hS : S ∈ M.sets)
    (bound : ∀ p (σ τ : D.names), ZFSet.pair (s.encode p) (ZFSet.pair σ.val.val τ.val.val) ∈ B)
    (fixed : definableOperator M.sets equalityStateFormula (equalityParameters s) B S = S)
    (p : P) (σ τ : D.names) :
    Name.codedEqualityRelation s S p σ.val τ.val ↔ Name.ForcesEq p σ.val τ.val := by
  have step : ∀ σ ∈ D.names, ∀ τ ∈ D.names, ∀ p,
      Name.codedEqualityRelation s S p σ τ ↔ Name.EqualityStep (Name.codedEqualityRelation s S) p σ τ := by
    intro σ hσ τ hτ p
    change ZFSet.pair (s.encode p) (ZFSet.pair σ.val τ.val) ∈ S ↔ _
    calc
      _ ↔ ZFSet.pair (s.encode p) (ZFSet.pair σ.val τ.val) ∈
          definableOperator M.sets equalityStateFormula (equalityParameters s) B S := by rw [fixed]
      _ ↔ _ := by
        rw [definableOperator, ZFSet.mem_sep,
          M.realize_equalityState_names s D ground pairing carrier order S hS p ⟨σ, hσ⟩ ⟨τ, hτ⟩]
        exact and_iff_right (bound p ⟨σ, hσ⟩ ⟨τ, hτ⟩)
  exact Name.fixed_equality_iff D (Name.codedEqualityRelation s S) step σ.property τ.property p

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem exists_atomicEquality_certificate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (p : P) (σ τ : Name s) (hσ : σ.val ∈ M.sets) (hτ : τ.val ∈ M.sets)
    (forced : Name.ForcesEq p σ τ) :
    ∃ S ∈ M.sets, Realize M.sets equalityCertificateFormula (extend S (equalityParameters s)) ∧
      Name.codedEqualityRelation s S p σ τ := by
  obtain ⟨T, hT, σT, τT, trans⟩ := M.exists_pair_transitiveCover pairing unions separation collection hσ hτ
  let D := namesInTransitiveSet s T (fun hx hy => trans _ hx _ hy)
  have ground : ∀ ν ∈ D.names, ν.val ∈ M.sets := fun _ hν => M.transitive hT hν
  obtain ⟨C, hC, pairBound⟩ := M.exists_pair_bound pairing unions powers hT hT
  obtain ⟨B, hB, tripleBound⟩ := M.exists_pair_bound pairing unions powers carrier hC
  have bound : ∀ q (ν ρ : D.names),
      ZFSet.pair (s.encode q) (ZFSet.pair ν.val.val ρ.val.val) ∈ B := by
    intro q ν ρ
    exact tripleBound (s.encode q) (s.encode_mem q) _
      (pairBound ν.val.val ν.property ρ.val.val ρ.property)
  obtain ⟨S, hS, hSB, fixed⟩ := M.exists_equalityState_fixedPoint s pairing unions powers separation
    carrier order B hB
  exact ⟨S, hS, M.fixedPoint_equalityCertificate s hS hSB fixed,
    (M.equality_fixedPoint_iff s D ground pairing carrier order hS bound fixed p ⟨σ, σT⟩ ⟨τ, τT⟩).2 forced⟩

theorem forcesEq_iff_exists_certificate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (p : P) (σ τ : Name s) (hσ : σ.val ∈ M.sets) (hτ : τ.val ∈ M.sets) :
    Name.ForcesEq p σ τ ↔
      ∃ S ∈ M.sets, Realize M.sets equalityCertificateFormula (extend S (equalityParameters s)) ∧
        Name.codedEqualityRelation s S p σ τ := by
  constructor
  · exact M.exists_atomicEquality_certificate s pairing unions powers separation collection carrier order
      p σ τ hσ hτ
  · rintro ⟨S, hS, certificate, rel⟩
    exact M.equalityCertificate_sound s (M.nameDomain s) (fun _ h => h)
      pairing carrier order S hS certificate p ⟨σ, hσ⟩ ⟨τ, hτ⟩ rel

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.SetFormula

universe u v

theorem map_empty {A : Type u} {B : Type v} (f : A → B) :
    (fun i : Fin 0 => f (Fin.elim0 i)) = (Fin.elim0 : Fin 0 → B) := by
  funext i
  exact Fin.elim0 i

def uniformEqualityFormula : SetFormula 5 :=
  ex (.conj (atomicApplication equalityCertificateFormula Fin.elim0 0 4 5)
    (tripleMembershipFormula 1 2 3 0))

def liftedEqualityFormula {k : Nat} (c o : Fin k) : SetFormula (k + 3) :=
  atomicApplication uniformEqualityFormula
    (extend c.succ.succ.succ (extend o.succ.succ.succ Fin.elim0)) 0 1 2

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_uniformEqualityFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (p : P) (σ τ : Name s) (hσ : σ.val ∈ M.sets) (hτ : τ.val ∈ M.sets) :
    Realize M.sets uniformEqualityFormula
      (extend (s.encode p) (extend σ.val (extend τ.val (equalityParameters s)))) ↔
      Name.ForcesEq p σ τ := by
  rw [M.forcesEq_iff_exists_certificate s pairing unions powers separation collection carrier order p σ τ hσ hτ,
    uniformEqualityFormula, realize_ex]
  apply exists_congr
  intro S
  apply and_congr_right
  intro hS
  let env := extend S (extend (s.encode p) (extend σ.val (extend τ.val (equalityParameters s))))
  change (Realize M.sets _ env ∧ Realize M.sets _ env) ↔ _
  rw [realize_atomicApplication,
    M.realize_tripleMembershipFormula pairing 1 2 3 0 env
      (M.transitive carrier (s.encode_mem p)) hσ hτ hS, map_empty]
  rfl

theorem equalityMeaning_uniform (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) :
    M.EqualityMeaning s D uniformEqualityFormula (equalityParameters s) := by
  intro p σ τ
  exact M.realize_uniformEqualityFormula s pairing unions powers separation collection carrier order
    p σ.val τ.val (ground σ.val σ.property) (ground τ.val τ.property)

theorem equalityMeaning_lifted (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k : Nat} (c o : Fin k) (constants : Fin k → ZFSet.{u})
    (hc : constants c = s.carrier) (ho : constants o = s.conditionOrder) :
    M.EqualityMeaning s D (liftedEqualityFormula c o) constants := by
  intro p σ τ
  rw [liftedEqualityFormula, realize_atomicApplication, map_extend, map_extend, map_empty]
  change Realize M.sets uniformEqualityFormula
    (extend (s.encode p) (extend σ.val.val (extend τ.val.val
      (extend (constants c) (extend (constants o) Fin.elim0))))) ↔ _
  rw [hc, ho]
  exact M.realize_uniformEqualityFormula s pairing unions powers separation collection carrier order
    p σ.val τ.val (ground σ.val σ.property) (ground τ.val τ.property)

end PartitionPilot.Forcing.TransitiveGround

end OAI
