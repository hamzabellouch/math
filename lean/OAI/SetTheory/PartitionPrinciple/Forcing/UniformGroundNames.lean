import OAI.SetTheory.PartitionPrinciple.Geometry.UniformAtomicEquality

namespace OAI


namespace PartitionPilot.Forcing

open SetRealization
universe u
variable {P : Type u} (s : Presentation P)

def NameCodeStep (S x : ZFSet.{u}) : Prop :=
  ∀ z ∈ x, ∃ y ∈ S, ∃ p, z = ZFSet.pair y (s.encode p)

theorem nameCodeStep_mono {S T x : ZFSet.{u}} (sub : S ⊆ T) (h : NameCodeStep s S x) :
    NameCodeStep s T x := by
  intro z hz
  obtain ⟨y, hy, p, shape⟩ := h z hz
  exact ⟨y, sub hy, p, shape⟩

theorem nameCodePostfixed_sound (S : ZFSet.{u}) (post : ∀ x ∈ S, NameCodeStep s S x) :
    ∀ x ∈ S, IsName s x := by
  intro x
  apply (InvImage.wf (fun z : ZFSet.{u} => ZFSet.rank z) wellFounded_lt).induction x
  intro x ih hx
  apply IsName.mk
  · intro z hz
    obtain ⟨y, _, p, shape⟩ := post x hx z hz
    exact ⟨y, p, shape⟩
  · intro y p entry
    obtain ⟨v, hv, q, shape⟩ := post x hx _ entry
    have eq := (ZFSet.pair_inj.1 shape).1
    have hy : y ∈ S := eq ▸ hv
    have lt : ZFSet.rank y < ZFSet.rank x :=
      (ZFSet.rank_lt_of_mem (ZFSet.mem_singleton.2 rfl : y ∈ ({y} : ZFSet.{u}))).trans
        ((ZFSet.rank_lt_of_mem (ZFSet.mem_pair.2 (Or.inl rfl) :
          ({y} : ZFSet.{u}) ∈ ZFSet.pair y (s.encode p))).trans (ZFSet.rank_lt_of_mem entry))
    exact ih y lt hy

theorem nameCodePrefixed_complete (D : Name.NameDomain s) (S : ZFSet.{u})
    (pre : ∀ τ ∈ D.names, NameCodeStep s S τ.val → τ.val ∈ S) :
    ∀ τ ∈ D.names, τ.val ∈ S := by
  intro τ
  induction τ using Name.inductionOn with
  | step τ ih =>
    intro hτ
    apply pre τ hτ
    intro z hz
    obtain ⟨ν, p, rfl⟩ := Name.entries_cover τ hz
    exact ⟨ν.val, ih ν p hz (D.children hτ hz), p, rfl⟩

namespace SetFormula

def nameCodeStepFormula : SetFormula 3 :=
  .all (imp (.mem 0 1) (ex (.conj (.mem 0 3)
    (exConditions 4 (orderedPairFormula 2 1 0)))))

def nameCertificateFormula : SetFormula 2 := postfixedFormula nameCodeStepFormula

end SetFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_nameCodeStepFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (carrier : s.carrier ∈ M.sets)
    (x S : ZFSet.{u}) (hx : x ∈ M.sets) (hS : S ∈ M.sets) :
    Realize M.sets nameCodeStepFormula (extend x (extend S (extend s.carrier Fin.elim0))) ↔
      NameCodeStep s S x := by
  let env := extend x (extend S (extend s.carrier Fin.elim0))
  change (∀ z ∈ M.sets, Realize M.sets _ (extend z env)) ↔ _
  constructor
  · intro h z hz
    obtain ⟨y, hy, member, rest⟩ := (realize_ex M.sets _ _).1
      ((realize_imp M.sets _ _ _).1 (h z (M.transitive hx hz)) hz)
    obtain ⟨p, shape⟩ := (M.realize_exConditions s 4 _ (extend y (extend z env)) carrier rfl).1 rest
    exact ⟨y, member, p,
      (M.realize_orderedPairFormula pairing 2 1 0 (extend (s.encode p) (extend y (extend z env)))
        (M.transitive hx hz) hy (M.transitive carrier (s.encode_mem p))).1 shape⟩
  · intro h z hzM
    apply (realize_imp M.sets _ _ _).2
    intro hz
    obtain ⟨y, hy, p, shape⟩ := h z hz
    rw [realize_ex]
    refine ⟨y, M.transitive hS hy, hy, ?_⟩
    apply (M.realize_exConditions s 4 _ (extend y (extend z env)) carrier rfl).2
    exact ⟨p, (M.realize_orderedPairFormula pairing 2 1 0
      (extend (s.encode p) (extend y (extend z env))) hzM (M.transitive hS hy)
      (M.transitive carrier (s.encode_mem p))).2 shape⟩

theorem nameCertificate_sound
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (carrier : s.carrier ∈ M.sets)
    {S : ZFSet.{u}} (hS : S ∈ M.sets)
    (certificate : Realize M.sets nameCertificateFormula (extend S (extend s.carrier Fin.elim0))) :
    ∀ x ∈ S, IsName s x := by
  apply nameCodePostfixed_sound s S
  intro x hx
  exact (M.realize_nameCodeStepFormula s pairing carrier x S (M.transitive hS hx) hS).1
    ((realize_imp M.sets _ _ _).1 (certificate x (M.transitive hS hx)) hx)

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.SetFormula

universe u

structure ForcingPrimitives (k : Nat) where
  carrier : Fin k
  order : Fin k
  equality : SetFormula (k + 3)
  domain : SetFormula (k + 1)

def domainApplication {k m : Nat} (N : SetFormula (k + 1))
    (params : Fin k → Fin m) (x : Fin m) : SetFormula m := reindex (extend x params) N

theorem realize_domainApplication (U : Set ZFSet.{u}) {k m : Nat}
    (N : SetFormula (k + 1)) (params : Fin k → Fin m) (x : Fin m) (env : Fin m → ZFSet.{u}) :
    Realize U (domainApplication N params x) env ↔
      Realize U N (extend (env x) (fun i => env (params i))) := by
  rw [domainApplication, realize_reindex, map_extend]

def forcingTranslation {k : Nat} (A : ForcingPrimitives k) :
    {n m : Nat} → SetFormula n → (Fin k → Fin m) → Fin m → (Fin n → Fin m) → SetFormula m
  | _, _, .equal i j, params, p, names => atomicApplication A.equality params p (names i) (names j)
  | _, _, .mem i j, params, p, names =>
      membershipFormula A.equality A.carrier A.order params p (names i) (names j)
  | _, _, .neg φ, params, p, names =>
      allConditions (params A.carrier) <|
        imp (pairMembershipFormula 0 p.succ (params A.order).succ) <|
        .neg (forcingTranslation A φ (fun j => (params j).succ) 0 (fun i => (names i).succ))
  | _, _, .conj φ ψ, params, p, names =>
      .conj (forcingTranslation A φ params p names) (forcingTranslation A ψ params p names)
  | _, _, .all φ, params, p, names =>
      .all <| imp (domainApplication A.domain (fun j => (params j).succ) 0) <|
        forcingTranslation A φ (fun j => (params j).succ) p.succ
          (extend 0 (fun i => (names i).succ))

end PartitionPilot.Forcing.SetFormula



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

def DomainMeaning (D : Name.NameDomain s) {k : Nat} (N : SetFormula (k + 1))
    (constants : Fin k → ZFSet.{u}) : Prop :=
  ∀ x ∈ M.sets, Realize M.sets N (extend x constants) ↔ ∃ τ : D.names, τ.val.val = x

theorem realize_forcingTranslation (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k n : Nat} (A : ForcingPrimitives k) (φ : SetFormula n) :
    ∀ {m} (params : Fin k → Fin m) (pi : Fin m) (names : Fin n → Fin m)
      (env : Fin m → ZFSet.{u}),
      env (params A.carrier) = s.carrier → env (params A.order) = s.conditionOrder →
      M.EqualityMeaning s D A.equality (fun j => env (params j)) →
      M.DomainMeaning s D A.domain (fun j => env (params j)) →
      ∀ (p : P) (nameEnv : Assignment D n), env pi = s.encode p →
      (∀ i, env (names i) = (nameEnv i).val.val) →
      (Realize M.sets (forcingTranslation A φ params pi names) env ↔ Forces D φ nameEnv p) := by
  induction φ with
  | equal i j =>
    intro m params pi names env hc ho atomic domain p nameEnv hp hnames
    change Realize M.sets (atomicApplication A.equality params pi (names i) (names j)) env ↔ _
    rw [realize_atomicApplication, hp, hnames i, hnames j]
    exact atomic p (nameEnv i) (nameEnv j)
  | mem i j =>
    intro m params pi names env hc ho atomic domain p nameEnv hp hnames
    exact M.realize_membershipFormula s D ground pairing carrier order A.equality
      A.carrier A.order params pi (names i) (names j) env hc ho atomic p
      (nameEnv i) (nameEnv j) hp (hnames i) (hnames j)
  | neg φ ih =>
    intro m params pi names env hc ho atomic domain p nameEnv hp hnames
    change Realize M.sets (allConditions _ _) env ↔
      ∀ q, q ≤ p → ¬ Forces D φ nameEnv q
    rw [M.realize_allConditions s (params A.carrier) _ env carrier hc]
    apply forall_congr'
    intro q
    rw [realize_imp, M.realize_conditionLE s pairing carrier order 0 pi.succ
      (params A.order).succ (extend (s.encode q) env) q p rfl hp ho]
    apply forall_congr'
    intro _
    exact not_congr (ih (fun j => (params j).succ) 0 (fun i => (names i).succ)
      (extend (s.encode q) env) hc ho atomic domain q nameEnv rfl hnames)
  | conj φ ψ ihφ ihψ =>
    intro m params pi names env hc ho atomic domain p nameEnv hp hnames
    exact and_congr (ihφ params pi names env hc ho atomic domain p nameEnv hp hnames)
      (ihψ params pi names env hc ho atomic domain p nameEnv hp hnames)
  | all φ ih =>
    intro m params pi names env hc ho atomic domain p nameEnv hp hnames
    change (∀ x ∈ M.sets, Realize M.sets (imp
      (domainApplication A.domain (fun j => (params j).succ) 0)
      (forcingTranslation A φ (fun j => (params j).succ) pi.succ
        (extend 0 (fun i => (names i).succ)))) (extend x env)) ↔
      ∀ τ : D.names, Forces D φ (extend τ nameEnv) p
    constructor
    · intro h τ
      have hx := ground τ.val τ.property
      have belongs : Realize M.sets (domainApplication A.domain (fun j => (params j).succ) 0)
          (extend τ.val.val env) :=
        (realize_domainApplication M.sets A.domain _ _ _).2 ((domain τ.val.val hx).2 ⟨τ, rfl⟩)
      have body := (realize_imp M.sets _ _ _).1 (h τ.val.val hx) belongs
      apply (ih (fun j => (params j).succ) pi.succ (extend 0 (fun i => (names i).succ))
        (extend τ.val.val env) hc ho atomic domain p (extend τ nameEnv) hp ?_).1 body
      intro i
      exact Fin.cases rfl (fun j => hnames j) i
    · intro h x hx
      rw [realize_imp, realize_domainApplication]
      intro belongs
      obtain ⟨τ, rfl⟩ := (domain x hx).1 belongs
      apply (ih (fun j => (params j).succ) pi.succ (extend 0 (fun i => (names i).succ))
        (extend τ.val.val env) hc ho atomic domain p (extend τ nameEnv) hp ?_).2 (h τ)
      intro i
      exact Fin.cases rfl (fun j => hnames j) i






theorem forcingSet_mem (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (separation : SeparationSchema M.sets)
    {k n m : Nat} (A : ForcingPrimitives k) (φ : SetFormula n)
    (params : Fin k → Fin m) (names : Fin n → Fin m) (context : Fin m → ZFSet.{u})
    (members : ∀ i, context i ∈ M.sets)
    (hc : context (params A.carrier) = s.carrier)
    (ho : context (params A.order) = s.conditionOrder)
    (atomic : M.EqualityMeaning s D A.equality (fun j => context (params j)))
    (domain : M.DomainMeaning s D A.domain (fun j => context (params j)))
    (nameEnv : Assignment D n) (hnames : ∀ i, context (names i) = (nameEnv i).val.val) :
    s.subset (fun p => Forces D φ nameEnv p) ∈ M.sets := by
  let translated := forcingTranslation A φ (fun j => (params j).succ) 0 (fun i => (names i).succ)
  have selected := M.separation_mem separation translated context members carrier
  have eq : ZFSet.sep (fun z => Realize M.sets translated (extend z context)) s.carrier =
      s.subset (fun p => Forces D φ nameEnv p) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, s.mem_subset]
    constructor
    · rintro ⟨hz, truth⟩
      obtain ⟨p, rfl⟩ := (s.mem_carrier z).1 hz
      exact ⟨p, (M.realize_forcingTranslation s D ground pairing carrier order A φ
        (fun j => (params j).succ) 0 (fun i => (names i).succ) (extend (s.encode p) context)
        hc ho atomic domain p nameEnv rfl hnames).1 truth, rfl⟩
    · rintro ⟨p, forced, rfl⟩
      exact ⟨s.encode_mem p, (M.realize_forcingTranslation s D ground pairing carrier order A φ
        (fun j => (params j).succ) 0 (fun i => (names i).succ) (extend (s.encode p) context)
        hc ho atomic domain p nameEnv rfl hnames).2 forced⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem exists_groundName_certificate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (τ : Name s) (hτ : τ.val ∈ M.sets) :
    ∃ S ∈ M.sets, Realize M.sets nameCertificateFormula (extend S (extend s.carrier Fin.elim0)) ∧
      τ.val ∈ S := by
  obtain ⟨T, hT, τT, trans⟩ := M.exists_transitiveCover pairing unions separation collection τ.val hτ
  let D := namesInTransitiveSet s T (fun hx hy => trans _ hx _ hy)
  let params := extend s.carrier Fin.elim0
  have members : ∀ i, params i ∈ M.sets := Fin.cases carrier (fun i => Fin.elim0 i)
  have mono : ∀ S ∈ M.sets, ∀ U ∈ M.sets, S ⊆ T → U ⊆ T → S ⊆ U →
      definableOperator M.sets nameCodeStepFormula params T S ⊆
        definableOperator M.sets nameCodeStepFormula params T U := by
    intro S hS U hU _ _ sub x hx
    obtain ⟨hxT, step⟩ := ZFSet.mem_sep.1 hx
    have hxM := M.transitive hT hxT
    exact ZFSet.mem_sep.2 ⟨hxT, (M.realize_nameCodeStepFormula s pairing carrier x U hxM hU).2
      (nameCodeStep_mono s sub ((M.realize_nameCodeStepFormula s pairing carrier x S hxM hS).1 step))⟩
  obtain ⟨S, hS, bound, fixed, _⟩ := M.exists_greatest_definable_fixedPoint unions powers separation
    nameCodeStepFormula params members hT mono
  have certificate : Realize M.sets nameCertificateFormula (extend S params) := by
    apply (M.realize_postfixedFormula nameCodeStepFormula params hS bound).2
    rw [fixed]
  have pre : ∀ ν ∈ D.names, NameCodeStep s S ν.val → ν.val ∈ S := by
    intro ν hν step
    have member : ν.val ∈ definableOperator M.sets nameCodeStepFormula params T S :=
      ZFSet.mem_sep.2 ⟨hν, (M.realize_nameCodeStepFormula s pairing carrier ν.val S
        (M.transitive hT hν) hS).2 step⟩
    rwa [fixed] at member
  exact ⟨S, hS, certificate, nameCodePrefixed_complete s D S pre τ τT⟩

theorem isName_iff_exists_certificate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (x : ZFSet.{u}) (hx : x ∈ M.sets) :
    IsName s x ↔
      ∃ S ∈ M.sets, Realize M.sets nameCertificateFormula (extend S (extend s.carrier Fin.elim0)) ∧
        x ∈ S := by
  constructor
  · intro name
    exact M.exists_groundName_certificate s pairing unions powers separation collection carrier ⟨x, name⟩ hx
  · rintro ⟨S, hS, certificate, member⟩
    exact M.nameCertificate_sound s pairing carrier hS certificate x member

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.SetFormula

def withGroundEquality {k : Nat} (c o : Fin k) (N : SetFormula (k + 1)) : ForcingPrimitives k where
  carrier := c
  order := o
  equality := liftedEqualityFormula c o
  domain := N

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_forcingWithGroundEquality (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k n m : Nat} (c o : Fin k) (N : SetFormula (k + 1)) (φ : SetFormula n)
    (params : Fin k → Fin m) (pi : Fin m) (names : Fin n → Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params c) = s.carrier) (ho : env (params o) = s.conditionOrder)
    (domain : M.DomainMeaning s D N (fun j => env (params j)))
    (p : P) (nameEnv : Assignment D n) (hp : env pi = s.encode p)
    (hnames : ∀ i, env (names i) = (nameEnv i).val.val) :
    Realize M.sets (forcingTranslation (withGroundEquality c o N) φ params pi names) env ↔
      Forces D φ nameEnv p :=
  M.realize_forcingTranslation s D ground pairing carrier order (withGroundEquality c o N) φ
    params pi names env hc ho
    (M.equalityMeaning_lifted s D ground pairing unions powers separation collection carrier order c o _ hc ho)
    domain p nameEnv hp hnames

theorem forcingSet_mem_withGroundEquality (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k n m : Nat} (c o : Fin k) (N : SetFormula (k + 1)) (φ : SetFormula n)
    (params : Fin k → Fin m) (names : Fin n → Fin m) (context : Fin m → ZFSet.{u})
    (members : ∀ i, context i ∈ M.sets)
    (hc : context (params c) = s.carrier) (ho : context (params o) = s.conditionOrder)
    (domain : M.DomainMeaning s D N (fun j => context (params j)))
    (nameEnv : Assignment D n) (hnames : ∀ i, context (names i) = (nameEnv i).val.val) :
    s.subset (fun p => Forces D φ nameEnv p) ∈ M.sets :=
  M.forcingSet_mem s D ground pairing carrier order separation (withGroundEquality c o N) φ params names
    context members hc ho
    (M.equalityMeaning_lifted s D ground pairing unions powers separation collection carrier order c o _ hc ho)
    domain nameEnv hnames

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.SetFormula

def uniformNameFormula : SetFormula 2 :=
  ex (.conj (domainApplication nameCertificateFormula (extend 2 Fin.elim0) 0) (.mem 1 0))

def liftedNameFormula {k : Nat} (c : Fin k) : SetFormula (k + 1) :=
  domainApplication uniformNameFormula (extend c.succ Fin.elim0) 0

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem realize_uniformNameFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (x : ZFSet.{u}) (hx : x ∈ M.sets) :
    Realize M.sets uniformNameFormula (extend x (extend s.carrier Fin.elim0)) ↔ IsName s x := by
  rw [M.isName_iff_exists_certificate s pairing unions powers separation collection carrier x hx,
    uniformNameFormula, realize_ex]
  apply exists_congr
  intro S
  apply and_congr_right
  intro _
  change (Realize M.sets _ _ ∧ x ∈ S) ↔ _
  rw [realize_domainApplication, map_extend, map_empty]
  rfl

theorem domainMeaning_liftedNames
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets)
    {k : Nat} (c : Fin k) (constants : Fin k → ZFSet.{u}) (hc : constants c = s.carrier) :
    M.DomainMeaning s (M.nameDomain s) (liftedNameFormula c) constants := by
  intro x hx
  rw [liftedNameFormula, realize_domainApplication, map_extend, map_empty]
  change Realize M.sets uniformNameFormula (extend x (extend (constants c) Fin.elim0)) ↔ _
  rw [hc, M.realize_uniformNameFormula s pairing unions powers separation collection carrier x hx]
  constructor
  · intro name
    exact ⟨⟨⟨x, name⟩, hx⟩, rfl⟩
  · rintro ⟨τ, rfl⟩
    exact τ.val.property

end PartitionPilot.Forcing.TransitiveGround

end OAI
