import OAI.SetTheory.PartitionPrinciple.Definability.NameSupportFormulas

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

def nameSymmetryFormula : SetFormula 6 :=
  exConditions 3 (allConditions 3 (imp (pairMembershipFormula 1 0 6)
    (atomicApplication nameActionFormula (extend 3 (extend 7 Fin.elim0)) 0 2 2)))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

noncomputable def symmetryParameters (K : I → Subgroup G) : Fin 5 → ZFSet.{u} :=
  extend s.carrier (extend t.carrier (extend b.carrier
    (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) Fin.elim0))))

theorem realize_nameSymmetryFormula (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (τ : Name s) (hτ : τ.val ∈ M.sets) :
    Realize M.sets nameSymmetryFormula (extend τ.val (symmetryParameters a s t b K)) ↔
      F.mem (a.stabilizer s τ) := by
  let env := extend τ.val (symmetryParameters a s t b K)
  rw [basis (a.stabilizer s τ), nameSymmetryFormula,
    M.realize_exConditions b 3 _ env indices rfl]
  apply exists_congr
  intro i
  rw [M.realize_allConditions t 3 _ (extend (b.encode i) env) group rfl]
  change (∀ g, Realize M.sets _ _) ↔ ∀ g, g ∈ K i → a.act s g τ = τ
  apply forall_congr'
  intro g
  let e := extend (t.encode g) (extend (b.encode i) env)
  rw [realize_imp, M.realize_pairMembershipFormula pairing 1 0 6 e
    (M.transitive indices (b.encode_mem i)) (M.transitive group (t.encode_mem g)) supports]
  change (ZFSet.pair (b.encode i) (t.encode g) ∈ supportBasisCode b t K → Realize M.sets _ e) ↔ _
  rw [pair_mem_supportBasisCode]
  apply forall_congr'
  intro _
  rw [realize_atomicApplication, map_extend, map_extend, map_empty]
  exact M.realize_nameActionFormula a s t pairing unions powers separation collection carrier group maps g τ τ hτ hτ

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.SetFormula

def hereditaryStepFormula : SetFormula 7 :=
  .conj (domainApplication nameSymmetryFormula (fun j => j.succ.succ) 0)
    (binaryApplication nameCodeStepFormula (extend 2 Fin.elim0) 0 1)

def hereditaryCertificateFormula : SetFormula 6 := postfixedFormula hereditaryStepFormula

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem realize_hereditaryStepFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (carrier : s.carrier ∈ M.sets)
    (params : Fin 5 → ZFSet.{u}) (hc : params 0 = s.carrier)
    (x R : ZFSet.{u}) (hx : x ∈ M.sets) (hr : R ∈ M.sets) :
    Realize M.sets hereditaryStepFormula (extend x (extend R params)) ↔
      Realize M.sets nameSymmetryFormula (extend x params) ∧ NameCodeStep s R x := by
  change (Realize M.sets _ _ ∧ Realize M.sets _ _) ↔ _
  rw [realize_domainApplication, realize_binaryApplication, map_extend, map_empty]
  change (Realize M.sets nameSymmetryFormula (extend x params) ∧
    Realize M.sets nameCodeStepFormula (extend x (extend R (extend (params 0) Fin.elim0)))) ↔ _
  rw [hc, M.realize_nameCodeStepFormula s pairing carrier x R hx hr]

theorem hereditaryCertificate_isName
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (carrier : s.carrier ∈ M.sets)
    (params : Fin 5 → ZFSet.{u}) (hc : params 0 = s.carrier)
    {R : ZFSet.{u}} (hr : R ∈ M.sets)
    (certificate : Realize M.sets hereditaryCertificateFormula (extend R params)) :
    ∀ x ∈ R, IsName s x := by
  apply nameCodePostfixed_sound s R
  intro x hx
  exact ((M.realize_hereditaryStepFormula s pairing carrier params hc x R (M.transitive hr hx) hr).1
    ((realize_imp M.sets _ _ _).1 (certificate x (M.transitive hr hx)) hx)).2

variable {I G : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (t : Presentation G) (b : Presentation I)

theorem hereditaryCertificate_sound (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    {R : ZFSet.{u}} (hr : R ∈ M.sets)
    (certificate : Realize M.sets hereditaryCertificateFormula (extend R (symmetryParameters a s t b K))) :
    ∀ τ : Name s, τ.val ∈ R → HereditarilySymmetric a s F τ := by
  intro τ
  induction τ using Name.inductionOn with
  | step τ ih =>
    intro hτ
    have hτM := M.transitive hr hτ
    have step := (M.realize_hereditaryStepFormula s pairing carrier (symmetryParameters a s t b K)
      rfl τ.val R hτM hr).1 ((realize_imp M.sets _ _ _).1 (certificate τ.val hτM) hτ)
    apply HereditarilySymmetric.mk
    · exact (M.realize_nameSymmetryFormula a s t b F K basis pairing unions powers separation collection
        carrier group indices supports maps τ hτM).1 step.1
    · intro σ p entry
      obtain ⟨x, hx, q, shape⟩ := step.2 _ entry
      have eq := (ZFSet.pair_inj.1 shape).1
      exact ih σ p entry (eq ▸ hx)

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem exists_hereditary_certificate (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (τ : Name s) (hτ : τ.val ∈ M.sets) (hs : HereditarilySymmetric a s F τ) :
    ∃ R ∈ M.sets, Realize M.sets hereditaryCertificateFormula
      (extend R (symmetryParameters a s t b K)) ∧ τ.val ∈ R := by
  obtain ⟨T, hT, τT, trans⟩ := M.exists_transitiveCover pairing unions separation collection τ.val hτ
  let D := a.symmetricDomain s (namesInTransitiveSet s T (fun hx hy => trans _ hx _ hy)) F
  let params := symmetryParameters a s t b K
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases carrier (Fin.cases group (Fin.cases indices (Fin.cases supports
      (Fin.cases maps (fun i => Fin.elim0 i)))))
  have mono : ∀ R ∈ M.sets, ∀ S ∈ M.sets, R ⊆ T → S ⊆ T → R ⊆ S →
      definableOperator M.sets hereditaryStepFormula params T R ⊆
        definableOperator M.sets hereditaryStepFormula params T S := by
    intro R hr S hS _ _ sub x hx
    obtain ⟨hxT, step⟩ := ZFSet.mem_sep.1 hx
    have hxM := M.transitive hT hxT
    obtain ⟨sym, children⟩ := (M.realize_hereditaryStepFormula s pairing carrier params rfl x R hxM hr).1 step
    exact ZFSet.mem_sep.2 ⟨hxT, (M.realize_hereditaryStepFormula s pairing carrier params rfl x S hxM hS).2
      ⟨sym, nameCodeStep_mono s sub children⟩⟩
  obtain ⟨R, hr, bound, fixed, _⟩ := M.exists_greatest_definable_fixedPoint unions powers separation
    hereditaryStepFormula params members hT mono
  have certificate : Realize M.sets hereditaryCertificateFormula (extend R params) := by
    apply (M.realize_postfixedFormula hereditaryStepFormula params hr bound).2
    rw [fixed]
  have pre : ∀ ν ∈ D.names, NameCodeStep s R ν.val → ν.val ∈ R := by
    intro ν hν step
    have hνM := M.transitive hT hν.1
    have sym := (M.realize_nameSymmetryFormula a s t b F K basis pairing unions powers separation collection
      carrier group indices supports maps ν hνM).2 hν.2.symmetric
    have member : ν.val ∈ definableOperator M.sets hereditaryStepFormula params T R :=
      ZFSet.mem_sep.2 ⟨hν.1,
        (M.realize_hereditaryStepFormula s pairing carrier params rfl ν.val R hνM hr).2 ⟨sym, step⟩⟩
    rwa [fixed] at member
  exact ⟨R, hr, certificate, nameCodePrefixed_complete s D R pre τ ⟨τT, hs⟩⟩

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.SetFormula

def uniformHereditaryFormula : SetFormula 6 :=
  ex (.conj (domainApplication hereditaryCertificateFormula (fun j => j.succ.succ) 0) (.mem 1 0))

def liftedHereditaryFormula {k : Nat} (c g i b a : Fin k) : SetFormula (k + 1) :=
  domainApplication uniformHereditaryFormula
    (extend c.succ (extend g.succ (extend i.succ (extend b.succ (extend a.succ Fin.elim0))))) 0

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem realize_uniformHereditaryFormula (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (x : ZFSet.{u}) (hx : x ∈ M.sets) :
    Realize M.sets uniformHereditaryFormula (extend x (symmetryParameters a s t b K)) ↔
      ∃ h : IsName s x, HereditarilySymmetric a s F ⟨x, h⟩ := by
  rw [uniformHereditaryFormula, realize_ex]
  constructor
  · rintro ⟨R, hr, certificate, member⟩
    have cert := (realize_domainApplication M.sets hereditaryCertificateFormula _ _ _).1 certificate
    have name := M.hereditaryCertificate_isName s pairing carrier (symmetryParameters a s t b K) rfl hr cert x member
    exact ⟨name, M.hereditaryCertificate_sound s a t b F K basis pairing unions powers separation collection
      carrier group indices supports maps hr cert ⟨x, name⟩ member⟩
  · rintro ⟨name, hs⟩
    obtain ⟨R, hr, certificate, member⟩ := M.exists_hereditary_certificate a s t b F K basis
      pairing unions powers separation collection carrier group indices supports maps ⟨x, name⟩ hx hs
    exact ⟨R, hr, (realize_domainApplication M.sets hereditaryCertificateFormula _ _ _).2 certificate, member⟩

theorem domainMeaning_liftedHereditary (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    {k : Nat} (c g i j l : Fin k) (constants : Fin k → ZFSet.{u})
    (hc : constants c = s.carrier) (hg : constants g = t.carrier) (hi : constants i = b.carrier)
    (hj : constants j = supportBasisCode b t K) (hl : constants l = a.conditionMapFamily s t) :
    M.DomainMeaning s (a.symmetricDomain s (M.nameDomain s) F)
      (liftedHereditaryFormula c g i j l) constants := by
  intro x hx
  rw [liftedHereditaryFormula, realize_domainApplication,
    map_extend, map_extend, map_extend, map_extend, map_extend, map_empty]
  change Realize M.sets uniformHereditaryFormula (extend x
    (extend (constants c) (extend (constants g) (extend (constants i)
      (extend (constants j) (extend (constants l) Fin.elim0)))))) ↔ _
  rw [hc, hg, hi, hj, hl]
  change Realize M.sets uniformHereditaryFormula (extend x (symmetryParameters a s t b K)) ↔ _
  rw [M.realize_uniformHereditaryFormula a s t b F K basis pairing unions powers separation collection
      carrier group indices supports maps x hx]
  constructor
  · rintro ⟨name, hs⟩
    exact ⟨⟨⟨x, name⟩, hx, hs⟩, rfl⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨τ.val.property, τ.property.2⟩

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.SetFormula

def symmetricGroundPrimitives : ForcingPrimitives 6 :=
  withGroundEquality 0 1 (liftedHereditaryFormula 0 2 3 4 5)

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem realize_symmetricGroundForcing (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    {n m : Nat} (φ : SetFormula n) (params : Fin 6 → Fin m)
    (pi : Fin m) (names : Fin n → Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params 0) = s.carrier) (ho : env (params 1) = s.conditionOrder)
    (hg : env (params 2) = t.carrier) (hi : env (params 3) = b.carrier)
    (hj : env (params 4) = supportBasisCode b t K) (hl : env (params 5) = a.conditionMapFamily s t)
    (p : P) (nameEnv : Assignment (a.symmetricDomain s (M.nameDomain s) F) n)
    (hp : env pi = s.encode p) (hnames : ∀ i, env (names i) = (nameEnv i).val.val) :
    Realize M.sets (forcingTranslation symmetricGroundPrimitives φ params pi names) env ↔
      Forces (a.symmetricDomain s (M.nameDomain s) F) φ nameEnv p :=
  M.realize_forcingWithGroundEquality s (a.symmetricDomain s (M.nameDomain s) F) (fun _ h => h.1)
    pairing unions powers separation collection carrier order 0 1 (liftedHereditaryFormula 0 2 3 4 5)
    φ params pi names env hc ho
    (M.domainMeaning_liftedHereditary a s t b F K basis pairing unions powers separation collection carrier
      group indices supports maps 0 2 3 4 5 _ hc hg hi hj hl) p nameEnv hp hnames

theorem symmetricForcingSet_mem (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    {n : Nat} (φ : SetFormula n) (nameEnv : Assignment (a.symmetricDomain s (M.nameDomain s) F) n) :
    s.subset (fun p => Forces (a.symmetricDomain s (M.nameDomain s) F) φ nameEnv p) ∈ M.sets := by
  let context := extend s.carrier (extend s.conditionOrder (extend t.carrier (extend b.carrier
    (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) (fun i => (nameEnv i).val.val))))))
  let params : Fin 6 → Fin (n + 6) := extend 0 (extend 1 (extend 2 (extend 3 (extend 4 (extend 5 Fin.elim0)))))
  have members : ∀ i, context i ∈ M.sets :=
    Fin.cases carrier (Fin.cases order (Fin.cases group (Fin.cases indices (Fin.cases supports
      (Fin.cases maps (fun i => (nameEnv i).property.1))))))
  apply M.forcingSet_mem_withGroundEquality s (a.symmetricDomain s (M.nameDomain s) F) (fun _ h => h.1)
    pairing unions powers separation collection carrier order 0 1 (liftedHereditaryFormula 0 2 3 4 5) φ
    params (fun i => i.succ.succ.succ.succ.succ.succ) context members rfl rfl
  · exact M.domainMeaning_liftedHereditary a s t b F K basis pairing unions powers separation collection
      carrier group indices supports maps 0 2 3 4 5 _ rfl rfl rfl rfl rfl
  · exact fun _ => rfl

end PartitionPilot.Forcing.TransitiveGround

end OAI
