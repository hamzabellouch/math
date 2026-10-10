import OAI.SetTheory.PartitionPrinciple.Definability.CodedInjectiveCones
import OAI.SetTheory.PartitionPrinciple.Definability.RawRenameFormulas
import OAI.SetTheory.PartitionPrinciple.Definability.SeparationFulfillmentCodes
import OAI.SetTheory.PartitionPrinciple.Geometry.DecodedGroundGroups

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

def renameStateFormula : SetFormula 4 :=
  ex (ex (.conj (orderedPairFormula 2 1 0) (renameStepFormula 4 5 3 1 0)))

def renameCertificateFormula : SetFormula 3 := postfixedFormula renameStateFormula

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

noncomputable def renameParameters (f : P → P) : Fin 2 → ZFSet.{u} :=
  extend s.carrier (extend (s.graph s f) Fin.elim0)

theorem realize_renameState
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    (z R : ZFSet.{u}) (hz : z ∈ M.sets) (hr : R ∈ M.sets) :
    Realize M.sets renameStateFormula (extend z (extend R (renameParameters s f))) ↔
      ∃ x ∈ M.sets, ∃ y ∈ M.sets, z = ZFSet.pair x y ∧ M.RawRenameStep s f R x y := by
  rw [renameStateFormula, realize_ex]
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  rw [realize_ex]
  apply exists_congr
  intro y
  apply and_congr_right
  intro hy
  let e := extend y (extend x (extend z (extend R (renameParameters s f))))
  change (Realize M.sets _ e ∧ Realize M.sets _ e) ↔ _
  rw [M.realize_orderedPairFormula pairing 2 1 0 e hz hx hy,
    M.realize_renameStepFormula s pairing carrier f graph 4 5 3 1 0 e rfl rfl hr hx hy]
  rfl

theorem rawRenameStep_names (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (f : P → P) (R : ZFSet.{u}) (σ τ : D.names) :
    M.RawRenameStep s f R σ.val.val τ.val.val ↔
      Name.RenameStep f (fun ν ρ => ZFSet.pair ν.val ρ.val ∈ R) σ.val τ.val := by
  constructor
  · rintro ⟨left, right⟩
    constructor
    · intro ν p entry
      obtain ⟨w, _, q, matched, cond, rel⟩ := left ν.val (ground ν (D.children σ.property entry)) p entry
      change f p = q at cond
      subst q
      let ρ : Name s := ⟨w, Name.isName_of_pair_mem τ.val w (f p) matched⟩
      exact ⟨ρ, matched, rel⟩
    · intro ρ q entry
      obtain ⟨v, _, p, matched, cond, rel⟩ := right ρ.val (ground ρ (D.children τ.property entry)) q entry
      let ν : Name s := ⟨v, Name.isName_of_pair_mem σ.val v p matched⟩
      exact ⟨ν, p, matched, cond, rel⟩
  · rintro ⟨left, right⟩
    constructor
    · intro v _ p entry
      let ν : Name s := ⟨v, Name.isName_of_pair_mem σ.val v p entry⟩
      obtain ⟨ρ, matched, rel⟩ := left ν p entry
      exact ⟨ρ.val, ground ρ (D.children τ.property matched), f p, matched, rfl, rel⟩
    · intro w _ q entry
      let ρ : Name s := ⟨w, Name.isName_of_pair_mem τ.val w q entry⟩
      obtain ⟨ν, p, matched, cond, rel⟩ := right ρ q entry
      exact ⟨ν.val, ground ν (D.children σ.property matched), p, matched, cond, rel⟩

theorem realize_renameState_names (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    (R : ZFSet.{u}) (hr : R ∈ M.sets) (σ τ : D.names) :
    Realize M.sets renameStateFormula
      (extend (ZFSet.pair σ.val.val τ.val.val) (extend R (renameParameters s f))) ↔
      Name.RenameStep f (fun ν ρ => ZFSet.pair ν.val ρ.val ∈ R) σ.val τ.val := by
  have hz := M.orderedPair_mem pairing (ground σ.val σ.property) (ground τ.val τ.property)
  rw [M.realize_renameState s pairing carrier f graph _ R hz hr]
  constructor
  · rintro ⟨x, _, y, _, shape, step⟩
    obtain ⟨sx, ty⟩ := ZFSet.pair_inj.1 shape
    subst x
    subst y
    exact (M.rawRenameStep_names s D ground f R σ τ).1 step
  · intro step
    exact ⟨σ.val.val, ground σ.val σ.property, τ.val.val, ground τ.val τ.property, rfl,
      (M.rawRenameStep_names s D ground f R σ τ).2 step⟩

theorem renameCertificate_sound (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    {R : ZFSet.{u}} (hr : R ∈ M.sets)
    (certificate : Realize M.sets renameCertificateFormula (extend R (renameParameters s f)))
    (σ τ : D.names) : ZFSet.pair σ.val.val τ.val.val ∈ R → Name.rename s f σ.val = τ.val := by
  apply Name.rename_postfixed_sound D f (fun ν ρ => ZFSet.pair ν.val ρ.val ∈ R) _
    σ.val σ.property τ.val τ.property
  intro ν hν ρ hρ rel
  exact (M.realize_renameState_names s D ground pairing carrier f graph R hr ⟨ν, hν⟩ ⟨ρ, hρ⟩).1
    ((realize_imp M.sets _ _ _).1 (certificate _ (M.transitive hr rel)) rel)

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem exists_renameState_fixedPoint
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    (B : ZFSet.{u}) (hB : B ∈ M.sets) :
    ∃ R ∈ M.sets, R ⊆ B ∧ definableOperator M.sets renameStateFormula (renameParameters s f) B R = R := by
  have members : ∀ i, renameParameters s f i ∈ M.sets :=
    Fin.cases carrier (Fin.cases graph (fun i => Fin.elim0 i))
  have mono : ∀ R ∈ M.sets, ∀ S ∈ M.sets, R ⊆ B → S ⊆ B → R ⊆ S →
      definableOperator M.sets renameStateFormula (renameParameters s f) B R ⊆
        definableOperator M.sets renameStateFormula (renameParameters s f) B S := by
    intro R hr S hs _ _ sub z hz
    obtain ⟨hzB, step⟩ := ZFSet.mem_sep.1 hz
    have hzM := M.transitive hB hzB
    obtain ⟨x, hx, y, hy, shape, raw⟩ := (M.realize_renameState s pairing carrier f graph z R hzM hr).1 step
    exact ZFSet.mem_sep.2 ⟨hzB, (M.realize_renameState s pairing carrier f graph z S hzM hs).2
      ⟨x, hx, y, hy, shape, M.rawRenameStep_mono s f sub raw⟩⟩
  obtain ⟨R, hr, bound, fixed, _⟩ := M.exists_greatest_definable_fixedPoint unions powers separation
    renameStateFormula (renameParameters s f) members hB mono
  exact ⟨R, hr, bound, fixed⟩

theorem exists_groundRename_certificate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    (σ τ : Name s) (hσ : σ.val ∈ M.sets) (hτ : τ.val ∈ M.sets) (eq : Name.rename s f σ = τ) :
    ∃ R ∈ M.sets, Realize M.sets renameCertificateFormula (extend R (renameParameters s f)) ∧
      ZFSet.pair σ.val τ.val ∈ R := by
  obtain ⟨T, hT, σT, τT, trans⟩ := M.exists_pair_transitiveCover pairing unions separation collection hσ hτ
  let D := namesInTransitiveSet s T (fun hx hy => trans _ hx _ hy)
  have ground : ∀ ν ∈ D.names, ν.val ∈ M.sets := fun _ h => M.transitive hT h
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers hT hT
  obtain ⟨R, hr, bound, fixed⟩ := M.exists_renameState_fixedPoint s pairing unions powers separation
    carrier f graph B hB
  have certificate : Realize M.sets renameCertificateFormula (extend R (renameParameters s f)) := by
    apply (M.realize_postfixedFormula renameStateFormula (renameParameters s f) hr bound).2
    rw [fixed]
  have pre : ∀ ν ∈ D.names, ∀ ρ ∈ D.names,
      Name.RenameStep f (fun χ ψ => ZFSet.pair χ.val ψ.val ∈ R) ν ρ → ZFSet.pair ν.val ρ.val ∈ R := by
    intro ν hν ρ hρ step
    have member : ZFSet.pair ν.val ρ.val ∈
        definableOperator M.sets renameStateFormula (renameParameters s f) B R :=
      ZFSet.mem_sep.2 ⟨pairBound ν.val hν ρ.val hρ,
        (M.realize_renameState_names s D ground pairing carrier f graph R hr ⟨ν, hν⟩ ⟨ρ, hρ⟩).2 step⟩
    rwa [fixed] at member
  exact ⟨R, hr, certificate, Name.rename_prefixed_complete D f
    (fun ν ρ => ZFSet.pair ν.val ρ.val ∈ R) pre σ σT τ τT eq⟩

theorem rename_eq_iff_exists_certificate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    (σ τ : Name s) (hσ : σ.val ∈ M.sets) (hτ : τ.val ∈ M.sets) :
    Name.rename s f σ = τ ↔
      ∃ R ∈ M.sets, Realize M.sets renameCertificateFormula (extend R (renameParameters s f)) ∧
        ZFSet.pair σ.val τ.val ∈ R := by
  constructor
  · exact M.exists_groundRename_certificate s pairing unions powers separation collection carrier f graph σ τ hσ hτ
  · rintro ⟨R, hr, certificate, member⟩
    exact M.renameCertificate_sound s (M.nameDomain s) (fun _ h => h) pairing carrier f graph hr
      certificate ⟨σ, hσ⟩ ⟨τ, hτ⟩ member

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.SetFormula

universe u

def binaryApplication {k n : Nat} (φ : SetFormula (k + 2)) (params : Fin k → Fin n)
    (x y : Fin n) : SetFormula n := reindex (extend x (extend y params)) φ

theorem realize_binaryApplication (U : Set ZFSet.{u}) {k n : Nat} (φ : SetFormula (k + 2))
    (params : Fin k → Fin n) (x y : Fin n) (env : Fin n → ZFSet.{u}) :
    Realize U (binaryApplication φ params x y) env ↔
      Realize U φ (extend (env x) (extend (env y) (fun i => env (params i)))) := by
  rw [binaryApplication, realize_reindex, map_extend, map_extend]

def uniformRenameFormula : SetFormula 4 :=
  ex (.conj (atomicApplication renameCertificateFormula Fin.elim0 0 3 4)
    (pairMembershipFormula 1 2 0))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem realize_uniformRenameFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    (σ τ : Name s) (hσ : σ.val ∈ M.sets) (hτ : τ.val ∈ M.sets) :
    Realize M.sets uniformRenameFormula (extend σ.val (extend τ.val (renameParameters s f))) ↔
      Name.rename s f σ = τ := by
  rw [M.rename_eq_iff_exists_certificate s pairing unions powers separation collection carrier f graph σ τ hσ hτ,
    uniformRenameFormula, realize_ex]
  apply exists_congr
  intro R
  apply and_congr_right
  intro hr
  let env := extend R (extend σ.val (extend τ.val (renameParameters s f)))
  change (Realize M.sets _ env ∧ Realize M.sets _ env) ↔ _
  rw [realize_atomicApplication, map_empty,
    M.realize_pairMembershipFormula pairing 1 2 0 env hσ hτ hr]
  rfl

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.PosetAction

open SetRealization
universe u
variable {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

noncomputable def conditionMapFamily : ZFSet.{u} :=
  ZFSet.range (fun g : G => ZFSet.pair (t.encode g) (s.graph s (a.iso g)))

theorem pair_mem_conditionMapFamily (g : G) (F : ZFSet.{u}) :
    ZFSet.pair (t.encode g) F ∈ a.conditionMapFamily s t ↔ F = s.graph s (a.iso g) := by
  rw [conditionMapFamily, ZFSet.mem_range]
  constructor
  · rintro ⟨h, eq⟩
    obtain ⟨hg, value⟩ := ZFSet.pair_inj.1 eq
    have hgeq := t.injective hg
    subst h
    exact value.symm
  · intro eq
    exact ⟨g, congrArg (ZFSet.pair (t.encode g)) eq.symm⟩

end PartitionPilot.Forcing.PosetAction

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]

theorem conditionMap_graph_mem (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
    (maps : a.conditionMapFamily s t ∈ M.sets) (g : G) : s.graph s (a.iso g) ∈ M.sets :=
  M.pair_right (M.transitive maps ((a.pair_mem_conditionMapFamily s t g _).2 rfl))

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.PosetAction

open SetRealization
universe u
variable {G P : Type u} [Group G] [PartialOrder P]

noncomputable def actionGraph (a : PosetAction G P) (s : Presentation P) (t : Presentation G) : ZFSet.{u} :=
  (t.product s).graph s (fun x => a.iso x.1 x.2)

theorem triple_mem_actionGraph (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
    (g : G) (p q : P) :
    ZFSet.pair (ZFSet.pair (t.encode g) (s.encode p)) (s.encode q) ∈ a.actionGraph s t ↔ a.iso g p = q :=
  (t.product s).pair_mem_graph s (fun x => a.iso x.1 x.2) (g, p) q

end PartitionPilot.Forcing.PosetAction

namespace PartitionPilot.Forcing.PosetActionCode

open SetRealization
universe u
variable {G P m i e R A : ZFSet.{u}} (h : PosetActionCode G P m e R A)

noncomputable def act (g : SetMembers G) (p : SetMembers P) : SetMembers P :=
  ((SetMembers.presentation G).product (SetMembers.presentation P)).decodeFunction
    (SetMembers.presentation P) A h.function (g, p)

theorem act_mem (g : SetMembers G) (p : SetMembers P) :
    ZFSet.pair (ZFSet.pair (SetMembers.raw g) (SetMembers.raw p)) (SetMembers.raw (h.act g p)) ∈ A :=
  ((SetMembers.presentation G).product (SetMembers.presentation P)).decodeFunction_mem
    (SetMembers.presentation P) A h.function (g, p)

theorem act_eq_iff (g : SetMembers G) (p q : SetMembers P) : h.act g p = q ↔
    ZFSet.pair (ZFSet.pair (SetMembers.raw g) (SetMembers.raw p)) (SetMembers.raw q) ∈ A :=
  ((SetMembers.presentation G).product (SetMembers.presentation P)).decodeFunction_iff
    (SetMembers.presentation P) A h.function (g, p) q

theorem act_one (group : GroupCode G m i e) (p : SetMembers P) :
    letI _decodedGroup := group.toGroup
    h.act 1 p = p := by
  let decodedGroup := group.toGroup
  apply (h.act_eq_iff _ _ _).2
  change ZFSet.pair (ZFSet.pair (SetMembers.raw group.one) (SetMembers.raw p)) (SetMembers.raw p) ∈ A
  rw [group.raw_one]
  exact h.one _ (SetMembers.raw_mem p)

theorem act_mul (group : GroupCode G m i e) (g j : SetMembers G) (p : SetMembers P) :
    letI _decodedGroup := group.toGroup
    h.act (g * j) p = h.act g (h.act j p) := by
  let decodedGroup := group.toGroup
  apply (h.act_eq_iff _ _ _).2
  exact h.mul _ (SetMembers.raw_mem g) _ (SetMembers.raw_mem j) _ (SetMembers.raw_mem (g * j))
    _ (SetMembers.raw_mem p) _ (SetMembers.raw_mem (h.act j p)) _ (SetMembers.raw_mem (h.act g (h.act j p)))
    (group.mul_mem g j) (h.act_mem j p) (h.act_mem g (h.act j p))

theorem act_inv_left (group : GroupCode G m i e) (g : SetMembers G) (p : SetMembers P) :
    letI _decodedGroup := group.toGroup
    h.act g⁻¹ (h.act g p) = p := by
  let decodedGroup := group.toGroup
  rw [← h.act_mul group, inv_mul_cancel, h.act_one group]

theorem act_inv_right (group : GroupCode G m i e) (g : SetMembers G) (p : SetMembers P) :
    letI _decodedGroup := group.toGroup
    h.act g (h.act g⁻¹ p) = p := by
  let decodedGroup := group.toGroup
  rw [← h.act_mul group, mul_inv_cancel, h.act_one group]

theorem act_monotone (order : PartialOrderCode P R) (g : SetMembers G) :
    letI _decodedOrder := order.toPartialOrder
    Monotone (h.act g) := by
  let decodedOrder := order.toPartialOrder
  intro p q pq
  exact h.monotone _ (SetMembers.raw_mem g) _ (SetMembers.raw_mem p) _ (SetMembers.raw_mem q)
    _ (SetMembers.raw_mem (h.act g p)) _ (SetMembers.raw_mem (h.act g q))
    (h.act_mem g p) (h.act_mem g q) pq

theorem act_le_iff (group : GroupCode G m i e) (order : PartialOrderCode P R)
    (g : SetMembers G) (p q : SetMembers P) :
    letI _decodedGroup := group.toGroup
    letI _decodedOrder := order.toPartialOrder
    h.act g p ≤ h.act g q ↔ p ≤ q := by
  let decodedGroup := group.toGroup
  let decodedOrder := order.toPartialOrder
  constructor
  · intro le
    have back := h.act_monotone order g⁻¹ le
    simpa only [h.act_inv_left group] using back
  · exact fun le => h.act_monotone order g le

noncomputable def toPosetAction (group : GroupCode G m i e) (order : PartialOrderCode P R) :
    letI _decodedGroup := group.toGroup
    letI _decodedOrder := order.toPartialOrder
    PosetAction (SetMembers G) (SetMembers P) := by
  letI decodedGroup := group.toGroup
  letI decodedOrder := order.toPartialOrder
  exact {
    iso := fun g => {
      toFun := h.act g
      invFun := h.act g⁻¹
      left_inv := h.act_inv_left group g
      right_inv := h.act_inv_right group g
      map_rel_iff' := h.act_le_iff group order g _ _ }
    one := h.act_one group
    mul := h.act_mul group }

theorem actionGraph_eq (group : GroupCode G m i e) (order : PartialOrderCode P R) :
    letI _decodedGroup := group.toGroup
    letI _decodedOrder := order.toPartialOrder
    (h.toPosetAction group order).actionGraph (SetMembers.presentation P) (SetMembers.presentation G) = A := by
  let decodedGroup := group.toGroup
  let decodedOrder := order.toPartialOrder
  exact ((SetMembers.presentation G).product (SetMembers.presentation P)).graph_decodeFunction
    (SetMembers.presentation P) A h.function

end PartitionPilot.Forcing.PosetActionCode

end


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

def identityPosetAction (G P : Type u) [Group G] [PartialOrder P] : PosetAction G P where
  iso _ := OrderIso.refl P
  one _ := rfl
  mul _ _ _ := rfl

def trivialGroupPresentation : Presentation (Equiv.Perm (ULift.{u} Unit)) where
  carrier := {∅}
  encode _ := ∅
  injective := fun _ _ _ => Subsingleton.elim _ _
  mem_carrier x := by
    rw [ZFSet.mem_singleton]
    exact ⟨fun h => ⟨1, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩

theorem identityPosetAction_graph_eq {G P : Type u} [Group G] [PartialOrder P]
    (s : Presentation P) (g : G) :
    s.graph s ((identityPosetAction G P).iso g) = identityFunctionGraph s.carrier := by
  apply ZFSet.ext
  intro z
  rw [s.mem_graph, mem_identityFunctionGraph]
  constructor
  · rintro ⟨p, eq⟩
    exact ⟨s.encode p, s.encode_mem p, eq.symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
    exact ⟨p, rfl⟩

theorem identityPosetAction_conditionMapFamily {P : Type u} [PartialOrder P]
    (s : Presentation P) :
    (identityPosetAction (Equiv.Perm (ULift.{u} Unit)) P).conditionMapFamily
      s trivialGroupPresentation = {ZFSet.pair ∅ (identityFunctionGraph s.carrier)} := by
  apply ZFSet.ext
  intro z
  rw [PosetAction.conditionMapFamily, ZFSet.mem_range, ZFSet.mem_singleton]
  constructor
  · rintro ⟨g, eq⟩
    change ZFSet.pair ∅ (s.graph s ((identityPosetAction _ P).iso g)) = z at eq
    rw [identityPosetAction_graph_eq] at eq
    exact eq.symm
  · intro eq
    refine ⟨1, ?_⟩
    change ZFSet.pair ∅ (s.graph s ((identityPosetAction (Equiv.Perm (ULift.{u} Unit)) P).iso 1)) = z
    rw [identityPosetAction_graph_eq]
    exact eq.symm

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem trivialGroupPresentation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (nonempty : M.sets.Nonempty) :
    trivialGroupPresentation.carrier ∈ M.sets := by
  change ({∅} : ZFSet.{u}) ∈ M.sets
  simpa only [ZFSet.pair_eq_singleton] using
    M.unorderedPair_mem pairing (M.empty_mem nonempty) (M.empty_mem nonempty)

theorem identityPosetAction_conditionMapFamily_mem {P : Type u} [PartialOrder P]
    (s : Presentation P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) :
    (identityPosetAction (Equiv.Perm (ULift.{u} Unit)) P).conditionMapFamily
      s trivialGroupPresentation ∈ M.sets := by
  rw [identityPosetAction_conditionMapFamily]
  have entry := M.orderedPair_mem pairing (M.empty_mem ⟨s.carrier, carrier⟩)
    (M.identityFunctionGraph_mem pairing unions powers separation carrier)
  simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing entry entry

end TransitiveGround

end PartitionPilot.Forcing


section

namespace PartitionPilot.Forcing.SetFormula

def nameActionFormula : SetFormula 5 :=
  ex (.conj (pairMembershipFormula 1 0 5)
    (binaryApplication uniformRenameFormula (extend 4 (extend 0 Fin.elim0)) 2 3))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem realize_nameActionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (g : G) (σ τ : Name s) (hσ : σ.val ∈ M.sets) (hτ : τ.val ∈ M.sets) :
    Realize M.sets nameActionFormula
      (extend (t.encode g) (extend σ.val (extend τ.val
        (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))) ↔
      a.act s g σ = τ := by
  rw [nameActionFormula, realize_ex]
  have hg := M.transitive group (t.encode_mem g)
  have graph := M.conditionMap_graph_mem a s t maps g
  let base := extend (t.encode g) (extend σ.val (extend τ.val
    (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))
  constructor
  · rintro ⟨F, hF, lookup, renamed⟩
    have raw := (M.realize_pairMembershipFormula pairing 1 0 5 (extend F base) hg hF maps).1 lookup
    have eq := (a.pair_mem_conditionMapFamily s t g F).1 raw
    subst F
    rw [realize_binaryApplication, map_extend, map_extend, map_empty] at renamed
    exact (M.realize_uniformRenameFormula s pairing unions powers separation collection carrier
      (a.iso g) graph σ τ hσ hτ).1 renamed
  · intro eq
    refine ⟨s.graph s (a.iso g), graph, ?_, ?_⟩
    · exact (M.realize_pairMembershipFormula pairing 1 0 5 (extend (s.graph s (a.iso g)) base)
        hg graph maps).2 ((a.pair_mem_conditionMapFamily s t g _).2 rfl)
    · rw [realize_binaryApplication, map_extend, map_extend, map_empty]
      exact (M.realize_uniformRenameFormula s pairing unions powers separation collection carrier
        (a.iso g) graph σ τ hσ hτ).2 eq

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.SetRealization.Presentation

universe u
variable {I : Type u} [Bot I]

noncomputable def nonbottom (s : Presentation I) : Presentation {x : I // x ≠ ⊥} where
  carrier := ZFSet.sep (fun z => z ≠ s.encode ⊥) s.carrier
  encode x := s.encode x.val
  injective := fun _ _ eq => Subtype.ext (s.injective eq)
  mem_carrier z := by
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, ne⟩
      obtain ⟨x, rfl⟩ := (s.mem_carrier z).1 hz
      exact ⟨⟨x, fun eq => ne (congrArg s.encode eq)⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨s.encode_mem x.val, fun eq => x.property (s.injective eq)⟩

theorem nonbottom_encode (s : Presentation I) (x : {x : I // x ≠ ⊥}) :
    s.nonbottom.encode x = s.encode x.val := rfl

theorem mem_nonbottom_carrier (s : Presentation I) (z : ZFSet.{u}) :
    z ∈ s.nonbottom.carrier ↔ z ∈ s.carrier ∧ z ≠ s.encode ⊥ := by
  change z ∈ ZFSet.sep (fun w => w ≠ s.encode ⊥) s.carrier ↔ _
  exact ZFSet.mem_sep

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.PosetAction

universe u v
variable {G : Type v} [Group G] {I : Type u} [PartialOrder I] [OrderBot I]

def nonbottomIso (a : PosetAction G I) (g : G) :
    {x : I // x ≠ ⊥} ≃o {x : I // x ≠ ⊥} where
  toFun x := ⟨a.iso g x.val, fun eq =>
    x.property ((a.iso g).injective (eq.trans (a.iso g).map_bot.symm))⟩
  invFun x := ⟨(a.iso g).symm x.val, fun eq =>
    x.property ((a.iso g).symm.injective (eq.trans (a.iso g).symm.map_bot.symm))⟩
  left_inv x := Subtype.ext ((a.iso g).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((a.iso g).apply_symm_apply x.val)
  map_rel_iff' := (a.iso g).map_rel_iff

def nonbottom (a : PosetAction G I) : PosetAction G {x : I // x ≠ ⊥} where
  iso := a.nonbottomIso
  one x := Subtype.ext (a.one x.val)
  mul g h x := Subtype.ext (a.mul g h x.val)

theorem nonbottom_iso_val (a : PosetAction G I) (g : G) (x : {x : I // x ≠ ⊥}) :
    (a.nonbottom.iso g x).val = a.iso g x.val := rfl

end PartitionPilot.Forcing.PosetAction

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def actionRestrictionEntryFormula {n} (z g p : Fin n) : BoundedFormula n :=
  exMem g (exMem p.succ (exMem p.succ.succ
    (orderedTripleFormula z.succ.succ.succ 2 1 0)))

theorem truth_actionRestrictionEntryFormula {n} (z g p : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (actionRestrictionEntryFormula z g p) env ↔
      ∃ h ∈ env g, ∃ x ∈ env p, ∃ y ∈ env p,
        env z = ZFSet.pair (ZFSet.pair h x) y := by
  simp only [actionRestrictionEntryFormula, truth_exMem, truth_orderedTripleFormula]
  rfl

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.PosetAction

open SetRealization SetFormula
universe u
variable {G I : Type u} [Group G] [PartialOrder I] [OrderBot I]

theorem nonbottom_actionGraph_eq_sep (a : PosetAction G I) (s : Presentation I)
    (t : Presentation G) :
    a.nonbottom.actionGraph s.nonbottom t = ZFSet.sep
      (fun z => BoundedFormula.Truth (BoundedFormula.actionRestrictionEntryFormula 0 1 2)
        (extend z (extend t.carrier (extend s.nonbottom.carrier Fin.elim0))))
      (a.actionGraph s t) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨⟨g, x⟩, rfl⟩ := ((t.product s.nonbottom).mem_graph s.nonbottom
      (fun gx => a.nonbottom.iso gx.1 gx.2) z).1 hz
    apply ZFSet.mem_sep.2
    refine ⟨(a.triple_mem_actionGraph s t g x.val (a.iso g x.val)).2 rfl, ?_⟩
    exact (BoundedFormula.truth_actionRestrictionEntryFormula 0 1 2 _).2
      ⟨t.encode g, t.encode_mem g, s.nonbottom.encode x, s.nonbottom.encode_mem x,
        s.nonbottom.encode (a.nonbottom.iso g x), s.nonbottom.encode_mem _, rfl⟩
  · intro hz
    obtain ⟨original, shape⟩ := ZFSet.mem_sep.1 hz
    obtain ⟨g, hg, x, hx, y, hy, eq⟩ :=
      (BoundedFormula.truth_actionRestrictionEntryFormula 0 1 2 _).1 shape
    obtain ⟨g, rfl⟩ := (t.mem_carrier g).1 hg
    obtain ⟨x, rfl⟩ := (s.nonbottom.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.nonbottom.mem_carrier y).1 hy
    change z = ZFSet.pair (ZFSet.pair (t.encode g) (s.nonbottom.encode x))
      (s.nonbottom.encode y) at eq
    rw [eq]
    apply (a.nonbottom.triple_mem_actionGraph s.nonbottom t g x y).2
    apply Subtype.ext
    exact (a.triple_mem_actionGraph s t g x.val y.val).1 (eq ▸ original)

end PartitionPilot.Forcing.PosetAction

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem nonbottom_carrier_mem {I : Type u} [Bot I] (s : Presentation I)
    (separation : SeparationSchema M.sets) (carrier : s.carrier ∈ M.sets) :
    s.nonbottom.carrier ∈ M.sets := by
  have bottom := M.transitive carrier (s.encode_mem ⊥)
  exact M.bounded_separation_mem separation (.neg (.equal 0 1))
    (extend (s.encode ⊥) Fin.elim0) (Fin.cases bottom (fun j => Fin.elim0 j)) carrier

theorem nonbottom_actionGraph_mem {G I : Type u} [Group G] [PartialOrder I] [OrderBot I]
    (a : PosetAction G I) (s : Presentation I) (t : Presentation G)
    (separation : SeparationSchema M.sets) (carrier : s.carrier ∈ M.sets)
    (group : t.carrier ∈ M.sets) (graph : a.actionGraph s t ∈ M.sets) :
    a.nonbottom.actionGraph s.nonbottom t ∈ M.sets := by
  rw [a.nonbottom_actionGraph_eq_sep s t]
  exact M.bounded_separation_mem separation (BoundedFormula.actionRestrictionEntryFormula 0 1 2)
    (extend t.carrier (extend s.nonbottom.carrier Fin.elim0))
    (Fin.cases group (Fin.cases (M.nonbottom_carrier_mem s separation carrier)
      (fun j => Fin.elim0 j))) graph

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.PosetAction

open SetRealization
universe u
variable {G I : Type u} [Group G] [PartialOrder I]

noncomputable def productColumns (a : PosetAction G I) (C : Type u) [PartialOrder C] :
    PosetAction G (I × C) where
  iso g := {
    toFun := fun x => (a.iso g x.1, x.2)
    invFun := fun x => ((a.iso g).symm x.1, x.2)
    left_inv := fun x => Prod.ext ((a.iso g).symm_apply_apply x.1) rfl
    right_inv := fun x => Prod.ext ((a.iso g).apply_symm_apply x.1) rfl
    map_rel_iff' := by
      intro x y
      exact and_congr (a.iso g).map_rel_iff Iff.rfl }
  one x := Prod.ext (a.one x.1) rfl
  mul g h x := Prod.ext (a.mul g h x.1) rfl

theorem productColumns_apply (a : PosetAction G I) (C : Type u) [PartialOrder C]
    (g : G) (i : I) (c : C) : (a.productColumns C).iso g (i, c) = (a.iso g i, c) := rfl

theorem mem_productColumns_actionGraph {C : Type u} [PartialOrder C]
    (a : PosetAction G I) (s : Presentation I) (c : Presentation C) (t : Presentation G)
    (z : ZFSet.{u}) :
    z ∈ (a.productColumns C).actionGraph (s.product c) t ↔ ∃ g i k,
      z = ZFSet.pair (ZFSet.pair (t.encode g) (ZFSet.pair (s.encode i) (c.encode k)))
        (ZFSet.pair (s.encode (a.iso g i)) (c.encode k)) := by
  rw [actionGraph, Presentation.mem_graph]
  constructor
  · rintro ⟨⟨g, i, k⟩, eq⟩
    exact ⟨g, i, k, eq.symm⟩
  · rintro ⟨g, i, k, eq⟩
    exact ⟨(g, i, k), eq.symm⟩

end PartitionPilot.Forcing.PosetAction

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula SetRealization
universe u

def productColumnsEntryFormula {n} (z g i c q a : Fin n) : BoundedFormula n :=
  exMem g (exMem i.succ (exMem i.succ.succ (exMem c.succ.succ.succ
    (exMem q.succ.succ.succ.succ (exMem q.succ.succ.succ.succ.succ
      (.conj (orderedPairFormula 1 4 2)
        (.conj (orderedPairFormula 0 3 2)
          (.conj (orderedTripleFormula z.succ.succ.succ.succ.succ.succ 5 1 0)
            (tripleMembershipFormula 5 4 3 a.succ.succ.succ.succ.succ.succ)))))))))

theorem truth_productColumnsEntryFormula {n} (z g i c q a : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (productColumnsEntryFormula z g i c q a) env ↔
      ∃ h ∈ env g, ∃ x ∈ env i, ∃ y ∈ env i, ∃ k ∈ env c,
        ∃ v ∈ env q, ∃ w ∈ env q,
          v = ZFSet.pair x k ∧ w = ZFSet.pair y k ∧
          env z = ZFSet.pair (ZFSet.pair h v) w ∧
          ZFSet.pair (ZFSet.pair h x) y ∈ env a := by
  simp only [productColumnsEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_orderedTripleFormula, truth_tripleMembershipFormula]
  rfl

theorem productColumnsEntry_correct {G I C : Type u} [Group G] [PartialOrder I] [PartialOrder C]
    (a : PosetAction G I) (s : Presentation I) (c : Presentation C) (t : Presentation G)
    (z : ZFSet.{u}) :
    Truth (productColumnsEntryFormula 0 1 2 3 4 5)
      (extend z (extend t.carrier (extend s.carrier (extend c.carrier
        (extend (s.product c).carrier (extend (a.actionGraph s t) Fin.elim0)))))) ↔
      z ∈ (a.productColumns C).actionGraph (s.product c) t := by
  rw [truth_productColumnsEntryFormula]
  constructor
  · rintro ⟨g, hg, i, hi, j, hj, k, hk, x, _, y, _, xeq, yeq, eq, rel⟩
    obtain ⟨g, rfl⟩ := (t.mem_carrier g).1 hg
    obtain ⟨i, rfl⟩ := (s.mem_carrier i).1 hi
    obtain ⟨j, rfl⟩ := (s.mem_carrier j).1 hj
    obtain ⟨k, rfl⟩ := (c.mem_carrier k).1 hk
    subst x
    subst y
    change z = ZFSet.pair (ZFSet.pair (t.encode g) (ZFSet.pair (s.encode i) (c.encode k)))
      (ZFSet.pair (s.encode j) (c.encode k)) at eq
    rw [eq]
    exact ((a.productColumns C).triple_mem_actionGraph (s.product c) t g (i, k) (j, k)).2
      (Prod.ext ((a.triple_mem_actionGraph s t g i j).1 rel) rfl)
  · intro member
    obtain ⟨g, i, k, eq⟩ := (a.mem_productColumns_actionGraph s c t z).1 member
    exact ⟨t.encode g, t.encode_mem g, s.encode i, s.encode_mem i,
      s.encode (a.iso g i), s.encode_mem _, c.encode k, c.encode_mem k,
      (s.product c).encode (i, k), (s.product c).encode_mem _,
      (s.product c).encode (a.iso g i, k), (s.product c).encode_mem _, rfl, rfl, eq,
      (a.triple_mem_actionGraph s t g i (a.iso g i)).2 rfl⟩

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G I C : Type u} [Group G] [PartialOrder I] [PartialOrder C]

theorem productColumns_actionGraph_mem
    (a : PosetAction G I) (s : Presentation I) (c : Presentation C) (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (rows : s.carrier ∈ M.sets) (columns : c.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (graph : a.actionGraph s t ∈ M.sets) :
    (a.productColumns C).actionGraph (s.product c) t ∈ M.sets := by
  have coordinates : (s.product c).carrier ∈ M.sets :=
    M.prod_mem pairing unions powers separation rows columns
  have bound := M.prod_mem pairing unions powers separation
    (M.prod_mem pairing unions powers separation group coordinates) coordinates
  let params := extend t.carrier (extend s.carrier (extend c.carrier
    (extend (s.product c).carrier (extend (a.actionGraph s t) Fin.elim0))))
  have members : ∀ k, params k ∈ M.sets :=
    Fin.cases group (Fin.cases rows (Fin.cases columns (Fin.cases coordinates
      (Fin.cases graph (fun k => Fin.elim0 k)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.productColumnsEntryFormula 0 1 2 3 4 5) params members bound
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.productColumnsEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod (ZFSet.prod t.carrier (s.product c).carrier) (s.product c).carrier) =
        (a.productColumns C).actionGraph (s.product c) t := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.productColumnsEntry_correct]
    exact ⟨And.right, fun hz => ⟨((t.product (s.product c)).graph_isFunc (s.product c)
      (fun x => (a.productColumns C).iso x.1 x.2)).1 hz, hz⟩⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end OAI
