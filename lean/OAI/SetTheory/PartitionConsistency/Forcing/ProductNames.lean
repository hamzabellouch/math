import Mathlib
import OAI.SetTheory.PartitionConsistency.Forcing.EquivariantMixing
import OAI.SetTheory.PartitionConsistency.Forcing.ProductForcing

namespace OAI

/-! ## ProductSystem -/

namespace PartitionConsistency.SetForcingNames
universe u v
noncomputable section

/-- A genuine small set of condition codes, obtained by wellordering the
condition type. The codes carry no forcing or satisfaction information. -/
def posetCode (P : Type u) (p : P) : ZFSet.{u} :=
  (Ordinal.typein (@WellOrderingRel P) p).toZFSet

theorem posetCode_injective (P : Type u) : Function.Injective (posetCode P) :=
  Ordinal.toZFSet_injective.comp (Ordinal.typein_injective _)

def conditionSet (P : Type u) : ZFSet.{u} := ZFSet.range (posetCode P)

def conditionEquiv (P : Type u) : P ≃ conditionSet P := Equiv.ofBijective
  (fun p => ⟨posetCode P p, ZFSet.mem_range.mpr ⟨p,rfl⟩⟩)
  ⟨fun _ _ h => posetCode_injective P (congrArg Subtype.val h),
    fun p => by
      obtain ⟨q,hq⟩ := ZFSet.mem_range.mp p.property
      exact ⟨q,Subtype.ext hq⟩⟩

namespace SymmetricSystem
variable {P : Type u} [PartialOrder P] {Γ : Type v} [Group Γ]
  (r : Γ →* (P ≃o P))

/-- Conjugating an honest order action by the coding equivalence. -/
def codedAction : ConditionAction.{u} Γ where
  conditions := conditionSet P
  perm := {
    toFun g := ((conditionEquiv P).symm.trans (r g).toEquiv).trans (conditionEquiv P)
    map_one' := by ext p; simp
    map_mul' := by intro g h; ext p; simp }

def ofOrderAction (F : Set (Subgroup Γ)) (hF : SupportFilter.IsNormalFilter F) :
    SymmetricSystem.{u} P Γ where
  action := codedAction r
  codeEquiv := conditionEquiv P
  order g p q := by
    change (conditionEquiv P).symm ((conditionEquiv P) ((r g) ((conditionEquiv P).symm ((conditionEquiv P) p)))) ≤
      (conditionEquiv P).symm ((conditionEquiv P) ((r g) ((conditionEquiv P).symm ((conditionEquiv P) q)))) ↔ _
    simp
  filter := F
  normal := hF

@[simp] theorem move_ofOrderAction (F : Set (Subgroup Γ)) (hF : SupportFilter.IsNormalFilter F)
    (g : Γ) (p : P) : (ofOrderAction r F hF).move g p = r g p := by
  change (conditionEquiv P).symm ((conditionEquiv P) ((r g) ((conditionEquiv P).symm ((conditionEquiv P) p)))) = _
  simp

@[simp] theorem code_ofOrderAction (F : Set (Subgroup Γ)) (hF : SupportFilter.IsNormalFilter F)
    (p : P) : (ofOrderAction r F hF).code p = posetCode P p := rfl

end SymmetricSystem
end
end PartitionConsistency.SetForcingNames

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]

/-- The paper explicitly allows adjoining a fixed largest condition. -/
abbrev Poset (M I κ : Type u) := WithTop (Condition M I κ)

def actionHom : Equiv.Perm I →* (Poset M I κ ≃o Poset M I κ) where
  toFun π := (permuteOrderIso π).withTopCongr
  map_one' := by
    ext p
    induction p using WithTop.recTopCoe with
    | top => rfl
    | coe p => exact congrArg WithTop.some (permute_one p)
  map_mul' π σ := by
    ext p
    induction p using WithTop.recTopCoe with
    | top => rfl
    | coe p => exact congrArg WithTop.some (permute_mul π σ p)

/-- The literal Cohen/diagram symmetric system, with exactly the small-support
subgroup filter. Neither ZF nor any target axiom is a structure field. -/
def system {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) :
    SymmetricSystem.{u} (Poset M I κ) (Equiv.Perm I) :=
  SymmetricSystem.ofOrderAction actionHom (SupportFilter.subgroupFilter μ)
    (SupportFilter.isNormalFilter hμ)

variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

@[simp] theorem move_coe (π : Equiv.Perm I) (p : Condition M I κ) :
    (system (M := M) (κ := κ) hμ).move π (p : Poset M I κ) =
      (permute π p : Poset M I κ) := by
  rw [system,SymmetricSystem.move_ofOrderAction]; rfl

@[simp] theorem move_top (π : Equiv.Perm I) :
    (system (M := M) (I := I) (κ := κ) hμ).move π ⊤ = ⊤ := by
  rw [system,SymmetricSystem.move_ofOrderAction]; rfl

/-- Full ZF follows from the already proved unbounded HS-name theorem for
this actual action and filter. This is not a proof of the extra axioms. -/
theorem forces_ZF (p : Poset M I κ) :
    ∀ φ ∈ SetLanguage.ZF, (system hμ).Forces Fin.elim0 p φ :=
  (system hμ).forces_ZF p

/-- Each HS name has a literal support of size at most the prescribed bound. -/
theorem name_support (σ : (system (M := M) (I := I) (κ := κ) hμ).Name) :
    ∃ J : Set I, Cardinal.mk J ≤ μ ∧ ∀ π ∈ SupportFilter.Fix J, π • σ = σ := by
  obtain ⟨J,hJ,hfix⟩ := σ.hs.symmetric
  refine ⟨J,hJ,?_⟩
  intro π hπ
  exact Subtype.ext (hfix hπ)

end
end PartitionConsistency.ProductForcing


/-! ## Label -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w t
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

@[simp] theorem Name.smul_check (g : Γ) (x : ZFSet.{u}) :
    g • (Name.check (S := S) x) = Name.check x := by
  apply Subtype.ext
  exact ConditionAction.Name.smul_check (S.code_mem ⊤) g (S.code_top_fixed g) x

/-- Check names reflect ground equality at every condition. This uses
well-foundedness of actual sets, and does not presume a generic extension. -/
theorem eq_check_iff (x y : ZFSet.{u}) (p : P) :
    S.atomic.EqF p (Name.check x) (Name.check y) ↔ x = y := by
  suffices h : ∀ x y : ZFSet.{u}, ∀ p : P,
      S.atomic.EqF p (Name.check x) (Name.check y) → x = y from
    ⟨h x y p, fun h => h ▸ S.atomic.eq_refl p (Name.check x)⟩
  intro x
  induction x using ZFSet.mem_wf.induction with
  | h x ih =>
    intro y p he
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      have hm := (S.atomic.mem_congr (S.atomic.eq_refl p (Name.check z)) he).mp
        (S.check_mem_of_mem hz p)
      obtain ⟨r,_,a,ha,he'⟩ := (S.mem_check y (Name.check z) p).mp hm p le_rfl
      exact (ih z hz a r he').symm ▸ ha
    · intro hz
      have hm := (S.atomic.mem_congr (S.atomic.eq_refl p (Name.check z)) he).mpr
        (S.check_mem_of_mem hz p)
      obtain ⟨r,_,a,ha,he'⟩ := (S.mem_check x (Name.check z) p).mp hm p le_rfl
      exact ih a ha z r (S.atomic.eq_symm he') ▸ ha

@[simp] theorem mem_check_check (x y : ZFSet.{u}) (p : P) :
    S.atomic.MemF p (Name.check x) (Name.check y) ↔ x ∈ y := by
  refine ⟨fun h => ?_,fun h => S.check_mem_of_mem h p⟩
  obtain ⟨r,_,z,hz,he⟩ := (S.mem_check y (Name.check x) p).mp h p le_rfl
  rw [(S.eq_check_iff x z r).mp he]
  exact hz

omit [OrderTop P] in
/-- Exact transport of a set-sized collected entry family. -/
theorem collectRaw_move {ι : Type t} [Small.{u} ι]
    (f f' : ι → S.Name) (R R' : ι → P → Prop) (g : Γ) (e : Equiv.Perm ι)
    (hf : ∀ i, g • f i = f' (e i))
    (hR : ∀ i p, R i p ↔ R' (e i) (S.move g p)) :
    mapConditions (S.action.actCode g) (S.collectRaw f R) = S.collectRaw f' R' := by
  apply ZFSet.ext
  intro z
  constructor
  · intro h
    obtain ⟨ν,c,he,rfl⟩ := mem_mapConditions_iff.mp h
    obtain ⟨i,p,hi,rfl,rfl⟩ := (S.edge_collectRaw f R ν c).mp he
    refine (S.mem_collectRaw f' R' _).mpr ⟨e i,S.move g p,(hR i p).mp hi,?_⟩
    rw [← hf,Name.smul_val,S.actCode_code]
  · intro h
    obtain ⟨i,p,hi,rfl⟩ := (S.mem_collectRaw f' R' _).mp h
    apply mem_mapConditions_iff.mpr
    refine ⟨(f (e.symm i)).raw,S.code ((S.move g).symm p),?_,?_⟩
    · apply (S.edge_collectRaw f R _ _).mpr
      exact ⟨e.symm i,(S.move g).symm p,(hR _ _).mpr (by simpa using hi),rfl,rfl⟩
    · rw [S.actCode_code,OrderIso.apply_symm_apply]
      have hh := congrArg Name.raw (hf (e.symm i))
      simpa only [Name.smul_val,Equiv.apply_symm_apply] using congrArg (fun a => ZFSet.pair a (S.code p)) hh

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- The Boolean assignment actually contained in a product condition. The
adjoined top condition supplies no assignment. -/
def Bit (p : Poset M I κ) (j : I) (α : κ) (b : Bool) : Prop :=
  ∃ q : Condition M I κ, p = q ∧ ((j,α),b) ∈ q.1.graph

omit [LeftCancelMonoid M] [DiagramOrder.IsConical M] in
@[simp] theorem bit_coe (p : Condition M I κ) (j : I) (α : κ) (b : Bool) :
    Bit (p : Poset M I κ) j α b ↔ ((j,α),b) ∈ p.1.graph := by
  simp only [Bit,WithTop.coe_inj]
  exact ⟨fun ⟨q,hq,h⟩ => hq ▸ h,fun h => ⟨p,rfl,h⟩⟩

omit [LeftCancelMonoid M] [DiagramOrder.IsConical M] in
@[simp] theorem not_bit_top (j : I) (α : κ) (b : Bool) :
    ¬ Bit (⊤ : Poset M I κ) j α b := by simp [Bit]

theorem bit_mono {p q : Poset M I κ} (h : q ≤ p) {j : I} {α : κ} {b : Bool}
    (hb : Bit p j α b) : Bit q j α b := by
  obtain ⟨p,rfl,hb⟩ := hb
  induction q using WithTop.recTopCoe with
  | top => simp at h
  | coe q =>
    exact (bit_coe q j α b).mpr ((WithTop.coe_le_coe.mp h).1 hb)

omit [LeftCancelMonoid M] [DiagramOrder.IsConical M] in
theorem bit_functional {p : Poset M I κ} {j : I} {α : κ} {b c : Bool}
    (hb : Bit p j α b) (hc : Bit p j α c) : b = c := by
  obtain ⟨q,rfl,hb⟩ := hb
  exact q.1.functional _ _ _ hb ((bit_coe q j α c).mp hc)

@[simp] theorem bit_move (π : Equiv.Perm I) (p : Poset M I κ)
    (j : I) (α : κ) (b : Bool) :
    Bit ((system (M := M) (I := I) (κ := κ) hμ).move π p) (π j) α b ↔ Bit p j α b := by
  induction p using WithTop.recTopCoe with
  | top => simp
  | coe p => simp [permute,CohenForcing.Condition.mem_permute]

/-- An index is coded by an actual ground set (eventually a ground ordinal).
At coordinate j the name has precisely the positively assigned indices. -/
def label (c : κ → ZFSet.{u}) (j : I) : (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system (M := M) (I := I) (κ := κ) hμ).collect (fun α : κ => Name.check (c α))
    (fun α p => Bit p j α true) (SupportFilter.Fix {j})
    ⟨{j},by simpa using (Cardinal.one_le_aleph0.trans hμ),le_rfl⟩ (by
      intro π hπ α p hp
      refine ⟨α,by simp,?_⟩
      have hj : π j = j := (SupportFilter.mem_Fix {j} π).mp hπ j (Set.mem_singleton j)
      simpa only [hj] using (bit_move hμ π p j α true).mpr hp)

@[simp] theorem label_raw (c : κ → ZFSet.{u}) (j : I) :
    (label (M := M) hμ c j).raw = (system (M := M) (I := I) (κ := κ) hμ).collectRaw
      (fun α : κ => Name.check (c α)) (fun α p => Bit p j α true) := rfl

@[simp] theorem smul_label (c : κ → ZFSet.{u}) (π : Equiv.Perm I) (j : I) :
    π • label (M := M) hμ c j = label (M := M) hμ c (π j) := by
  apply Name.ext
  rw [Name.smul_val,label_raw,label_raw]
  apply (system (M := M) (I := I) (κ := κ) hμ).collectRaw_move _ _ _ _ π (Equiv.refl κ)
  · intro α; simp
  · intro α p; exact (bit_move hμ π p j α true).symm

/-- Positive bits force their ground indices into the named label. -/
theorem mem_label_of_bit (c : κ → ZFSet.{u}) {j : I} {α : κ} {p : Poset M I κ}
    (hb : Bit p j α true) : (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF p (Name.check (c α)) (label (M := M) hμ c j) := by
  apply (system (M := M) (I := I) (κ := κ) hμ).mem_of_edge (c := p) ?_ le_rfl
  rw [label_raw]
  exact ((system (M := M) (I := I) (κ := κ) hμ).edge_collectRaw _ _ _ _).mpr ⟨α,p,hb,rfl,rfl⟩

/-- The complete local-witness membership characterization of a canonical label. -/
theorem mem_label (c : κ → ZFSet.{u}) (j : I) (ν : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF p ν (label (M := M) hμ c j) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ α : κ, Bit r j α true ∧
        (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF r ν (Name.check (c α)) := by
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,τ,d,he,hrd,heq⟩ := (system (M := M) (I := I) (κ := κ) hμ).mem_iff.mp h q hqp
    rw [label_raw] at he
    obtain ⟨α,d',hα,hτ,hd⟩ := ((system (M := M) (I := I) (κ := κ) hμ).edge_collectRaw _ _ _ _).mp he
    have hh : Name.check (S := system (M := M) (I := I) (κ := κ) hμ) (c α) = τ := Name.ext hτ
    obtain rfl := (system (M := M) (I := I) (κ := κ) hμ).code_injective hd
    exact ⟨r,hrq,α,bit_mono hrd hα,hh ▸ heq⟩
  · intro h
    apply (system (M := M) (I := I) (κ := κ) hμ).mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,α,hα,he⟩ := h q hqp
    exact ⟨r,hrq,Name.check (c α),r,
      by rw [label_raw]; exact ((system (M := M) (I := I) (κ := κ) hμ).edge_collectRaw _ _ _ _).mpr ⟨α,r,hα,rfl,rfl⟩,le_rfl,he⟩

/-- Negative bits force nonmembership; injectivity here is injectivity of the
ordinary ground-coordinate coding, not an assumed distinctness of labels. -/
theorem not_mem_label_of_bit (c : κ → ZFSet.{u}) (hc : Function.Injective c)
    {j : I} {α : κ} {p : Poset M I κ} (hb : Bit p j α false) :
    ¬ (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF p (Name.check (c α)) (label (M := M) hμ c j) := by
  intro hm
  obtain ⟨r,hrp,β,hβ,heq⟩ := (mem_label (M := M) hμ c j _ p).mp hm p le_rfl
  have hαβ := hc (((system (M := M) (I := I) (κ := κ) hμ).eq_check_iff (c α) (c β) r).mp heq)
  subst β
  have hbad := bit_functional (bit_mono hrp hb) hβ
  cases hbad

/-- Distinct index coordinates give forced-distinct actual set names, below
every product condition. -/
theorem label_not_equal [Uncountable κ] (c : κ → ZFSet.{u})
    (hc : Function.Injective c) [Nonempty (DiagramForcing.Diagram M I)]
    {j k : I} (hjk : j ≠ k) (p : Poset M I κ) :
    ¬ (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF p (label (M := M) hμ c j) (label (M := M) hμ c k) := by
  intro heq
  suffices hh : ∀ q : Condition M I κ, q ≤ p → False by
    induction p using WithTop.recTopCoe with
    | top => exact hh (⊤,Classical.choice inferInstance) le_top
    | coe p => exact hh p le_rfl
  intro q hqp
  obtain ⟨d,α,hdq,hj,hk⟩ := CohenForcing.Condition.separate_labels q.1 hjk
  let r : Condition M I κ := (d,q.2)
  have hrq : (r : Poset M I κ) ≤ q := WithTop.coe_le_coe.mpr ⟨hdq,le_rfl⟩
  have hej := (system (M := M) (I := I) (κ := κ) hμ).atomic.eq_mono (hrq.trans hqp) heq
  have hm : (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF (r : Poset M I κ) (Name.check (c α)) (label (M := M) hμ c k) :=
    mem_label_of_bit hμ c ((bit_coe r k α true).mpr hk)
  exact not_mem_label_of_bit hμ c hc ((bit_coe r j α false).mpr hj)
    (((system (M := M) (I := I) (κ := κ) hμ).atomic.mem_congr ((system (M := M) (I := I) (κ := κ) hμ).atomic.eq_refl _ _) hej).mpr hm)

/-- The invariant set of all canonical generic labels. -/
def labelSet (c : κ → ZFSet.{u}) : (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system (M := M) (I := I) (κ := κ) hμ).collect (label (M := M) hμ c) (fun _ p => p = ⊤) ⊤ (system (M := M) (I := I) (κ := κ) hμ).normal.1 (by
    intro π _ j p hp
    refine ⟨π j,(smul_label (M := M) hμ c π j).symm,?_⟩
    simp only [hp,move_top])

@[simp] theorem labelSet_raw (c : κ → ZFSet.{u}) :
    (labelSet (M := M) (I := I) hμ c).raw =
      (system (M := M) (I := I) (κ := κ) hμ).collectRaw (label (M := M) hμ c) (fun _ p => p = ⊤) := rfl

@[simp] theorem smul_labelSet (c : κ → ZFSet.{u}) (π : Equiv.Perm I) :
    π • labelSet (M := M) (I := I) hμ c = labelSet (M := M) (I := I) hμ c := by
  apply Name.ext
  rw [Name.smul_val,labelSet_raw]
  apply (system (M := M) (I := I) (κ := κ) hμ).collectRaw_move _ _ _ _ π π
  · exact smul_label (M := M) hμ c π
  · intro i p
    constructor
    · rintro rfl; exact move_top hμ π
    · intro hp
      apply ((system (M := M) (I := I) (κ := κ) hμ).move π).injective
      rw [hp,move_top]

theorem label_mem_labelSet (c : κ → ZFSet.{u}) (j : I) (p : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF p (label (M := M) hμ c j) (labelSet (M := M) (I := I) hμ c) := by
  apply (system (M := M) (I := I) (κ := κ) hμ).mem_of_edge (c := ⊤) ?_ le_top
  rw [labelSet_raw]
  exact ((system (M := M) (I := I) (κ := κ) hμ).edge_collectRaw _ _ _ _).mpr ⟨j,⊤,rfl,rfl,rfl⟩

theorem mem_labelSet (c : κ → ZFSet.{u}) (ν : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p : Poset M I κ) : (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF p ν (labelSet (M := M) (I := I) hμ c) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ j : I, (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF r ν (label (M := M) hμ c j) := by
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,τ,d,he,_,heq⟩ := (system (M := M) (I := I) (κ := κ) hμ).mem_iff.mp h q hqp
    rw [labelSet_raw] at he
    obtain ⟨j,_,_,hτ,_⟩ := ((system (M := M) (I := I) (κ := κ) hμ).edge_collectRaw _ _ _ _).mp he
    have hh : label (M := M) hμ c j = τ := Name.ext hτ
    exact ⟨r,hrq,j,hh ▸ heq⟩
  · intro h
    apply (system (M := M) (I := I) (κ := κ) hμ).mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,j,heq⟩ := h q hqp
    exact ⟨r,hrq,label (M := M) hμ c j,⊤,
      by rw [labelSet_raw]; exact ((system (M := M) (I := I) (κ := κ) hμ).edge_collectRaw _ _ _ _).mpr ⟨j,⊤,rfl,rfl,rfl⟩,le_top,heq⟩

end
end PartitionConsistency.ProductForcing


/-! ## FunctionName -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Application is the forcing of the literal internal ordered-pair graph
formula. It does not replace a set function by an external function. -/
def App (p : P) (f x y : S.Name) : Prop :=
  S.Forces ![f,x,y] p (SetLanguage.edge 0 1 2)

theorem forces_edge {n} (v : Fin n → S.Name) (p : P) (f x y : Fin n) :
    S.Forces v p (SetLanguage.edge f x y) ↔ S.App p (v f) (v x) (v y) := by
  simp only [App, Forces, SetLanguage.edge, S.atomic.forceFormula_rename S.atomic_regular]
  have hv : v ∘ ![f,x,y] = ![v f,v x,v y] ∘ ![0,1,2] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]

theorem app_mono {p q : P} {f x y : S.Name} (h : q ≤ p) (ha : S.App p f x y) :
    S.App q f x y := S.atomic.forceFormula_mono h ha

theorem app_congr {p : P} {f f' x x' y y' : S.Name}
    (hf : S.atomic.EqF p f f') (hx : S.atomic.EqF p x x') (hy : S.atomic.EqF p y y') :
    S.App p f x y ↔ S.App p f' x' y' := by
  apply S.atomic.forceFormula_tuple_congr
  intro i
  fin_cases i <;> assumption

theorem app_symmetry (g : Γ) (p : P) (f x y : S.Name) :
    S.App p f x y ↔ S.App (S.move g p) (g • f) (g • x) (g • y) := by
  have h := S.forces_symmetry g (SetLanguage.edge 0 1 2) ![f,x,y] p
  simpa only [S.forces_edge,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using h

/-- The totality/uniqueness conjunct of the internal set-function sentence. -/
theorem functionOn_total {n} (v : Fin n → S.Name) (p : P) (f d : Fin n)
    (hf : S.Forces v p (SetLanguage.functionOn f d))
    (x : S.Name) {q : P} (hqp : q ≤ p) (hx : S.atomic.MemF q x (v d)) :
    ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ y : S.Name, S.App s (v f) x y ∧
      ∀ z : S.Name, ∀ t, t ≤ s → S.App t (v f) x z → S.atomic.EqF t z y := by
  simp only [Forces,SetLanguage.functionOn,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,ForcingQuotient.AtomicData.forceFormula_ex,
    ForcingQuotient.AtomicData.forceFormula_mem,ForcingQuotient.AtomicData.forceFormula_equal,
    S.forces_edge] at hf
  exact hf.2 x q hqp hx

/-- Forced single-valuedness, with three unrestricted HS names as arguments. -/
theorem functionOn_unique {n} (v : Fin n → S.Name) (p : P) (f d : Fin n)
    (hf : S.Forces v p (SetLanguage.functionOn f d))
    (x y z : S.Name) (hx : S.atomic.MemF p x (v d))
    (hy : S.App p (v f) x y) (hz : S.App p (v f) x z) : S.atomic.EqF p y z := by
  apply S.atomic_regular.1 p y z
  intro q hqp
  obtain ⟨r,hrq,a,_,ha⟩ := S.functionOn_total v p f d hf x le_rfl hx q hqp
  exact ⟨r,hrq,S.atomic.eq_trans (ha y r le_rfl (S.app_mono (hrq.trans hqp) hy))
    (S.atomic.eq_symm (ha z r le_rfl (S.app_mono (hrq.trans hqp) hz)))⟩

theorem forces_nonempty {n} (v : Fin n → S.Name) (p : P) (a : Fin n) :
    S.Forces v p (SetLanguage.nonempty a) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x : S.Name, S.atomic.MemF r x (v a) := by
  simp only [Forces,SetLanguage.nonempty,S.atomic.forceFormula_rename S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_ex,ForcingQuotient.AtomicData.forceFormula_mem]
  rfl

/-- Unpacking a choice function retains exactly the original graph formula. -/
theorem forces_choiceOn {n} (v : Fin n → S.Name) (p : P) (c a : Fin n) :
    S.Forces v p (SetLanguage.choiceOn c a) ↔
      S.Forces ![v c,v a] p (SetLanguage.functionOn 0 1) ∧
      ∀ x : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x (v a) →
        ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ y : S.Name,
          S.App s (v c) x y ∧ S.atomic.MemF s y x := by
  simp only [Forces,SetLanguage.choiceOn,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,ForcingQuotient.AtomicData.forceFormula_ex,
    ForcingQuotient.AtomicData.forceFormula_mem,S.forces_edge]
  have hv : v ∘ ![c,a] = ![v c,v a] := by
    funext i
    fin_cases i <;> rfl
  simp [hv,Fin.snoc]

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
