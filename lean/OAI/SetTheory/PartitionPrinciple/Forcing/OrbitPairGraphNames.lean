import OAI.SetTheory.PartitionPrinciple.Definability.CountableSetFormulas
import OAI.SetTheory.PartitionPrinciple.Forcing.InitialRowForcing

namespace OAI


namespace PartitionPilot.Forcing.Name

open SetRealization
universe u v
variable {P Q R : Type u} {s : Presentation P}

noncomputable def rename (t : Presentation Q) (f : P → Q) (τ : Name s) : Name t :=
  assemble (fun a : Entries τ => rename t f a.val.1) (fun a => f a.val.2)
termination_by ZFSet.rank τ.val
decreasing_by exact entry_rank_lt a.property

theorem entry_rename (t : Presentation Q) (f : P → Q) (τ : Name s)
    (σ : Name t) (q : Q) :
    Entry σ (rename t f τ) q ↔
      ∃ ν p, Entry ν τ p ∧ rename t f ν = σ ∧ f p = q := by
  rw [rename, entry_assemble]
  constructor
  · rintro ⟨a, eq, hp⟩
    exact ⟨a.val.1, a.val.2, a.property, eq, hp⟩
  · rintro ⟨ν, p, h, eq, hp⟩
    exact ⟨⟨(ν, p), h⟩, eq, hp⟩

theorem rename_assemble (t : Presentation Q) (f : P → Q)
    {α : Type v} [Small.{u} α] (names : α → Name s) (conditions : α → P) :
    rename t f (assemble names conditions) =
      assemble (fun i => rename t f (names i)) (fun i => f (conditions i)) := by
  apply ext
  intro σ q
  rw [entry_rename, entry_assemble]
  constructor
  · rintro ⟨ν, p, h, eq, hp⟩
    obtain ⟨i, rfl, rfl⟩ := (entry_assemble names conditions ν p).1 h
    exact ⟨i, eq, hp⟩
  · rintro ⟨i, eq, hp⟩
    exact ⟨names i, conditions i,
      (entry_assemble names conditions _ _).2 ⟨i, rfl, rfl⟩, eq, hp⟩

theorem rename_id (τ : Name s) : rename s id τ = τ := by
  induction τ using inductionOn with
  | step τ ih =>
    apply ext
    intro σ p
    rw [entry_rename]
    constructor
    · rintro ⟨ν, q, h, eq, hp⟩
      rw [ih ν q h] at eq
      simpa only [id_eq, ← eq, ← hp] using h
    · intro h
      exact ⟨σ, p, h, ih σ p h, rfl⟩

theorem rename_comp (t : Presentation Q) (r : Presentation R)
    (f : P → Q) (g : Q → R) (τ : Name s) :
    rename r g (rename t f τ) = rename r (g ∘ f) τ := by
  induction τ using inductionOn with
  | step τ ih =>
    apply ext
    intro σ q
    rw [entry_rename, entry_rename]
    constructor
    · rintro ⟨ν, p, h, eq, hp⟩
      obtain ⟨χ, a, ha, rfl, rfl⟩ := (entry_rename t f τ ν p).1 h
      exact ⟨χ, a, ha, (ih χ a ha).symm.trans eq, hp⟩
    · rintro ⟨χ, a, ha, eq, hp⟩
      exact ⟨rename t f χ, f a, (entry_rename t f τ _ _).2 ⟨χ, a, ha, rfl, rfl⟩,
        (ih χ a ha).trans eq, hp⟩

theorem rename_empty (t : Presentation Q) (f : P → Q) :
    rename t f (empty s) = empty t := by
  apply ext
  intro σ p
  rw [entry_rename]
  constructor
  · rintro ⟨ν, q, h, _, _⟩
    exact False.elim (not_entry_empty ν q h)
  · exact False.elim ∘ not_entry_empty σ p

theorem rename_check (t : Presentation Q) (f : P → Q) (one : P) (x : ZFSet.{u}) :
    rename t f (check s one x) = check t (f one) x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    rw [check, rename_assemble, check]
    apply congrArg (fun names : x → Name t => assemble names (fun _ => f one))
    funext y
    exact ih y.val y.property

theorem rename_check_fixed (f : P → P) (one : P) (fixed : f one = one) (x : ZFSet.{u}) :
    rename s f (check s one x) = check s one x := by
  rw [rename_check, fixed]

theorem rename_singleton (t : Presentation Q) (f : P → Q) (one : P) (σ : Name s) :
    rename t f (singleton one σ) = singleton (f one) (rename t f σ) := by
  rw [singleton, rename_assemble]
  rfl

theorem rename_unorderedPair (t : Presentation Q) (f : P → Q)
    (one : P) (σ τ : Name s) :
    rename t f (unorderedPair one σ τ) =
      unorderedPair (f one) (rename t f σ) (rename t f τ) := by
  rw [unorderedPair, rename_assemble, unorderedPair]
  apply congrArg (fun names : Bool → Name t => assemble names (fun _ => f one))
  funext b
  cases b <;> rfl

theorem rename_orderedPair (t : Presentation Q) (f : P → Q)
    (one : P) (σ τ : Name s) :
    rename t f (orderedPair one σ τ) =
      orderedPair (f one) (rename t f σ) (rename t f τ) := by
  rw [orderedPair, rename_unorderedPair, rename_singleton, rename_unorderedPair]
  rfl

theorem eval_rename (t : Presentation Q) (f : P → Q) (H : Set Q) (τ : Name s) :
    eval H (rename t f τ) = eval {p | f p ∈ H} τ := by
  induction τ using inductionOn with
  | step τ ih =>
    apply ZFSet.ext
    intro x
    rw [mem_eval, mem_eval]
    constructor
    · rintro ⟨ν, q, h, hq, eq⟩
      obtain ⟨σ, p, hp, rfl, rfl⟩ := (entry_rename t f τ ν q).1 h
      exact ⟨σ, p, hp, hq, (ih σ p hp).symm.trans eq⟩
    · rintro ⟨σ, p, hp, hq, eq⟩
      exact ⟨rename t f σ, f p,
        (entry_rename t f τ _ _).2 ⟨σ, p, hp, rfl, rfl⟩,
        hq, (ih σ p hp).trans eq⟩

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps.CosetGeometry.OrderAction
universe u v

structure PosetAction (G : Type v) [Group G] (P : Type u) [PartialOrder P] where
  iso : G → P ≃o P
  one : ∀ p, iso 1 p = p
  mul : ∀ g h p, iso (g * h) p = iso g (iso h p)

namespace PosetAction
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

noncomputable def act (g : G) (τ : Name s) : Name s := Name.rename s (a.iso g) τ

theorem act_one (τ : Name s) : a.act s 1 τ = τ := by
  have eq : (a.iso 1 : P → P) = id := funext a.one
  change Name.rename s (a.iso 1) τ = τ
  rw [eq, Name.rename_id]

theorem act_mul (g h : G) (τ : Name s) :
    a.act s (g * h) τ = a.act s g (a.act s h τ) := by
  have eq : (a.iso (g * h) : P → P) = (a.iso g : P → P) ∘ a.iso h :=
    funext (a.mul g h)
  change Name.rename s (a.iso (g * h)) τ =
    Name.rename s (a.iso g) (Name.rename s (a.iso h) τ)
  rw [Name.rename_comp, eq]

theorem act_inv_left (g : G) (τ : Name s) : a.act s g⁻¹ (a.act s g τ) = τ := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_inv_right (g : G) (τ : Name s) : a.act s g (a.act s g⁻¹ τ) = τ := by
  rw [← act_mul, mul_inv_cancel, act_one]

noncomputable def nameEquiv (g : G) : Name s ≃ Name s where
  toFun := a.act s g
  invFun := a.act s g⁻¹
  left_inv := a.act_inv_left s g
  right_inv := a.act_inv_right s g

theorem entry_act (g : G) (σ τ : Name s) (p : P) :
    Name.Entry (a.act s g σ) (a.act s g τ) (a.iso g p) ↔ Name.Entry σ τ p := by
  change Name.Entry (a.act s g σ) (Name.rename s (a.iso g) τ) (a.iso g p) ↔ _
  rw [Name.entry_rename]
  constructor
  · rintro ⟨ν, q, h, eq, hp⟩
    have eqν : ν = σ := (a.nameEquiv s g).injective eq
    have eqp : q = p := (a.iso g).injective hp
    simpa only [← eqν, ← eqp] using h
  · intro h
    exact ⟨σ, p, h, rfl, rfl⟩

theorem eval_act (g : G) (H : Set P) (τ : Name s) :
    Name.eval H (a.act s g τ) = Name.eval {p | a.iso g p ∈ H} τ :=
  Name.eval_rename s (a.iso g) H τ

theorem act_check [OrderTop P] (g : G) (x : ZFSet.{u}) :
    a.act s g (Name.check s ⊤ x) = Name.check s ⊤ x :=
  Name.rename_check_fixed (a.iso g) ⊤ (a.iso g).map_top x

def stabilizer (τ : Name s) : Subgroup G where
  carrier := {g | a.act s g τ = τ}
  one_mem' := a.act_one s τ
  mul_mem' {g h} hg hh := by
    change a.act s (g * h) τ = τ
    change a.act s g τ = τ at hg
    change a.act s h τ = τ at hh
    rw [a.act_mul, hh, hg]
  inv_mem' {g} hg := by
    have eq := a.act_inv_left s g τ
    rw [hg] at eq
    exact eq

theorem stabilizer_conjugation (g : G) (τ : Name s) :
    a.stabilizer s (a.act s g τ) = (a.stabilizer s τ).map (conjugateHom g) := by
  apply Subgroup.ext
  intro h
  constructor
  · intro fixed
    let k := g⁻¹ * h * g
    have eq : conjugateHom g k = h := by simp [conjugateHom, k, mul_assoc]
    refine Subgroup.mem_map.2 ⟨k, ?_, eq⟩
    change a.act s (g⁻¹ * h * g) τ = τ
    rw [a.act_mul, a.act_mul]
    change a.act s h (a.act s g τ) = a.act s g τ at fixed
    rw [fixed, a.act_inv_left]
  · intro member
    obtain ⟨k, fixed, rfl⟩ := Subgroup.mem_map.1 member
    change a.act s (g * k * g⁻¹) (a.act s g τ) = a.act s g τ
    change a.act s k τ = τ at fixed
    rw [a.act_mul, a.act_mul, a.act_inv_left, fixed]

def pullbackFilter (g : G) (F : ConditionFilter P) : ConditionFilter P where
  mem p := F.mem (a.iso g p)
  nonempty := by
    obtain ⟨p, hp⟩ := F.nonempty
    exact ⟨(a.iso g).symm p, by simpa using hp⟩
  upward {p q} hp hpq := F.upward hp ((a.iso g).monotone hpq)
  directed {p q} hp hq := by
    obtain ⟨r, hr, rp, rq⟩ := F.directed hp hq
    refine ⟨(a.iso g).symm r, ?_, ?_, ?_⟩
    · simpa using hr
    · simpa using (a.iso g).symm.monotone rp
    · simpa using (a.iso g).symm.monotone rq

end PosetAction
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.PosetAction

open SetRealization
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem forcesEq_act (g : G) {p : P} {σ τ : Name s} (eq : Name.ForcesEq p σ τ) :
    Name.ForcesEq (a.iso g p) (a.act s g σ) (a.act s g τ) := by
  induction σ using Name.inductionOn generalizing p τ with
  | step σ ih =>
    rw [Name.ForcesEq] at eq ⊢
    constructor
    · intro ρ r entry q qp qr
      change Name.Entry ρ (Name.rename s (a.iso g) σ) r at entry
      obtain ⟨ρ₀, r₀, old, rfl, rfl⟩ := (Name.entry_rename s (a.iso g) σ ρ r).1 entry
      have oldp : (a.iso g).symm q ≤ p := by simpa using (a.iso g).symm.monotone qp
      have oldr : (a.iso g).symm q ≤ r₀ := by simpa using (a.iso g).symm.monotone qr
      obtain ⟨t, tq, ν, k, target, tk, childEq⟩ := eq.1 ρ₀ r₀ old _ oldp oldr
      refine ⟨a.iso g t, ?_, a.act s g ν, a.iso g k,
        (a.entry_act s g ν τ k).2 target, (a.iso g).monotone tk, ih ρ₀ r₀ old childEq⟩
      simpa using (a.iso g).monotone tq
    · intro ν k entry q qp qk
      change Name.Entry ν (Name.rename s (a.iso g) τ) k at entry
      obtain ⟨ν₀, k₀, old, rfl, rfl⟩ := (Name.entry_rename s (a.iso g) τ ν k).1 entry
      have oldp : (a.iso g).symm q ≤ p := by simpa using (a.iso g).symm.monotone qp
      have oldk : (a.iso g).symm q ≤ k₀ := by simpa using (a.iso g).symm.monotone qk
      obtain ⟨t, tq, ρ, r, target, tr, childEq⟩ := eq.2 ν₀ k₀ old _ oldp oldk
      refine ⟨a.iso g t, ?_, a.act s g ρ, a.iso g r,
        (a.entry_act s g ρ σ r).2 target, (a.iso g).monotone tr, ih ρ r target childEq⟩
      simpa using (a.iso g).monotone tq

theorem forcesEq_act_iff (g : G) (p : P) (σ τ : Name s) :
    Name.ForcesEq (a.iso g p) (a.act s g σ) (a.act s g τ) ↔ Name.ForcesEq p σ τ := by
  constructor
  · intro eq
    have old := a.forcesEq_act s g⁻¹ eq
    rw [← a.mul, inv_mul_cancel, a.one, a.act_inv_left, a.act_inv_left] at old
    exact old
  · exact a.forcesEq_act s g

theorem forcesMem_act (g : G) {p : P} {σ τ : Name s} (mem : Name.ForcesMem p σ τ) :
    Name.ForcesMem (a.iso g p) (a.act s g σ) (a.act s g τ) := by
  intro q qp
  have oldp : (a.iso g).symm q ≤ p := by simpa using (a.iso g).symm.monotone qp
  obtain ⟨t, tq, ν, r, entry, tr, eq⟩ := mem _ oldp
  refine ⟨a.iso g t, ?_, a.act s g ν, a.iso g r,
    (a.entry_act s g ν τ r).2 entry, (a.iso g).monotone tr, a.forcesEq_act s g eq⟩
  simpa using (a.iso g).monotone tq

theorem forcesMem_act_iff (g : G) (p : P) (σ τ : Name s) :
    Name.ForcesMem (a.iso g p) (a.act s g σ) (a.act s g τ) ↔ Name.ForcesMem p σ τ := by
  constructor
  · intro mem
    have old := a.forcesMem_act s g⁻¹ mem
    rw [← a.mul, inv_mul_cancel, a.one, a.act_inv_left, a.act_inv_left] at old
    exact old
  · exact a.forcesMem_act s g

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing.PosetAction
open SetRealization
universe u v
variable {P Q : Type u} {G : Type v} [Group G]
variable [PartialOrder P] [PartialOrder Q]
variable (a : PosetAction G P) (e : PosetAction G Q)
variable (s : Presentation P) (t : Presentation Q) (f : P → Q)
variable (equivariant : ∀ g p, f (a.iso g p) = e.iso g (f p))

include equivariant

theorem act_rename_of_equivariant (g : G) (τ : Name s) :
    e.act t g (Name.rename t f τ) = Name.rename t f (a.act s g τ) := by
  change Name.rename t (e.iso g) (Name.rename t f τ) =
    Name.rename t f (Name.rename s (a.iso g) τ)
  rw [Name.rename_comp, Name.rename_comp]
  have equal : (e.iso g : Q → Q) ∘ f = f ∘ a.iso g :=
    funext (fun p => (equivariant g p).symm)
  rw [equal]

theorem stabilizer_le_rename (τ : Name s) :
    a.stabilizer s τ ≤ e.stabilizer t (Name.rename t f τ) := by
  intro g fixed
  change e.act t g (Name.rename t f τ) = Name.rename t f τ
  change a.act s g τ = τ at fixed
  rw [a.act_rename_of_equivariant e s t f equivariant, fixed]

theorem support_le_rename {K : Subgroup G} {τ : Name s}
    (supported : K ≤ a.stabilizer s τ) :
    K ≤ e.stabilizer t (Name.rename t f τ) :=
  supported.trans (a.stabilizer_le_rename e s t f equivariant τ)

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps.CosetGeometry
universe u v
variable {A G : Type v} [Group G] {L : MeetOrder A} (geom : OrderAction G L)
variable {P : Type u} [PartialOrder P] (a : PosetAction G P) (s : Presentation P)

theorem act_eq_of_support_agreement {C : A} {τ : Name s} {g h : G}
    (support : geom.fixSubgroup C ≤ a.stabilizer s τ)
    (agree : ∀ z, L.le z C → (geom.iso g).toFun z = (geom.iso h).toFun z) :
    a.act s g τ = a.act s h τ := by
  have fixed : h⁻¹ * g ∈ geom.fixSubgroup C := by
    intro z hz
    rw [geom.mul, agree z hz, geom.act_inv_left]
  have eq := support fixed
  change a.act s (h⁻¹ * g) τ = τ at eq
  have translated := congrArg (a.act s h) eq
  rw [a.act_mul, a.act_inv_right] at translated
  exact translated

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps
universe u v w
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]

inductive HereditarilySymmetric (a : PosetAction G P) (s : Presentation P)
    (F : NormalSubgroupFamily G) : Name s → Prop
  | mk {τ} : F.mem (a.stabilizer s τ) →
      (∀ σ p, Name.Entry σ τ p → HereditarilySymmetric a s F σ) →
      HereditarilySymmetric a s F τ

namespace HereditarilySymmetric
variable {a : PosetAction G P} {s : Presentation P} {F : NormalSubgroupFamily G}

theorem symmetric {τ : Name s} (h : HereditarilySymmetric a s F τ) :
    F.mem (a.stabilizer s τ) := by
  cases h with
  | mk hs _ => exact hs

theorem member {τ σ : Name s} (h : HereditarilySymmetric a s F τ)
    {p : P} (entry : Name.Entry σ τ p) : HereditarilySymmetric a s F σ := by
  cases h with
  | mk _ children => exact children σ p entry

theorem translated {τ : Name s} (h : HereditarilySymmetric a s F τ) (g : G) :
    HereditarilySymmetric a s F (a.act s g τ) := by
  induction τ using Name.inductionOn with
  | step τ ih =>
    refine HereditarilySymmetric.mk ?_ ?_
    · rw [a.stabilizer_conjugation]
      exact F.conjugate g h.symmetric
    · intro ν p entry
      change Name.Entry ν (Name.rename s (a.iso g) τ) p at entry
      obtain ⟨σ, q, hσ, rfl, _⟩ := (Name.entry_rename s (a.iso g) τ ν p).1 entry
      exact ih σ q hσ (h.member hσ)

theorem assemble {α : Type w} [Small.{u} α] (names : α → Name s) (conditions : α → P)
    (sym : F.mem (a.stabilizer s (Name.assemble names conditions)))
    (children : ∀ i, HereditarilySymmetric a s F (names i)) :
    HereditarilySymmetric a s F (Name.assemble names conditions) := by
  refine HereditarilySymmetric.mk sym ?_
  intro σ p entry
  obtain ⟨i, rfl, _⟩ := (Name.entry_assemble names conditions σ p).1 entry
  exact children i

theorem assemble_common [OrderTop P] {α : Type w} [Small.{u} α]
    (names : α → Name s) (children : ∀ i, HereditarilySymmetric a s F (names i))
    (K : Subgroup G) (hK : F.mem K) (fixed : ∀ g ∈ K, ∀ i, a.act s g (names i) = names i) :
    HereditarilySymmetric a s F (Name.assemble names (fun _ => ⊤)) := by
  apply assemble names (fun _ => ⊤) _ children
  apply F.upward hK
  intro g hg
  change Name.rename s (a.iso g) (Name.assemble names (fun _ => ⊤)) = _
  rw [Name.rename_assemble]
  have top : a.iso g ⊤ = ⊤ := (a.iso g).map_top
  simp only [top]
  apply congrArg (fun ns : α → Name s => Name.assemble ns (fun _ => ⊤))
  funext i
  exact fixed g hg i

theorem check [OrderTop P] (a : PosetAction G P) (s : Presentation P)
    (F : NormalSubgroupFamily G) (x : ZFSet.{u}) :
    HereditarilySymmetric a s F (Name.check s ⊤ x) := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    rw [Name.check]
    exact assemble_common (fun y : x => Name.check s ⊤ y.val)
      (fun y => ih y.val y.property) ⊤ F.top (fun g _ y => a.act_check s g y.val)

theorem singleton [OrderTop P] {τ : Name s} (h : HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a s F (Name.singleton ⊤ τ) :=
  assemble_common (fun _ : Unit => τ) (fun _ => h) (a.stabilizer s τ) h.symmetric
    (fun _ fixed _ => fixed)

theorem unorderedPair [OrderTop P] {σ τ : Name s}
    (hσ : HereditarilySymmetric a s F σ) (hτ : HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a s F (Name.unorderedPair ⊤ σ τ) := by
  apply assemble_common (fun b : Bool => if b then σ else τ)
    (fun b => by cases b; exact hτ; exact hσ)
    (a.stabilizer s σ ⊓ a.stabilizer s τ) (F.inf hσ.symmetric hτ.symmetric)
  intro g fixed b
  cases b
  · exact fixed.2
  · exact fixed.1

theorem orderedPair [OrderTop P] {σ τ : Name s}
    (hσ : HereditarilySymmetric a s F σ) (hτ : HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a s F (Name.orderedPair ⊤ σ τ) :=
  hσ.singleton.unorderedPair (hσ.unorderedPair hτ)

end HereditarilySymmetric
end PartitionPilot.Forcing


section

namespace PartitionPilot.Forcing.Name.NameDomain

open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem empty_mem (D : NameDomain s) (nonempty : D.names.Nonempty) : empty s ∈ D.names := by
  classical
  have step : ∀ τ : Name s, τ ∈ D.names → empty s ∈ D.names := by
    intro τ
    induction τ using inductionOn with
    | step τ ih =>
      intro hτ
      by_cases member : ∃ σ p, Entry σ τ p
      · obtain ⟨σ, p, entry⟩ := member
        exact ih σ p entry (D.children hτ entry)
      · have eq : τ = empty s := by
          apply Name.ext
          intro σ p
          constructor
          · intro h
            exact False.elim (member ⟨σ, p, h⟩)
          · intro h
            exact False.elim (not_entry_empty σ p h)
        exact eq ▸ hτ
  obtain ⟨τ, hτ⟩ := nonempty
  exact step τ hτ

theorem empty_value_mem (D : NameDomain s) (nonempty : D.names.Nonempty) (H : Set P) :
    (∅ : ZFSet.{u}) ∈ D.values H :=
  (D.mem_values H ∅).2 ⟨empty s, D.empty_mem nonempty, eval_empty H⟩

end PartitionPilot.Forcing.Name.NameDomain

namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]

theorem empty_hs (a : PosetAction G P) (s : Presentation P) (F : NormalSubgroupFamily G) :
    HereditarilySymmetric a s F (Name.empty s) := by
  refine HereditarilySymmetric.mk (F.upward F.top ?_) ?_
  · intro g _
    exact Name.rename_empty s (a.iso g)
  · intro σ p entry
    exact False.elim (Name.not_entry_empty σ p entry)

end PartitionPilot.Forcing.PosetAction

namespace PartitionPilot.Forcing.SetFormula

open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem realize_emptySet (D : Name.NameDomain s) (nonempty : D.names.Nonempty) (H : Set P) :
    Realize (D.values H) emptySet Fin.elim0 := by
  rw [emptySet, realize_ex]
  refine ⟨∅, D.empty_value_mem nonempty H, ?_⟩
  intro x _ member
  exact ZFSet.notMem_empty x member

end PartitionPilot.Forcing.SetFormula

end


namespace PartitionPilot.Forcing.HereditarilySymmetric
open SetRealization Compression.RecursiveMaps
universe u v
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
variable {G : Type v} [Group G]
variable {a : PosetAction G P} {s : Presentation P}
variable (e : PosetAction G Q) (t : Presentation Q) (f : P → Q)
variable (equivariant : ∀ g p, f (a.iso g p) = e.iso g (f p))
variable {F : NormalSubgroupFamily G}
include equivariant

theorem rename {τ : Name s} (hs : HereditarilySymmetric a s F τ) :
    HereditarilySymmetric e t F (Name.rename t f τ) := by
  induction τ using Name.inductionOn with
  | step τ ih =>
    refine .mk ?_ ?_
    · exact F.upward hs.symmetric (a.stabilizer_le_rename e s t f equivariant τ)
    · intro ν q entry
      obtain ⟨σ, p, old, rfl, _⟩ := (Name.entry_rename t f τ ν q).1 entry
      exact ih σ p old (hs.member old)

end PartitionPilot.Forcing.HereditarilySymmetric



namespace PartitionPilot.Compression.RecursiveMaps.NormalSubgroupFamily

universe u
variable {G : Type u} [Group G]

theorem fin_iInf (F : NormalSubgroupFamily G) {n : Nat}
    (K : Fin n → Subgroup G) (hK : ∀ i, F.mem (K i)) : F.mem (⨅ i, K i) := by
  induction n with
  | zero =>
    apply F.upward F.top
    apply le_iInf
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    have split : (⨅ i, K i) = K 0 ⊓ ⨅ i : Fin n, K i.succ := by
      apply le_antisymm
      · exact le_inf (iInf_le K 0) (le_iInf (fun i => iInf_le K i.succ))
      · apply le_iInf
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact inf_le_left
        · exact le_trans inf_le_right (iInf_le (fun j : Fin n => K j.succ) j)
    rw [split]
    exact F.inf (hK 0) (ih (fun i => K i.succ) (fun i => hK i.succ))

end PartitionPilot.Compression.RecursiveMaps.NormalSubgroupFamily



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u
variable {G P : Type u} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P)

noncomputable def orbitPairGraph (tuple tau : Name s) : Name s :=
  assemble (fun g : G => orderedPair ⊤ (a.act s g tuple) (a.act s g tau)) (fun _ => ⊤)

theorem entry_orbitPairGraph (tuple tau sigma : Name s) (p : P) :
    Entry sigma (orbitPairGraph a s tuple tau) p ↔
      ∃ g : G, orderedPair ⊤ (a.act s g tuple) (a.act s g tau) = sigma ∧ p = ⊤ := by
  rw [orbitPairGraph, entry_assemble]
  exact exists_congr (fun _ => and_congr_right (fun _ => eq_comm))

theorem mem_eval_orbitPairGraph (tuple tau : Name s) (H : Set P) (topMember : (⊤ : P) ∈ H)
    (z : ZFSet.{u}) :
    z ∈ eval H (orbitPairGraph a s tuple tau) ↔
      ∃ g : G, ZFSet.pair (eval H (a.act s g tuple)) (eval H (a.act s g tau)) = z := by
  rw [mem_eval]
  constructor
  · rintro ⟨sigma, p, entry, _hp, equal⟩
    obtain ⟨g, rfl, rfl⟩ := (entry_orbitPairGraph a s tuple tau sigma p).1 entry
    exact ⟨g, (eval_orderedPair H ⊤ topMember _ _).symm.trans equal⟩
  · rintro ⟨g, equal⟩
    exact ⟨orderedPair ⊤ (a.act s g tuple) (a.act s g tau), ⊤,
      (entry_orbitPairGraph a s tuple tau _ ⊤).2 ⟨g, rfl, rfl⟩,
      topMember, (eval_orderedPair H ⊤ topMember _ _).trans equal⟩

private theorem act_pair (g : G) (x y : Name s) :
    a.act s g (orderedPair ⊤ x y) = orderedPair ⊤ (a.act s g x) (a.act s g y) := by
  change rename s (a.iso g) (orderedPair ⊤ x y) = _
  rw [rename_orderedPair, (a.iso g).map_top]
  rfl

theorem act_orbitPairGraph (tuple tau : Name s) (g : G) :
    a.act s g (orbitPairGraph a s tuple tau) = orbitPairGraph a s tuple tau := by
  apply Name.ext
  intro sigma p
  change Entry sigma (rename s (a.iso g) (orbitPairGraph a s tuple tau)) p ↔ _
  rw [entry_rename, entry_orbitPairGraph]
  constructor
  · rintro ⟨nu, q, entry, equal, condition⟩
    obtain ⟨h, rfl, rfl⟩ := (entry_orbitPairGraph a s tuple tau nu q).1 entry
    change a.act s g (orderedPair ⊤ (a.act s h tuple) (a.act s h tau)) = sigma at equal
    rw [act_pair, ← a.act_mul, ← a.act_mul] at equal
    exact ⟨g * h, equal, condition.symm.trans (a.iso g).map_top⟩
  · rintro ⟨h, rfl, rfl⟩
    refine ⟨orderedPair ⊤ (a.act s (g⁻¹ * h) tuple) (a.act s (g⁻¹ * h) tau), ⊤,
      (entry_orbitPairGraph a s tuple tau _ ⊤).2 ⟨g⁻¹ * h, rfl, rfl⟩, ?_, (a.iso g).map_top⟩
    change a.act s g (orderedPair ⊤ (a.act s (g⁻¹ * h) tuple) (a.act s (g⁻¹ * h) tau)) = _
    rw [act_pair, ← a.act_mul, ← a.act_mul, mul_inv_cancel_left]

theorem orbitPairGraph_hs (F : NormalSubgroupFamily G) (tuple tau : Name s)
    (tupleHS : HereditarilySymmetric a s F tuple) (tauHS : HereditarilySymmetric a s F tau) :
    HereditarilySymmetric a s F (orbitPairGraph a s tuple tau) := by
  apply HereditarilySymmetric.mk (F.upward F.top ?_) ?_
  · intro g _
    exact act_orbitPairGraph a s tuple tau g
  · intro sigma p entry
    obtain ⟨g, rfl, _⟩ := (entry_orbitPairGraph a s tuple tau sigma p).1 entry
    exact (tupleHS.translated g).orderedPair (tauHS.translated g)

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing

open SetRealization
universe u

namespace TransitiveGround

variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem pair_left {x y : ZFSet.{u}} (h : ZFSet.pair x y ∈ M.sets) : x ∈ M.sets :=
  M.transitive (M.transitive h (ZFSet.mem_pair.2 (Or.inl rfl))) (ZFSet.mem_singleton.2 rfl)

theorem pair_right {x y : ZFSet.{u}} (h : ZFSet.pair x y ∈ M.sets) : y ∈ M.sets :=
  M.transitive (M.transitive h (ZFSet.mem_pair.2 (Or.inr rfl))) (ZFSet.mem_pair.2 (Or.inr rfl))

def nameDomain : Name.NameDomain s where
  names := {τ | τ.val ∈ M.sets}
  children hτ entry := M.pair_left (M.transitive hτ entry)

theorem mem_nameDomain (τ : Name s) : τ ∈ (M.nameDomain s).names ↔ τ.val ∈ M.sets := Iff.rfl

theorem empty_mem (nonempty : M.sets.Nonempty) : (∅ : ZFSet.{u}) ∈ M.sets := by
  classical
  have descend : ∀ x : ZFSet.{u}, x ∈ M.sets → (∅ : ZFSet.{u}) ∈ M.sets := by
    intro x
    induction x using ZFSet.inductionOn with
    | h x ih =>
      intro hx
      by_cases member : ∃ y, y ∈ x
      · obtain ⟨y, hy⟩ := member
        exact ih y hy (M.transitive hx hy)
      · have eq : x = ∅ := by
          apply ZFSet.ext
          intro y
          exact ⟨fun h => False.elim (member ⟨y, h⟩), fun h => False.elim (ZFSet.notMem_empty y h)⟩
        exact eq ▸ hx
  obtain ⟨x, hx⟩ := nonempty
  exact descend x hx

theorem nameDomain_nonempty (nonempty : M.sets.Nonempty) : (M.nameDomain s).names.Nonempty :=
  ⟨Name.empty s, M.empty_mem nonempty⟩

theorem nameDomain_countable (small : M.sets.Countable) : (M.nameDomain s).names.Countable :=
  small.preimage Subtype.val_injective

theorem conditions_countable (small : M.sets.Countable) (carrier : s.carrier ∈ M.sets) :
    Countable P := by
  let : Countable M.sets := small
  let f : P → M.sets := fun p => ⟨s.encode p, M.transitive carrier (s.encode_mem p)⟩
  have injective : Function.Injective f := fun _ _ h => s.injective (congrArg Subtype.val h)
  exact injective.countable

end TransitiveGround
end PartitionPilot.Forcing

end OAI
