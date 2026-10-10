import OAI.SetTheory.PartitionPrinciple.Definability.GroundFlatCopyGraphs

namespace OAI


namespace PartitionPilot.Forcing

universe u

noncomputable def ordinalImageOrder (A N f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ m ∈ N, ∃ n ∈ N, z = ZFSet.pair m n ∧
    ∃ x ∈ A, ∃ y ∈ A, ZFSet.pair x m ∈ f ∧ ZFSet.pair y n ∈ f ∧ (x = y ∨ x ∈ y))
    (ZFSet.prod N N)

theorem ordinalImageOrder_subset (A N f : ZFSet.{u}) :
    ordinalImageOrder A N f ⊆ ZFSet.prod N N := fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem mem_ordinalImageOrder (A N f z : ZFSet.{u}) :
    z ∈ ordinalImageOrder A N f ↔ ∃ m ∈ N, ∃ n ∈ N, z = ZFSet.pair m n ∧
      ∃ x ∈ A, ∃ y ∈ A, ZFSet.pair x m ∈ f ∧ ZFSet.pair y n ∈ f ∧ (x = y ∨ x ∈ y) := by
  rw [ordinalImageOrder, ZFSet.mem_sep]
  exact ⟨And.right, fun h => ⟨by
    obtain ⟨m, hm, n, hn, eq, _⟩ := h
    exact eq.symm ▸ ZFSet.pair_mem_prod.2 ⟨hm, hn⟩, h⟩⟩

theorem pair_mem_ordinalImageOrder {A N f : ZFSet.{u}} (injection : InjectionCode A N f)
    (m n : ZFSet.{u}) :
    ZFSet.pair m n ∈ ordinalImageOrder A N f ↔
      ∃ x ∈ A, ∃ y ∈ A, ZFSet.pair x m ∈ f ∧ ZFSet.pair y n ∈ f ∧ (x = y ∨ x ∈ y) := by
  rw [mem_ordinalImageOrder]
  constructor
  · rintro ⟨a, _, b, _, eq, witnesses⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact witnesses
  · rintro ⟨x, hx, y, hy, xm, yn, order⟩
    exact ⟨m, (ZFSet.pair_mem_prod.1 (injection.function.1 xm)).2,
      n, (ZFSet.pair_mem_prod.1 (injection.function.1 yn)).2, rfl, x, hx, y, hy, xm, yn, order⟩

structure OrdinalOrderCode (A N f r : ZFSet.{u}) : Prop where
  ordinal : ordinalSetProperty A
  injection : InjectionCode A N f
  shape : r ⊆ ZFSet.prod N N
  order : ∀ m n, ZFSet.pair m n ∈ r ↔
    ∃ x ∈ A, ∃ y ∈ A, ZFSet.pair x m ∈ f ∧ ZFSet.pair y n ∈ f ∧ (x = y ∨ x ∈ y)

theorem ordinalImageOrder_code {A N f : ZFSet.{u}}
    (ordinal : ordinalSetProperty A) (injection : InjectionCode A N f) :
    OrdinalOrderCode A N f (ordinalImageOrder A N f) :=
  ⟨ordinal, injection, ordinalImageOrder_subset A N f, pair_mem_ordinalImageOrder injection⟩

theorem OrdinalOrderCode.eq_image {A N f r : ZFSet.{u}} (code : OrdinalOrderCode A N f r) :
    r = ordinalImageOrder A N f := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨m, _, n, _, rfl⟩ := ZFSet.mem_prod.1 (code.shape hz)
    exact (pair_mem_ordinalImageOrder code.injection m n).2 ((code.order m n).1 hz)
  · intro hz
    obtain ⟨m, _, n, _, rfl⟩ := ZFSet.mem_prod.1 (ordinalImageOrder_subset A N f hz)
    exact (code.order m n).2 ((pair_mem_ordinalImageOrder code.injection m n).1 hz)

end PartitionPilot.Forcing


section

namespace PartitionPilot.Forcing.OrdinalOrderCode

universe u
variable {A B N f g r : ZFSet.{u}}

theorem predecessor_exists (ha : OrdinalOrderCode A N f r) (hb : OrdinalOrderCode B N g r)
    {x y m : ZFSet.{u}} (hx : x ∈ A) (hy : y ∈ B)
    (fx : ZFSet.pair x m ∈ f) (gy : ZFSet.pair y m ∈ g)
    (z : ZFSet.{u}) (hz : z ∈ x) :
    ∃ w ∈ y, ∃ n, ZFSet.pair z n ∈ f ∧ ZFSet.pair w n ∈ g := by
  have hzA : z ∈ A := ha.ordinal.1 x hx z hz
  obtain ⟨n, fz, _⟩ := ha.injection.function.2 z hzA
  have relation : ZFSet.pair n m ∈ r :=
    (ha.order n m).2 ⟨z, hzA, x, hx, fz, fx, Or.inr hz⟩
  obtain ⟨w, _, v, _, gw, gv, lower⟩ := (hb.order n m).1 relation
  have vy : v = y := hb.injection.injective v y m gv gy
  rw [vy] at lower
  have different : w ≠ y := by
    intro same
    obtain ⟨k, _, unique⟩ := hb.injection.function.2 y hy
    have nm : n = m := (unique n (same ▸ gw)).trans (unique m gy).symm
    have zx : z = x := ha.injection.injective z x m (nm ▸ fz) fx
    exact ZFSet.mem_irrefl x (zx ▸ hz)
  exact ⟨w, lower.resolve_left different, n, fz, gw⟩

theorem matched_value_unique (ha : OrdinalOrderCode A N f r) (hb : OrdinalOrderCode B N g r) :
    ∀ x ∈ A, ∀ y ∈ B, ∀ m, ZFSet.pair x m ∈ f → ZFSet.pair y m ∈ g → x = y := by
  intro x
  induction x using ZFSet.inductionOn with
  | h x ih =>
    intro hx y hy m fx gy
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      obtain ⟨w, hw, n, fz, gw⟩ := ha.predecessor_exists hb hx hy fx gy z hz
      have same := ih z hz (ha.ordinal.1 x hx z hz) w (hb.ordinal.1 y hy w hw) n fz gw
      exact same.symm ▸ hw
    · intro hz
      obtain ⟨w, hw, n, gz, fw⟩ := hb.predecessor_exists ha hy hx gy fx z hz
      have same := ih w hw (ha.ordinal.1 x hx w hw) z (hb.ordinal.1 y hy z hz) n fw gz
      exact same ▸ hw

theorem domain_unique (ha : OrdinalOrderCode A N f r) (hb : OrdinalOrderCode B N g r) : A = B := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    obtain ⟨m, fx, _⟩ := ha.injection.function.2 x hx
    have diagonal : ZFSet.pair m m ∈ r :=
      (ha.order m m).2 ⟨x, hx, x, hx, fx, fx, Or.inl rfl⟩
    obtain ⟨y, hy, _, _, gy, _, _⟩ := (hb.order m m).1 diagonal
    exact (ha.matched_value_unique hb x hx y hy m fx gy).symm ▸ hy
  · intro hx
    obtain ⟨m, gx, _⟩ := hb.injection.function.2 x hx
    have diagonal : ZFSet.pair m m ∈ r :=
      (hb.order m m).2 ⟨x, hx, x, hx, gx, gx, Or.inl rfl⟩
    obtain ⟨y, hy, _, _, fy, _, _⟩ := (ha.order m m).1 diagonal
    exact (hb.matched_value_unique ha x hx y hy m gx fy).symm ▸ hy

end PartitionPilot.Forcing.OrdinalOrderCode

namespace PartitionPilot.Forcing

universe u

theorem ordinalImageOrder_domain_unique {A B N f g : ZFSet.{u}}
    (hA : ordinalSetProperty A) (hB : ordinalSetProperty B)
    (hf : InjectionCode A N f) (hg : InjectionCode B N g)
    (eq : ordinalImageOrder A N f = ordinalImageOrder B N g) : A = B := by
  have right : OrdinalOrderCode B N g (ordinalImageOrder A N f) :=
    eq.symm ▸ ordinalImageOrder_code hB hg
  exact (ordinalImageOrder_code hA hf).domain_unique right

end PartitionPilot.Forcing

end


namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def ordinalImagePairFormula {k} (m n a f : Fin k) : BoundedFormula k :=
  exMem a (exMem a.succ (.conj (pairMembershipFormula 1 m.succ.succ f.succ.succ)
    (.conj (pairMembershipFormula 0 n.succ.succ f.succ.succ) (disj (.equal 1 0) (.mem 1 0)))))

theorem truth_ordinalImagePairFormula {k} (m n a f : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (ordinalImagePairFormula m n a f) env ↔
      ∃ x ∈ env a, ∃ y ∈ env a, ZFSet.pair x (env m) ∈ env f ∧
        ZFSet.pair y (env n) ∈ env f ∧ (x = y ∨ x ∈ y) := by
  simp only [ordinalImagePairFormula, truth_exMem, Truth, truth_pairMembershipFormula, truth_disj]
  rfl

def ordinalImageEntryFormula {k} (z a n f : Fin k) : BoundedFormula k :=
  exMem n (exMem n.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (ordinalImagePairFormula 1 0 a.succ.succ f.succ.succ)))

theorem truth_ordinalImageEntryFormula {k} (z a n f : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (ordinalImageEntryFormula z a n f) env ↔
      env z ∈ ordinalImageOrder (env a) (env n) (env f) := by
  simp only [ordinalImageEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_ordinalImagePairFormula]
  exact (mem_ordinalImageOrder (env a) (env n) (env f) (env z)).symm

def ordinalImageFormula {k} (r a n f : Fin k) : BoundedFormula k :=
  .conj (.allMem r (ordinalImageEntryFormula 0 a.succ n.succ f.succ))
    (.allMem n (.allMem n.succ (imp (ordinalImagePairFormula 1 0 a.succ.succ f.succ.succ)
      (pairMembershipFormula 1 0 r.succ.succ))))

theorem truth_ordinalImageFormula {k} (r a n f : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (ordinalImageFormula r a n f) env ↔
      env r = ordinalImageOrder (env a) (env n) (env f) := by
  simp only [ordinalImageFormula, Truth, truth_ordinalImageEntryFormula,
    truth_imp, truth_ordinalImagePairFormula, truth_pairMembershipFormula]
  change ((∀ z ∈ env r, z ∈ ordinalImageOrder (env a) (env n) (env f)) ∧
    ∀ m ∈ env n, ∀ v ∈ env n,
      (∃ x ∈ env a, ∃ y ∈ env a, ZFSet.pair x m ∈ env f ∧
        ZFSet.pair y v ∈ env f ∧ (x = y ∨ x ∈ y)) → ZFSet.pair m v ∈ env r) ↔ _
  constructor
  · rintro ⟨subset, covers⟩
    apply ZFSet.ext
    intro z
    constructor
    · exact subset z
    · intro hz
      obtain ⟨m, hm, n, hn, eq, witnesses⟩ := (mem_ordinalImageOrder _ _ _ z).1 hz
      exact eq.symm ▸ covers m hm n hn witnesses
  · intro eq
    refine ⟨fun _ hz => eq ▸ hz, ?_⟩
    intro m hm n hn witnesses
    rw [eq]
    exact (mem_ordinalImageOrder _ _ _ _).2 ⟨m, hm, n, hn, rfl, witnesses⟩

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.SetFormula

def ordinalImageWitnessFormula : SetFormula 3 :=
  .conj (BoundedFormula.ordinalFormula 1).toFormula
    (ex (.conj (BoundedFormula.injectionFormula 2 3 0).toFormula
      (BoundedFormula.ordinalImageFormula 1 2 3 0).toFormula))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem ordinalImageOrder_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A N f : ZFSet.{u}} (hA : A ∈ M.sets) (hN : N ∈ M.sets) (hf : f ∈ M.sets) :
    ordinalImageOrder A N f ∈ M.sets := by
  let params := extend A (extend N (extend f Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.ordinalImageEntryFormula 0 1 2 3) params
    (Fin.cases hA (Fin.cases hN (Fin.cases hf (fun j => Fin.elim0 j))))
    (M.prod_mem pairing unions powers separation hN hN)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.ordinalImageEntryFormula 0 1 2 3) (extend z params)) (ZFSet.prod N N) =
      ordinalImageOrder A N f := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_ordinalImageEntryFormula]
    exact ⟨And.right, fun hz => ⟨ordinalImageOrder_subset A N f hz, hz⟩⟩
  exact eq ▸ selected

theorem realize_ordinalImageWitnessFormula {r A N : ZFSet.{u}}
    (hr : r ∈ M.sets) (hA : A ∈ M.sets) (hN : N ∈ M.sets) :
    Realize M.sets ordinalImageWitnessFormula (extend r (extend A (extend N Fin.elim0))) ↔
      ordinalSetProperty A ∧ ∃ f ∈ M.sets,
        InjectionCode A N f ∧ r = ordinalImageOrder A N f := by
  have members : ∀ j, (extend r (extend A (extend N Fin.elim0))) j ∈ M.sets :=
    Fin.cases hr (Fin.cases hA (Fin.cases hN (fun j => Fin.elim0 j)))
  have ordinal : Realize M.sets (BoundedFormula.ordinalFormula 1).toFormula
      (extend r (extend A (extend N Fin.elim0))) ↔ ordinalSetProperty A :=
    (BoundedFormula.realize_ordinalFormula M 1 _ members).trans (ordinalSetProperty_iff A).symm
  change (Realize M.sets (BoundedFormula.ordinalFormula 1).toFormula _ ∧
    Realize M.sets (ex _) _) ↔ _
  rw [ordinal, realize_ex]
  apply and_congr Iff.rfl
  apply exists_congr
  intro f
  apply and_congr_right
  intro hf
  have extended : ∀ j, (extend f (extend r (extend A (extend N Fin.elim0)))) j ∈ M.sets :=
    Fin.cases hf members
  change (Realize M.sets (BoundedFormula.injectionFormula 2 3 0).toFormula _ ∧
    Realize M.sets (BoundedFormula.ordinalImageFormula 1 2 3 0).toFormula _) ↔ _
  rw [BoundedFormula.realize_toFormula M _ _ extended,
    BoundedFormula.realize_toFormula M _ _ extended,
    BoundedFormula.truth_injectionFormula, BoundedFormula.truth_ordinalImageFormula]
  rfl

end PartitionPilot.Forcing.TransitiveGround

end OAI
