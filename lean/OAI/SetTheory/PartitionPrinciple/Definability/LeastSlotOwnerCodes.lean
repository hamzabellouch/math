import OAI.SetTheory.PartitionPrinciple.Geometry.TileStarIncomingCodes

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

def LeastSupportCode (V omega depths supports x v : ZFSet.{u}) : Prop :=
  ZFSet.pair v x ∈ supports ∧ ∃ n ∈ omega, ZFSet.pair v n ∈ depths ∧
    ∀ w ∈ V, ∀ m ∈ omega, ZFSet.pair w x ∈ supports → ZFSet.pair w m ∈ depths → m ∉ n

noncomputable def leastSupportGraph (V Q depths supports : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ Q, ∃ v ∈ V, z = ZFSet.pair x v ∧
    LeastSupportCode V ZFSet.omega depths supports x v) (ZFSet.prod Q V)

theorem pair_mem_leastSupportGraph (V Q depths supports x v : ZFSet.{u}) :
    ZFSet.pair x v ∈ leastSupportGraph V Q depths supports ↔
      x ∈ Q ∧ v ∈ V ∧ LeastSupportCode V ZFSet.omega depths supports x v := by
  rw [leastSupportGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, x', hx, v', hv, equal, body⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx, hv, body⟩
  · rintro ⟨hx, hv, body⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hv⟩, x, hx, v, hv, rfl, body⟩

namespace BoundedFormula
def leastSupportFormula {k} (V omega depths supports x v : Fin k) : BoundedFormula k :=
  .conj (pairMembershipFormula v x supports)
    (exMem omega (.conj (pairMembershipFormula v.succ 0 depths.succ)
      (allMem V.succ (allMem omega.succ.succ
        (.imp (pairMembershipFormula 1 x.succ.succ.succ supports.succ.succ.succ)
          (.imp (pairMembershipFormula 1 0 depths.succ.succ.succ) (.neg (.mem 0 2))))))))

theorem truth_leastSupportFormula {k} (V omega depths supports x v : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (leastSupportFormula V omega depths supports x v) env ↔
      LeastSupportCode (env V) (env omega) (env depths) (env supports) (env x) (env v) := by
  simp only [leastSupportFormula, Truth, truth_exMem, truth_imp, truth_pairMembershipFormula]
  rfl

def leastSupportEntryFormula {k} (z V Q omega depths supports : Fin k) : BoundedFormula k :=
  exMem Q (exMem V.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (leastSupportFormula V.succ.succ omega.succ.succ depths.succ.succ supports.succ.succ 1 0)))

theorem truth_leastSupportEntryFormula {k} (z V Q omega depths supports : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (leastSupportEntryFormula z V Q omega depths supports) env ↔
      ∃ x ∈ env Q, ∃ v ∈ env V, env z = ZFSet.pair x v ∧
        LeastSupportCode (env V) (env omega) (env depths) (env supports) x v := by
  simp only [leastSupportEntryFormula, truth_exMem, Truth, truth_orderedPairFormula, truth_leastSupportFormula]
  rfl
end BoundedFormula

namespace TransitiveGround
theorem leastSupportGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {V Q depths supports : ZFSet.{u}} (hV : V ∈ M.sets) (hQ : Q ∈ M.sets)
    (hDepths : depths ∈ M.sets) (hSupports : supports ∈ M.sets) :
    leastSupportGraph V Q depths supports ∈ M.sets := by
  have hOmega := M.omega_mem separation infinite
  let params := extend V (extend Q (extend ZFSet.omega (extend depths (extend supports Fin.elim0))))
  have selected := M.bounded_separation_mem separation (BoundedFormula.leastSupportEntryFormula 0 1 2 3 4 5)
    params (Fin.cases hV (Fin.cases hQ (Fin.cases hOmega (Fin.cases hDepths
      (Fin.cases hSupports (fun i => Fin.elim0 i)))))) (M.prod_mem pairing unions powers separation hQ hV)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.leastSupportEntryFormula 0 1 2 3 4 5)
      (extend z params)) (ZFSet.prod Q V) = leastSupportGraph V Q depths supports := by
    apply ZFSet.ext
    intro z
    rw [leastSupportGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_leastSupportEntryFormula _ _ _ _ _ _ _)
  exact equal ▸ selected
end TransitiveGround

variable {V X : Type u} (s : Presentation V) (q : Presentation X) (depth : V → Nat)
variable {depths supports : ZFSet.{u}} (supported : V → X → Prop)
variable (depthEntries : ∀ v n, ZFSet.pair (s.encode v) (natSetCode n) ∈ depths ↔ n = depth v)
variable (supportEntries : ∀ v x, ZFSet.pair (s.encode v) (q.encode x) ∈ supports ↔ supported v x)
include depthEntries supportEntries

theorem leastSupportCode_iff (x : X) (v : V) :
    LeastSupportCode s.carrier ZFSet.omega depths supports (q.encode x) (s.encode v) ↔
      supported v x ∧ ∀ w, supported w x → depth v ≤ depth w := by
  constructor
  · rintro ⟨support, n, hn, entry, least⟩
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    have equal := (depthEntries v n).1 entry
    subst n
    refine ⟨(supportEntries v x).1 support, ?_⟩
    intro w hw
    have noLower := least (s.encode w) (s.encode_mem w) (natSetCode (depth w))
      (natSetCode_mem_omega _) ((supportEntries w x).2 hw) ((depthEntries w _).2 rfl)
    exact Nat.le_of_not_lt (fun lower => noLower ((natSetCode_mem_iff _ _).2 lower))
  · rintro ⟨support, minimal⟩
    refine ⟨(supportEntries v x).2 support, natSetCode (depth v), natSetCode_mem_omega _,
      (depthEntries v _).2 rfl, ?_⟩
    intro w hw m hm member entry lower
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    obtain ⟨m, rfl⟩ := (mem_omega_iff_natSetCode m).1 hm
    have equal := (depthEntries w m).1 entry
    subst m
    exact Nat.not_lt_of_ge (minimal w ((supportEntries w x).1 member)) ((natSetCode_mem_iff _ _).1 lower)

theorem leastSupportGraph_entry (x : X) (v : V) :
    ZFSet.pair (q.encode x) (s.encode v) ∈ leastSupportGraph s.carrier q.carrier depths supports ↔
      supported v x ∧ ∀ w, supported w x → depth v ≤ depth w := by
  rw [pair_mem_leastSupportGraph, leastSupportCode_iff s q depth supported depthEntries supportEntries]
  exact ⟨fun h => h.2.2, fun h => ⟨q.encode_mem x, s.encode_mem v, h⟩⟩

theorem leastSupportGraph_function
    (unique : ∀ x, ∃! v, supported v x ∧ ∀ w, supported w x → depth v ≤ depth w) :
    ZFSet.IsFunc q.carrier s.carrier (leastSupportGraph s.carrier q.carrier depths supports) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x hx
  obtain ⟨x, rfl⟩ := (q.mem_carrier x).1 hx
  obtain ⟨v, good, only⟩ := unique x
  refine ⟨s.encode v, (leastSupportGraph_entry s q depth supported depthEntries supportEntries x v).2 good, ?_⟩
  intro w hw
  have member := (pair_mem_leastSupportGraph _ _ _ _ _ _).1 hw
  obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 member.2.1
  exact congrArg s.encode (only w ((leastSupportGraph_entry s q depth supported depthEntries supportEntries x w).1 hw))

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

def LeastSlotCode (supports v x j : ZFSet.{u}) : Prop :=
  ZFSet.pair (ZFSet.pair v j) x ∈ supports ∧
    ∀ k ∈ j, ZFSet.pair (ZFSet.pair v k) x ∉ supports

theorem LeastSlotCode.le {supports v x j k : ZFSet.{u}}
    (code : LeastSlotCode supports v x j) (hj : j ∈ natSetCode 3) (hk : k ∈ natSetCode 3)
    (supported : ZFSet.pair (ZFSet.pair v k) x ∈ supports) : j = k ∨ j ∈ k := by
  obtain ⟨n, _, rfl⟩ := (mem_natSetCode j 3).1 hj
  obtain ⟨m, _, rfl⟩ := (mem_natSetCode k 3).1 hk
  rcases Nat.lt_trichotomy n m with less | same | greater
  · exact Or.inr ((natSetCode_mem_iff _ _).2 less)
  · exact Or.inl (congrArg natSetCode same)
  · exact False.elim (code.2 _ ((natSetCode_mem_iff _ _).2 greater) supported)

theorem LeastSlotCode.unique {supports v x j k : ZFSet.{u}}
    (first : LeastSlotCode supports v x j) (second : LeastSlotCode supports v x k)
    (hj : j ∈ natSetCode 3) (hk : k ∈ natSetCode 3) : j = k := by
  rcases first.le hj hk second.1 with same | less
  · exact same
  · exact False.elim (second.2 _ less first.1)

theorem exists_leastSlotCode {supports v x : ZFSet.{u}}
    (cover : ∃ j ∈ natSetCode 3, ZFSet.pair (ZFSet.pair v j) x ∈ supports) :
    ∃ j ∈ natSetCode 3, LeastSlotCode supports v x j := by
  classical
  have candidates : ∃ n : Nat, n < 3 ∧ ZFSet.pair (ZFSet.pair v (natSetCode n)) x ∈ supports := by
    obtain ⟨j, hj, supported⟩ := cover
    obtain ⟨n, hn, rfl⟩ := (mem_natSetCode j 3).1 hj
    exact ⟨n, hn, supported⟩
  refine ⟨natSetCode (Nat.find candidates), (natSetCode_mem_iff _ _).2 (Nat.find_spec candidates).1,
    (Nat.find_spec candidates).2, ?_⟩
  intro k hk supported
  obtain ⟨k, lower, rfl⟩ := (mem_natSetCode k (Nat.find candidates)).1 hk
  exact Nat.find_min candidates lower ⟨Nat.lt_trans lower (Nat.find_spec candidates).1, supported⟩

noncomputable def leastSlotOwnerGraph (P B V owner supports : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ B, ∃ j ∈ natSetCode 3, ∃ v ∈ V,
    z = ZFSet.pair x j ∧ x ∉ P ∧ ZFSet.pair x v ∈ owner ∧ LeastSlotCode supports v x j)
    (ZFSet.prod B (natSetCode 3))

theorem pair_mem_leastSlotOwnerGraph (P B V owner supports x j : ZFSet.{u}) :
    ZFSet.pair x j ∈ leastSlotOwnerGraph P B V owner supports ↔
      x ∈ B ∧ j ∈ natSetCode 3 ∧ x ∉ P ∧ ∃ v ∈ V,
        ZFSet.pair x v ∈ owner ∧ LeastSlotCode supports v x j := by
  rw [leastSlotOwnerGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, x', hx, j', hj, v, hv, equal, fresh, owned, code⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx, hj, fresh, v, hv, owned, code⟩
  · rintro ⟨hx, hj, fresh, v, hv, owned, code⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hj⟩, x, hx, j, hj, v, hv, rfl, fresh, owned, code⟩

theorem pair_mem_leastSlotOwnerGraph_of_owner {P B V owner supports x j v : ZFSet.{u}}
    (function : ZFSet.IsFunc B V owner) (owned : ZFSet.pair x v ∈ owner) :
    ZFSet.pair x j ∈ leastSlotOwnerGraph P B V owner supports ↔
      j ∈ natSetCode 3 ∧ x ∉ P ∧ LeastSlotCode supports v x j := by
  have shape := ZFSet.pair_mem_prod.1 (function.1 owned)
  rw [pair_mem_leastSlotOwnerGraph]
  constructor
  · rintro ⟨_, hj, fresh, v', _, owned', code⟩
    have equal := (show FunctionGraphOn B owner from ⟨V, function⟩).unique owned' owned
    exact ⟨hj, fresh, equal ▸ code⟩
  · rintro ⟨hj, fresh, code⟩
    exact ⟨shape.1, hj, fresh, v, shape.2, owned, code⟩

theorem leastSlotOwnerGraph_partial {P B V owner supports : ZFSet.{u}}
    (function : ZFSet.IsFunc B V owner) :
    PartialFunctionCode B (natSetCode 3) (leastSlotOwnerGraph P B V owner supports) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x j k first second
  obtain ⟨_, hj, _, v, _, owned, code⟩ := (pair_mem_leastSlotOwnerGraph _ _ _ _ _ _ _).1 first
  have other := (pair_mem_leastSlotOwnerGraph_of_owner function owned).1 second
  exact code.unique other.2.2 hj other.1

theorem leastSlotOwnerGraph_function {P B V owner supports : ZFSet.{u}}
    (function : ZFSet.IsFunc B V owner)
    (cover : ∀ x ∈ B, x ∉ P → ∀ v, ZFSet.pair x v ∈ owner →
      ∃ j ∈ natSetCode 3, ZFSet.pair (ZFSet.pair v j) x ∈ supports) :
    ZFSet.IsFunc (ZFSet.sep (fun x => x ∉ P) B) (natSetCode 3)
      (leastSlotOwnerGraph P B V owner supports) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    have shape := (ZFSet.mem_sep.1 hz).1
    obtain ⟨x, hx, j, hj, rfl⟩ := ZFSet.mem_prod.1 shape
    have fresh := ((pair_mem_leastSlotOwnerGraph _ _ _ _ _ _ _).1 hz).2.2.1
    exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_sep.2 ⟨hx, fresh⟩, hj⟩
  · intro x hx
    obtain ⟨hx, fresh⟩ := ZFSet.mem_sep.1 hx
    obtain ⟨v, owned, _⟩ := function.2 x hx
    obtain ⟨j, hj, code⟩ := exists_leastSlotCode (cover x hx fresh v owned)
    refine ⟨j, (pair_mem_leastSlotOwnerGraph_of_owner function owned).2 ⟨hj, fresh, code⟩, ?_⟩
    intro k other
    exact (leastSlotOwnerGraph_partial function).unique x k j other
      ((pair_mem_leastSlotOwnerGraph_of_owner function owned).2 ⟨hj, fresh, code⟩)

theorem leastSlotOwnerGraph_monotone {P B V owner supports order x y j k : ZFSet.{u}}
    (first : ZFSet.pair x j ∈ leastSlotOwnerGraph P B V owner supports)
    (second : ZFSet.pair y k ∈ leastSlotOwnerGraph P B V owner supports)
    (sameOwner : ∀ v w, ZFSet.pair x v ∈ owner → ZFSet.pair y w ∈ owner → v = w)
    (ideals : ∀ v ∈ V, ∀ t ∈ natSetCode 3, ∀ a ∈ B, ∀ b ∈ B,
      ZFSet.pair a b ∈ order → ZFSet.pair (ZFSet.pair v t) b ∈ supports →
        ZFSet.pair (ZFSet.pair v t) a ∈ supports)
    (lower : ZFSet.pair x y ∈ order) : j = k ∨ j ∈ k := by
  obtain ⟨hx, hj, _, v, hv, owned, code⟩ := (pair_mem_leastSlotOwnerGraph _ _ _ _ _ _ _).1 first
  obtain ⟨hy, hk, _, w, _, owned', code'⟩ := (pair_mem_leastSlotOwnerGraph _ _ _ _ _ _ _).1 second
  have equal := sameOwner v w owned owned'
  subst w
  exact code.le hj hk (ideals v hv k hk x hx y hy lower code'.1)

end PartitionPilot.Forcing

end

end OAI
