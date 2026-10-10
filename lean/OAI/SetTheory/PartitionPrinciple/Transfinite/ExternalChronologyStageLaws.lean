import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundExternalBirthLayers

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def ownerLevelPrefix (P B levels n : ZFSet.{u}) : ZFSet.{u} :=
  P ∪ ZFSet.sep (fun x => x ∉ P ∧ ∃ k ∈ ZFSet.omega,
    ZFSet.pair x k ∈ levels ∧ (k = n ∨ k ∈ n)) B

theorem mem_ownerLevelPrefix (P B levels n x : ZFSet.{u}) :
    x ∈ ownerLevelPrefix P B levels n ↔ x ∈ P ∨
      x ∈ B ∧ x ∉ P ∧ ∃ k ∈ ZFSet.omega, ZFSet.pair x k ∈ levels ∧ (k = n ∨ k ∈ n) := by
  rw [ownerLevelPrefix, ZFSet.mem_union, ZFSet.mem_sep]

theorem ownerLevelPrefix_old (P B levels n : ZFSet.{u}) : P ⊆ ownerLevelPrefix P B levels n :=
  fun _ hx => (mem_ownerLevelPrefix _ _ _ _ _).2 (Or.inl hx)

theorem ownerLevelPrefix_subset {P B : ZFSet.{u}} (subset : P ⊆ B) (levels n : ZFSet.{u}) :
    ownerLevelPrefix P B levels n ⊆ B := by
  intro x hx
  exact ((mem_ownerLevelPrefix _ _ _ _ _).1 hx).elim (fun h => subset h) And.left

theorem mem_ownerLevelPrefix_fresh {P B levels n x : ZFSet.{u}} (fresh : x ∉ P) :
    x ∈ ownerLevelPrefix P B levels n ↔
      x ∈ B ∧ ∃ k ∈ ZFSet.omega, ZFSet.pair x k ∈ levels ∧ (k = n ∨ k ∈ n) := by
  rw [mem_ownerLevelPrefix]
  exact ⟨fun h => h.elim (fun old => False.elim (fresh old)) (fun h => ⟨h.1, h.2.2⟩),
    fun h => Or.inr ⟨h.1, fresh, h.2⟩⟩

theorem omegaMemberOrEqual_trans {k n m : ZFSet.{u}} (hk : k ∈ ZFSet.omega)
    (hn : n ∈ ZFSet.omega) (hm : m ∈ ZFSet.omega)
    (first : k = n ∨ k ∈ n) (second : n = m ∨ n ∈ m) : k = m ∨ k ∈ m := by
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode k).1 hk
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  obtain ⟨m, rfl⟩ := (mem_omega_iff_natSetCode m).1 hm
  have kn : k ≤ n := first.elim (fun h => Nat.le_of_eq (natSetCode_injective h))
    (fun h => Nat.le_of_lt ((natSetCode_mem_iff _ _).1 h))
  have nm : n ≤ m := second.elim (fun h => Nat.le_of_eq (natSetCode_injective h))
    (fun h => Nat.le_of_lt ((natSetCode_mem_iff _ _).1 h))
  rcases Nat.lt_or_eq_of_le (Nat.le_trans kn nm) with less | same
  · exact Or.inr ((natSetCode_mem_iff _ _).2 less)
  · exact Or.inl (congrArg natSetCode same)

theorem ownerLevelPrefix_mono {P B levels n m : ZFSet.{u}}
    (hn : n ∈ ZFSet.omega) (hm : m ∈ ZFSet.omega) (before : n = m ∨ n ∈ m) :
    ownerLevelPrefix P B levels n ⊆ ownerLevelPrefix P B levels m := by
  intro x hx
  rcases (mem_ownerLevelPrefix _ _ _ _ _).1 hx with old | ⟨hx, fresh, k, hk, entry, bound⟩
  · exact ownerLevelPrefix_old _ _ _ _ old
  · exact (mem_ownerLevelPrefix _ _ _ _ _).2 (Or.inr
      ⟨hx, fresh, k, hk, entry, omegaMemberOrEqual_trans hk hn hm bound before⟩)

theorem ownerLevelPrefix_union {P B levels : ZFSet.{u}} (subset : P ⊆ B)
    (function : ZFSet.IsFunc (ZFSet.sep (fun x => x ∉ P) B) ZFSet.omega levels) (x : ZFSet.{u}) :
    x ∈ B ↔ ∃ n : Nat, x ∈ ownerLevelPrefix P B levels (natSetCode n) := by
  classical
  constructor
  · intro hx
    by_cases old : x ∈ P
    · exact ⟨0, ownerLevelPrefix_old _ _ _ _ old⟩
    · obtain ⟨k, entry, _⟩ := function.2 x (ZFSet.mem_sep.2 ⟨hx, old⟩)
      have hk := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
      obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode k).1 hk
      exact ⟨n, (mem_ownerLevelPrefix _ _ _ _ _).2
        (Or.inr ⟨hx, old, natSetCode n, natSetCode_mem_omega n, entry, Or.inl rfl⟩)⟩
  · rintro ⟨n, hx⟩
    exact ownerLevelPrefix_subset subset levels (natSetCode n) hx

theorem ownerLevelPrefix_lower {P B levels order n : ZFSet.{u}}
    (hn : n ∈ ZFSet.omega)
    (oldLower : ∀ x ∈ B, ∀ y ∈ P, ZFSet.pair x y ∈ order → x ∈ P)
    (function : ZFSet.IsFunc (ZFSet.sep (fun x => x ∉ P) B) ZFSet.omega levels)
    (monotone : ∀ x ∈ B, x ∉ P → ∀ y ∈ B, y ∉ P → ∀ k l,
      ZFSet.pair x k ∈ levels → ZFSet.pair y l ∈ levels → ZFSet.pair x y ∈ order → k = l ∨ k ∈ l) :
    ∀ x ∈ B, ∀ y ∈ ownerLevelPrefix P B levels n,
      ZFSet.pair x y ∈ order → x ∈ ownerLevelPrefix P B levels n := by
  classical
  intro x hx y hy lower
  by_cases old : x ∈ P
  · exact ownerLevelPrefix_old _ _ _ _ old
  rcases (mem_ownerLevelPrefix _ _ _ _ _).1 hy with hy | ⟨hy, fresh, l, hl, atY, bound⟩
  · exact False.elim (old (oldLower x hx y hy lower))
  · obtain ⟨k, atX, _⟩ := function.2 x (ZFSet.mem_sep.2 ⟨hx, old⟩)
    have hk := (ZFSet.pair_mem_prod.1 (function.1 atX)).2
    exact (mem_ownerLevelPrefix _ _ _ _ _).2 (Or.inr ⟨hx, old, k, hk, atX,
      omegaMemberOrEqual_trans hk hl hn (monotone x hx old y hy fresh k l atX atY lower) bound⟩)





noncomputable def ownerLevelPrefixPoints (P B levels : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n ∈ ZFSet.omega, ∃ x ∈ B,
    z = ZFSet.pair n x ∧ x ∈ ownerLevelPrefix P B levels n) (ZFSet.prod ZFSet.omega B)

theorem pair_mem_ownerLevelPrefixPoints (P B levels n x : ZFSet.{u}) :
    ZFSet.pair n x ∈ ownerLevelPrefixPoints P B levels ↔
      n ∈ ZFSet.omega ∧ x ∈ B ∧ x ∈ ownerLevelPrefix P B levels n := by
  rw [ownerLevelPrefixPoints, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, n', hn, x', hx, equal, member⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hn, hx, member⟩
  · rintro ⟨hn, hx, member⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hn, hx⟩, n, hn, x, hx, rfl, member⟩

theorem ownerLevelPrefixPoints_fiber {P B levels n : ZFSet.{u}}
    (subset : P ⊆ B) (hn : n ∈ ZFSet.omega) :
    relationFiber B (ownerLevelPrefixPoints P B levels) n = ownerLevelPrefix P B levels n := by
  apply ZFSet.ext
  intro x
  rw [mem_relationFiber, pair_mem_ownerLevelPrefixPoints]
  exact ⟨fun h => h.2.2.2, fun hx =>
    ⟨ownerLevelPrefix_subset subset levels n hx, hn, ownerLevelPrefix_subset subset levels n hx, hx⟩⟩

namespace BoundedFormula

def ownerLevelPrefixFormula {n} (x P B levels cutoff omega : Fin n) : BoundedFormula n :=
  disj (.mem x P) (.conj (.mem x B) (.conj (.neg (.mem x P))
    (exMem omega (.conj (pairMembershipFormula x.succ 0 levels.succ)
      (disj (.equal 0 cutoff.succ) (.mem 0 cutoff.succ))))))

theorem truth_ownerLevelPrefixFormula {n} (x P B levels cutoff omega : Fin n)
    (env : Fin n → ZFSet.{u}) (omegaEq : env omega = ZFSet.omega) :
    Truth (ownerLevelPrefixFormula x P B levels cutoff omega) env ↔
      env x ∈ ownerLevelPrefix (env P) (env B) (env levels) (env cutoff) := by
  simp only [ownerLevelPrefixFormula, truth_disj, Truth, truth_exMem, truth_pairMembershipFormula]
  simp only [extend, Fin.cases_zero, Fin.cases_succ]
  rw [omegaEq, mem_ownerLevelPrefix]

def ownerLevelPrefixPointFormula {n} (z P B levels omega : Fin n) : BoundedFormula n :=
  exMem omega (exMem B.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (ownerLevelPrefixFormula 0 P.succ.succ B.succ.succ levels.succ.succ 1 omega.succ.succ)))

theorem truth_ownerLevelPrefixPointFormula {n} (z P B levels omega : Fin n)
    (env : Fin n → ZFSet.{u}) (omegaEq : env omega = ZFSet.omega) :
    Truth (ownerLevelPrefixPointFormula z P B levels omega) env ↔
      env z ∈ ownerLevelPrefixPoints (env P) (env B) (env levels) := by
  simp only [ownerLevelPrefixPointFormula, truth_exMem, Truth, truth_orderedPairFormula,
    ownerLevelPrefixFormula, truth_disj, truth_pairMembershipFormula]
  simp only [extend, Fin.cases_zero, Fin.cases_succ]
  rw [omegaEq, ownerLevelPrefixPoints, ZFSet.mem_sep]
  simp only [mem_ownerLevelPrefix]
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  obtain ⟨n, hn, x, hx, equal, _⟩ := h
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨hn, hx⟩
end BoundedFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def ownerLevelPrefixFamily (P B levels : ZFSet.{u}) : ZFSet.{u} :=
  M.relationFiberFamily ZFSet.omega B (ownerLevelPrefixPoints P B levels)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable {P B levels : ZFSet.{u}} (hP : P ∈ M.sets) (hB : B ∈ M.sets) (hLevels : levels ∈ M.sets)
include pairing unions powers separation infinite hP hB hLevels

theorem ownerLevelPrefixPoints_mem : ownerLevelPrefixPoints P B levels ∈ M.sets := by
  have hOmega := M.omega_mem separation infinite
  let params := extend P (extend B (extend levels (extend ZFSet.omega Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.ownerLevelPrefixPointFormula 0 1 2 3 4) params
    (Fin.cases hP (Fin.cases hB (Fin.cases hLevels (Fin.cases hOmega (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation hOmega hB)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.ownerLevelPrefixPointFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod ZFSet.omega B) = ownerLevelPrefixPoints P B levels := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_ownerLevelPrefixPointFormula _ _ _ _ _ _ rfl]
    exact ⟨And.right, fun h => ⟨(ZFSet.mem_sep.1 h).1, h⟩⟩
  exact equal ▸ selected

theorem ownerLevelPrefix_mem (subset : P ⊆ B) {n : ZFSet.{u}} (hn : n ∈ ZFSet.omega) :
    ownerLevelPrefix P B levels n ∈ M.sets := by
  rw [← ownerLevelPrefixPoints_fiber subset hn]
  exact M.relationFiber_mem separation hB (M.ownerLevelPrefixPoints_mem pairing unions powers separation infinite hP hB hLevels)
    (M.transitive (M.omega_mem separation infinite) hn)

theorem ownerLevelPrefixFamily_spec (subset : P ⊆ B) :
    M.ownerLevelPrefixFamily P B levels ∈ M.sets ∧
      FunctionGraphOn ZFSet.omega (M.ownerLevelPrefixFamily P B levels) ∧
      ∀ n S, ZFSet.pair n S ∈ M.ownerLevelPrefixFamily P B levels ↔
        n ∈ ZFSet.omega ∧ S = ownerLevelPrefix P B levels n := by
  have hOmega := M.omega_mem separation infinite
  have hPoints := M.ownerLevelPrefixPoints_mem pairing unions powers separation infinite hP hB hLevels
  refine ⟨M.relationFiberFamily_mem pairing unions powers separation hOmega hB hPoints,
    ⟨M.groundPower B, M.relationFiberFamily_function separation hOmega hB hPoints⟩, ?_⟩
  intro n S
  change ZFSet.pair n S ∈ M.relationFiberFamily _ _ _ ↔ _
  rw [M.relationFiberFamily_entries separation hOmega hB hPoints]
  exact ⟨fun h => ⟨h.1, h.2.trans (ownerLevelPrefixPoints_fiber subset h.1)⟩,
    fun h => ⟨h.1, h.2.trans (ownerLevelPrefixPoints_fiber subset h.1).symm⟩⟩

end TransitiveGround





theorem PartialOrderCode.heightOrderRestriction {B Q r : ZFSet.{u}}
    (order : PartialOrderCode B r) (subset : Q ⊆ B) :
    PartialOrderCode Q (heightOrderRestriction Q r) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).2, ?_, ?_, ?_⟩
  · intro x hx
    exact (pair_mem_heightOrderRestriction _ _ _ _).2 ⟨order.refl x (subset hx), hx, hx⟩
  · intro x hx y hy xy yx
    exact order.antisymm x (subset hx) y (subset hy) (ZFSet.mem_sep.1 xy).1 (ZFSet.mem_sep.1 yx).1
  · intro x hx y hy z hz xy yz
    exact (pair_mem_heightOrderRestriction _ _ _ _).2
      ⟨order.trans x (subset hx) y (subset hy) z (subset hz) (ZFSet.mem_sep.1 xy).1 (ZFSet.mem_sep.1 yz).1, hx, hz⟩

theorem MeetOrderCode.restrict_lower {B Q r μ : ZFSet.{u}}
    (meet : MeetOrderCode B r μ) (subset : Q ⊆ B)
    (lower : ∀ x ∈ B, ∀ y ∈ Q, ZFSet.pair x y ∈ r → x ∈ Q) :
    MeetOrderCode Q (heightOrderRestriction Q r) (graphRestriction (ZFSet.prod Q Q) μ) := by
  have productSubset : ZFSet.prod Q Q ⊆ ZFSet.prod B B := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
    exact ZFSet.pair_mem_prod.2 ⟨subset hx, subset hy⟩
  have function := (show FunctionGraphOn (ZFSet.prod B B) μ from ⟨B, meet.operation⟩).restrict productSubset
  have result : ∀ x y z, ZFSet.pair (ZFSet.pair x y) z ∈ graphRestriction (ZFSet.prod Q Q) μ → z ∈ Q := by
    intro x y z entry
    obtain ⟨entry, domain⟩ := pair_mem_graphRestriction.1 entry
    exact lower z (ZFSet.pair_mem_prod.1 (meet.operation.1 entry)).2
      x (ZFSet.pair_mem_prod.1 domain).1 (meet.lower_left x y z entry)
  refine ⟨meet.order.heightOrderRestriction subset, ⟨?_, function.to_isFunc.2⟩, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨a, ha, w, rfl, _⟩ := mem_graphRestriction.1 hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 ha
    exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, result x y w hz⟩
  · intro x y z entry
    have domain := ZFSet.pair_mem_prod.1 (pair_mem_graphRestriction.1 entry).2
    exact (pair_mem_heightOrderRestriction _ _ _ _).2
      ⟨meet.lower_left x y z (pair_mem_graphRestriction.1 entry).1, result x y z entry, domain.1⟩
  · intro x y z entry
    have domain := ZFSet.pair_mem_prod.1 (pair_mem_graphRestriction.1 entry).2
    exact (pair_mem_heightOrderRestriction _ _ _ _).2
      ⟨meet.lower_right x y z (pair_mem_graphRestriction.1 entry).1, result x y z entry, domain.2⟩
  · intro x y z w hw entry left right
    exact (pair_mem_heightOrderRestriction _ _ _ _).2
      ⟨meet.greatest x y z w (subset hw) (pair_mem_graphRestriction.1 entry).1
        (ZFSet.mem_sep.1 left).1 (ZFSet.mem_sep.1 right).1, hw, result x y z entry⟩

theorem StrictLexHeightCode.restrict_order {B Q C D r height rD : ZFSet.{u}}
    (code : StrictLexHeightCode B C D r height rD) (subset : Q ⊆ B) :
    StrictLexHeightCode Q C D (heightOrderRestriction Q r) (graphRestriction Q height) rD := by
  have function := (show FunctionGraphOn B height from ⟨ZFSet.prod C D, code.function⟩).restrict subset
  refine ⟨⟨?_, function.to_isFunc.2⟩, ?_⟩
  · intro z hz
    obtain ⟨x, hx, y, rfl, entry⟩ := mem_graphRestriction.1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hx, (ZFSet.pair_mem_prod.1 (code.function.1 entry)).2⟩
  · intro x hx y hy c q d v lower distinct first second
    exact code.strict x (subset hx) y (subset hy) c q d v (ZFSet.mem_sep.1 lower).1 distinct
      (pair_mem_graphRestriction.1 first).1 (pair_mem_graphRestriction.1 second).1

theorem ownerLevelPrefix_codes {P B levels r μ C D height rD n : ZFSet.{u}}
    (subset : P ⊆ B) (hn : n ∈ ZFSet.omega)
    (oldLower : ∀ x ∈ B, ∀ y ∈ P, ZFSet.pair x y ∈ r → x ∈ P)
    (function : ZFSet.IsFunc (ZFSet.sep (fun x => x ∉ P) B) ZFSet.omega levels)
    (monotone : ∀ x ∈ B, x ∉ P → ∀ y ∈ B, y ∉ P → ∀ k l,
      ZFSet.pair x k ∈ levels → ZFSet.pair y l ∈ levels → ZFSet.pair x y ∈ r → k = l ∨ k ∈ l)
    (meet : MeetOrderCode B r μ) (code : StrictLexHeightCode B C D r height rD) :
    let Q := ownerLevelPrefix P B levels n
    MeetOrderCode Q (heightOrderRestriction Q r) (graphRestriction (ZFSet.prod Q Q) μ) ∧
      StrictLexHeightCode Q C D (heightOrderRestriction Q r) (graphRestriction Q height) rD := by
  exact ⟨meet.restrict_lower (ownerLevelPrefix_subset subset levels n)
      (ownerLevelPrefix_lower hn oldLower function monotone),
    code.restrict_order (ownerLevelPrefix_subset subset levels n)⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem heightOrderRestriction_mem {Q r : ZFSet.{u}} (hQ : Q ∈ M.sets) (hr : r ∈ M.sets) :
    heightOrderRestriction Q r ∈ M.sets := by
  have hProduct := M.prod_mem pairing unions powers separation hQ hQ
  exact M.bounded_separation_mem separation (.mem 0 1) (extend (ZFSet.prod Q Q) Fin.elim0)
    (Fin.cases hProduct (fun i => Fin.elim0 i)) hr

theorem ownerLevelPrefix_fields_mem
    (infinite : Realize M.sets infinity Fin.elim0)
    {P B levels r μ height n : ZFSet.{u}}
    (hP : P ∈ M.sets) (hB : B ∈ M.sets) (hLevels : levels ∈ M.sets)
    (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hHeight : height ∈ M.sets)
    (subset : P ⊆ B) (hn : n ∈ ZFSet.omega) :
    let Q := ownerLevelPrefix P B levels n
    Q ∈ M.sets ∧ heightOrderRestriction Q r ∈ M.sets ∧
      graphRestriction (ZFSet.prod Q Q) μ ∈ M.sets ∧ graphRestriction Q height ∈ M.sets := by
  have hQ := M.ownerLevelPrefix_mem pairing unions powers separation infinite hP hB hLevels subset hn
  exact ⟨hQ, M.heightOrderRestriction_mem pairing unions powers separation hQ hr,
    M.graphRestriction_mem unions separation (M.prod_mem pairing unions powers separation hQ hQ) hμ,
    M.graphRestriction_mem unions separation hQ hHeight⟩

end TransitiveGround





noncomputable def chronologyRestriction (kind : Fin 3) (P f : ZFSet.{u}) : ZFSet.{u} :=
  Fin.cases (graphRestriction P f) (Fin.cases (heightOrderRestriction P f)
    (fun _ => graphRestriction (ZFSet.prod P P) f)) kind

namespace BoundedFormula

def chronologyRestrictionMemberFormula (kind : Fin 3) {n} (z P R : Fin n) : BoundedFormula n :=
  Fin.cases (productElementFormula z P R) (Fin.cases (productElementFormula z P P)
    (fun _ => exMem R (exMem R.succ (.conj (orderedPairFormula z.succ.succ 1 0)
      (productElementFormula 1 P.succ.succ P.succ.succ))))) kind

theorem truth_chronologyRestrictionMemberFormula (kind : Fin 3) {n}
    (z P R : Fin n) (env : Fin n → ZFSet.{u}) {f : ZFSet.{u}}
    (bound : env R = ZFSet.sUnion (ZFSet.sUnion f)) (member : env z ∈ f) :
    Truth (chronologyRestrictionMemberFormula kind z P R) env ↔
      env z ∈ chronologyRestriction kind (env P) f := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) kind
  · simp only [chronologyRestrictionMemberFormula, chronologyRestriction, Fin.cases_zero,
      truth_productElementFormula, graphRestriction, ZFSet.mem_sep, member, true_and, bound]
  · simp only [chronologyRestrictionMemberFormula, chronologyRestriction, Fin.cases_succ,
      Fin.cases_zero, truth_productElementFormula, heightOrderRestriction, ZFSet.mem_sep, member, true_and]
  · simp only [chronologyRestrictionMemberFormula, chronologyRestriction, Fin.cases_succ,
      truth_exMem, Truth, truth_orderedPairFormula, truth_productElementFormula]
    change (∃ a ∈ env R, ∃ b ∈ env R, env z = ZFSet.pair a b ∧ a ∈ ZFSet.prod (env P) (env P)) ↔ _
    constructor
    · rintro ⟨a, _, b, _, equal, ha⟩
      rw [equal] at member ⊢
      exact pair_mem_graphRestriction.2 ⟨member, ha⟩
    · intro entry
      obtain ⟨a, ha, b, equal, pair⟩ := mem_graphRestriction.1 entry
      exact ⟨a, bound.symm ▸ pair_first_mem_doubleUnion pair,
        b, bound.symm ▸ pair_second_mem_doubleUnion pair, equal, ha⟩

def chronologyRestrictionFormula (kind : Fin 3) {n} (q P R f : Fin n) : BoundedFormula n :=
  .conj (.allMem q (.conj (.mem 0 f.succ) (chronologyRestrictionMemberFormula kind 0 P.succ R.succ)))
    (.allMem f (imp (chronologyRestrictionMemberFormula kind 0 P.succ R.succ) (.mem 0 q.succ)))

theorem truth_chronologyRestrictionFormula (kind : Fin 3) {n}
    (q P R f : Fin n) (env : Fin n → ZFSet.{u}) (bound : env R = ZFSet.sUnion (ZFSet.sUnion (env f))) :
    Truth (chronologyRestrictionFormula kind q P R f) env ↔
      env q = chronologyRestriction kind (env P) (env f) := by
  have subset : chronologyRestriction kind (env P) (env f) ⊆ env f := by
    exact Fin.cases (graphRestriction_subset _ _)
      (Fin.cases (fun _ hz => (ZFSet.mem_sep.1 hz).1)
        (fun _ => graphRestriction_subset _ _)) kind
  simp only [chronologyRestrictionFormula, Truth, truth_imp]
  constructor
  · rintro ⟨forward, backward⟩
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      exact (truth_chronologyRestrictionMemberFormula kind 0 P.succ R.succ (extend z env)
        bound (forward z hz).1).1 (forward z hz).2
    · intro hz
      exact backward z (subset hz) ((truth_chronologyRestrictionMemberFormula kind 0 P.succ R.succ
        (extend z env) bound (subset hz)).2 hz)
  · intro equal
    change (∀ z ∈ env q, z ∈ env f ∧ _) ∧ (∀ z ∈ env f, _ → z ∈ env q)
    rw [equal]
    exact ⟨fun z hz => ⟨subset hz, (truth_chronologyRestrictionMemberFormula kind 0 P.succ R.succ
      (extend z env) bound (subset hz)).2 hz⟩,
      fun z hz recognized => (truth_chronologyRestrictionMemberFormula kind 0 P.succ R.succ
        (extend z env) bound hz).1 recognized⟩

def chronologyRestrictionFamilyFormula (kind : Fin 3) {n}
    (z I Ps Q R W f : Fin n) : BoundedFormula n :=
  exMem I (exMem Q.succ (exMem W.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 2 0)
      (.conj (pairMembershipFormula 2 1 Ps.succ.succ.succ)
        (chronologyRestrictionFormula kind 0 1 R.succ.succ.succ f.succ.succ.succ)))))

theorem truth_chronologyRestrictionFamilyFormula (kind : Fin 3) {n}
    (z I Ps Q R W f : Fin n) (env : Fin n → ZFSet.{u}) (bound : env R = ZFSet.sUnion (ZFSet.sUnion (env f))) :
    Truth (chronologyRestrictionFamilyFormula kind z I Ps Q R W f) env ↔
      ∃ i ∈ env I, ∃ P ∈ env Q, ∃ q ∈ env W, env z = ZFSet.pair i q ∧
        ZFSet.pair i P ∈ env Ps ∧ q = chronologyRestriction kind P (env f) := by
  have meaning (i P q : ZFSet.{u}) :=
    truth_chronologyRestrictionFormula kind 0 1 R.succ.succ.succ f.succ.succ.succ
      (extend q (extend P (extend i env))) bound
  simp only [chronologyRestrictionFamilyFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula, meaning]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def chronologyRestrictionFamily (kind : Fin 3) (I Ps f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ P ∈ ZFSet.sUnion (ZFSet.sUnion Ps), ∃ q ∈ M.groundPower f,
    z = ZFSet.pair i q ∧ ZFSet.pair i P ∈ Ps ∧ q = chronologyRestriction kind P f)
    (ZFSet.prod I (M.groundPower f))

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem chronologyRestriction_mem (kind : Fin 3) {P f : ZFSet.{u}}
    (hP : P ∈ M.sets) (hf : f ∈ M.sets) : chronologyRestriction kind P f ∈ M.sets := by
  exact Fin.cases (M.graphRestriction_mem unions separation hP hf)
    (Fin.cases (M.heightOrderRestriction_mem pairing unions powers separation hP hf)
      (fun _ => M.graphRestriction_mem unions separation
        (M.prod_mem pairing unions powers separation hP hP) hf)) kind

theorem chronologyRestrictionFamily_mem (kind : Fin 3) {I Ps f : ZFSet.{u}}
    (hI : I ∈ M.sets) (hPs : Ps ∈ M.sets) (hf : f ∈ M.sets) :
    M.chronologyRestrictionFamily kind I Ps f ∈ M.sets := by
  have hW := M.groundPower_mem powers hf
  let params := extend I (extend Ps (extend (ZFSet.sUnion (ZFSet.sUnion Ps)) (extend (ZFSet.sUnion (ZFSet.sUnion f))
    (extend (M.groundPower f) (extend f Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.chronologyRestrictionFamilyFormula kind 0 1 2 3 4 5 6) params
    (Fin.cases hI (Fin.cases hPs (Fin.cases (M.union_mem unions (M.union_mem unions hPs))
      (Fin.cases (M.union_mem unions (M.union_mem unions hf)) (Fin.cases hW
        (Fin.cases hf (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hI hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.chronologyRestrictionFamilyFormula kind 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod I (M.groundPower f)) = M.chronologyRestrictionFamily kind I Ps f := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, chronologyRestrictionFamily, ZFSet.mem_sep,
      BoundedFormula.truth_chronologyRestrictionFamilyFormula kind _ _ _ _ _ _ _ _ rfl]
    rfl
  exact equal ▸ selected

theorem chronologyRestrictionFamily_entries (kind : Fin 3) {I Ps f : ZFSet.{u}}
    (hPs : Ps ∈ M.sets) (hf : f ∈ M.sets) (function : FunctionGraphOn I Ps)
    {i P : ZFSet.{u}} (entry : ZFSet.pair i P ∈ Ps) (q : ZFSet.{u}) :
    ZFSet.pair i q ∈ M.chronologyRestrictionFamily kind I Ps f ↔
      q = chronologyRestriction kind P f := by
  constructor
  · intro member
    obtain ⟨_, j, _, Q, _, w, _, equal, input, output⟩ := ZFSet.mem_sep.1 member
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.1 equal
    exact function.unique input entry ▸ output
  · intro equal
    have hP := M.pair_right (M.transitive hPs entry)
    have subset : chronologyRestriction kind P f ⊆ f := by
      exact Fin.cases (graphRestriction_subset _ _)
        (Fin.cases (fun _ hz => (ZFSet.mem_sep.1 hz).1)
          (fun _ => graphRestriction_subset _ _)) kind
    have bound := (M.mem_groundPower f q).2 ⟨equal.symm ▸
      M.chronologyRestriction_mem pairing unions powers separation kind hP hf,
      fun z hz => subset (equal ▸ hz)⟩
    have hi := (ZFSet.pair_mem_prod.1 (function.to_isFunc.1 entry)).1
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hi,bound⟩, i,hi,P,
      pair_second_mem_doubleUnion entry,q,bound,rfl,entry,equal⟩

theorem chronologyRestrictionFamily_function (kind : Fin 3) {I Ps f : ZFSet.{u}}
    (hPs : Ps ∈ M.sets) (hf : f ∈ M.sets) (function : FunctionGraphOn I Ps) :
    ZFSet.IsFunc I (M.groundPower f) (M.chronologyRestrictionFamily kind I Ps f) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro i hi
  obtain ⟨P, entry, _⟩ := function.to_isFunc.2 i hi
  have exactEntries := M.chronologyRestrictionFamily_entries pairing unions powers separation kind hPs hf function entry
  exact ⟨chronologyRestriction kind P f, (exactEntries _).2 rfl, fun q hq => (exactEntries q).1 hq⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "r" => completion.externalPointOrder P0 r0 μ0 A0
local notation "μ" => completion.externalPointMeet P0 r0 μ0 A0
local notation "levels" => completion.externalOwnerLevels P0 r0 μ0 A0

noncomputable def cutoff (_births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion) (n : Nat) : ZFSet.{u} :=
  ownerLevelPrefix P B levels (natSetCode n)

noncomputable def cutoffFamily (_births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion) : ZFSet.{u} :=
  M.ownerLevelPrefixFamily P B levels

variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion)
noncomputable def cutoffOrder (n : Nat) : ZFSet.{u} := heightOrderRestriction (births.cutoff n) r
noncomputable def cutoffMeet (n : Nat) : ZFSet.{u} := graphRestriction (ZFSet.prod (births.cutoff n) (births.cutoff n)) μ
noncomputable def cutoffBirth (n : Nat) : ZFSet.{u} := graphRestriction (births.cutoff n) births.birth
noncomputable def cutoffHeight (height : ZFSet.{u}) (n : Nat) : ZFSet.{u} := graphRestriction (births.cutoff n) height

theorem cutoff_old (n : Nat) : P ⊆ births.cutoff n := ownerLevelPrefix_old _ _ _ _

theorem cutoff_subset (n : Nat) : births.cutoff n ⊆ B :=
  ownerLevelPrefix_subset (fun _ hx => (mem_relationImage _ _ _ _).1 hx |>.1) levels (natSetCode n)

theorem cutoff_mono {n k : Nat} (before : n ≤ k) : births.cutoff n ⊆ births.cutoff k := by
  apply ownerLevelPrefix_mono (natSetCode_mem_omega n) (natSetCode_mem_omega k)
  rcases Nat.lt_or_eq_of_le before with less | same
  · exact Or.inr ((natSetCode_mem_iff _ _).2 less)
  · exact Or.inl (congrArg natSetCode same)

theorem cutoff_union
    (levelFunction : ZFSet.IsFunc (ownerFresh P B) ZFSet.omega levels) (x : ZFSet.{u}) :
    x ∈ B ↔ ∃ n : Nat, x ∈ births.cutoff n :=
  ownerLevelPrefix_union (fun _ hx => (mem_relationImage _ _ _ _).1 hx |>.1) levelFunction x

theorem cutoff_birth_function (n : Nat) :
    ZFSet.IsFunc (births.cutoff n) births.limit (births.cutoffBirth n) := by
  have restricted := (show FunctionGraphOn B births.birth from ⟨births.limit, births.function⟩).restrict (births.cutoff_subset n)
  apply isFunc_retarget_of_entries restricted.to_isFunc
  intro x t entry
  exact (ZFSet.pair_mem_prod.1 (births.function.1 (pair_mem_graphRestriction.1 entry).1)).2

theorem cutoff_old_meet (n : Nat) : OldMeetCode (births.cutoffOrder n) (births.cutoffMeet n) (births.cutoffBirth n) := by
  intro x y z a b c ya xb before notLower xy zc
  have hx := (pair_mem_graphRestriction.1 xb).2
  have hy := (pair_mem_graphRestriction.1 ya).2
  exact births.old_meet x y z a b c (pair_mem_graphRestriction.1 ya).1 (pair_mem_graphRestriction.1 xb).1 before
    (fun lower => notLower ((pair_mem_heightOrderRestriction _ _ _ _).2 ⟨lower, hx, hy⟩))
    (pair_mem_graphRestriction.1 xy).1 (pair_mem_graphRestriction.1 zc).1

theorem cutoff_birth_bound
    (levelFunction : ZFSet.IsFunc (ownerFresh P B) ZFSet.omega levels)
    (n : Nat) {x t : ZFSet.{u}} (entry : ZFSet.pair x t ∈ births.cutoffBirth n) :
    t ∈ compressionStamp oldTimes n ∨ t = compressionStamp oldTimes n := by
  classical
  obtain ⟨entry, hx⟩ := pair_mem_graphRestriction.1 entry
  by_cases old : x ∈ P
  · exact Or.inl (births.old_before ((ownerBirthGraph_old_iff old).1 entry) n)
  · obtain ⟨_, k, hk, level, bound⟩ := (mem_ownerLevelPrefix_fresh old).1 hx
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode k).1 hk
    obtain ⟨_, _, j, actualLevel, stamp⟩ := (ownerBirthGraph_fresh_nat_iff births.seed_function old).1 entry
    have equal : j = k := natSetCode_injective
      ((show FunctionGraphOn (ownerFresh P B) levels from ⟨ZFSet.omega, levelFunction⟩).unique actualLevel level)
    subst j
    rw [(births.times.entries k t).1 stamp]
    rcases bound with same | before
    · exact Or.inr (congrArg (compressionStamp oldTimes) (natSetCode_injective same))
    · exact Or.inl ((compressionStamp_mem_iff oldTimes k n).2 ((natSetCode_mem_iff _ _).1 before))

variable {inv : ZFSet.{u}}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
include data group action pairing unions powers separation infinite hG hP0

theorem cutoffFamily_spec : births.cutoffFamily ∈ M.sets ∧ FunctionGraphOn ZFSet.omega births.cutoffFamily ∧
    ∀ n : Nat, ∀ Q, ZFSet.pair (natSetCode n) Q ∈ births.cutoffFamily ↔ Q = births.cutoff n := by
  have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP0
  have hSeed := data.externalSeedCarrier_ground group action pairing unions powers separation infinite hG hP0
  have hLevels := (data.externalOwnerLevels_ground_function group action pairing unions powers separation infinite hG hP0).1
  have spec := M.ownerLevelPrefixFamily_spec pairing unions powers separation infinite hSeed geometry.carrier_ground hLevels
    (fun _ hx => (mem_relationImage _ _ _ _).1 hx |>.1)
  exact ⟨spec.1, spec.2.1, fun n Q => (spec.2.2 (natSetCode n) Q).trans (and_iff_right (natSetCode_mem_omega n))⟩

theorem cutoff_lower (n : Nat) :
    ∀ x ∈ B, ∀ y ∈ births.cutoff n, ZFSet.pair x y ∈ r → x ∈ births.cutoff n := by
  have levelFunction := (data.externalOwnerLevels_ground_function group action pairing unions powers separation infinite hG hP0).2
  apply ownerLevelPrefix_lower (natSetCode_mem_omega n)
    (fun _ hx _ hy lower => data.externalSeedCarrier_lower group action pairing unions powers separation infinite hG hx hy lower) levelFunction
  intro x _ _ y _ _ k l first second lower
  have hk := (ZFSet.pair_mem_prod.1 (levelFunction.1 first)).2
  have hl := (ZFSet.pair_mem_prod.1 (levelFunction.1 second)).2
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode k).1 hk
  obtain ⟨l, rfl⟩ := (mem_omega_iff_natSetCode l).1 hl
  have before := data.externalOwnerLevels_monotone group action pairing unions powers separation infinite hG hP0 lower first second
  rcases Nat.lt_or_eq_of_le before with less | same
  · exact Or.inr ((natSetCode_mem_iff _ _).2 less)
  · exact Or.inl (congrArg natSetCode same)

theorem cutoff_fields {C D rD lo hi seed : ZFSet.{u}}
    (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 C D rD lo hi seed completion)
    (n : Nat) :
    births.cutoff n ∈ M.sets ∧ births.cutoffOrder n ∈ M.sets ∧ births.cutoffMeet n ∈ M.sets ∧
      births.cutoffBirth n ∈ M.sets ∧ births.cutoffHeight heights.height n ∈ M.sets ∧
      MeetOrderCode (births.cutoff n) (births.cutoffOrder n) (births.cutoffMeet n) ∧
      ZFSet.IsFunc (births.cutoff n) births.limit (births.cutoffBirth n) ∧
      OldMeetCode (births.cutoffOrder n) (births.cutoffMeet n) (births.cutoffBirth n) ∧
      StrictLexHeightCode (births.cutoff n) C D (births.cutoffOrder n) (births.cutoffHeight heights.height n) rD ∧
      ∀ x t, ZFSet.pair x t ∈ births.cutoffBirth n → t ∈ compressionStamp oldTimes n ∨ t = compressionStamp oldTimes n := by
  have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP0
  have levelCode := data.externalOwnerLevels_ground_function group action pairing unions powers separation infinite hG hP0
  have hSeed := data.externalSeedCarrier_ground group action pairing unions powers separation infinite hG hP0
  have hQ := M.ownerLevelPrefix_mem pairing unions powers separation infinite hSeed geometry.carrier_ground levelCode.1
    (fun _ hx => (mem_relationImage _ _ _ _).1 hx |>.1) (natSetCode_mem_omega n)
  refine ⟨hQ, M.heightOrderRestriction_mem pairing unions powers separation hQ geometry.order_ground,
    M.graphRestriction_mem unions separation (M.prod_mem pairing unions powers separation hQ hQ) geometry.meet_ground,
    M.graphRestriction_mem unions separation hQ births.birth_ground,
    M.graphRestriction_mem unions separation hQ heights.height_ground,
    geometry.meet.restrict_lower (births.cutoff_subset n)
      (births.cutoff_lower data group action pairing unions powers separation infinite hG hP0 n),
    births.cutoff_birth_function n, births.cutoff_old_meet n,
    heights.code.restrict_order (births.cutoff_subset n), ?_⟩
  intro x t entry
  exact births.cutoff_birth_bound levelCode.2 n entry

end PartitionPilot.Forcing.GroundExternalBirthData



namespace PartitionPilot.Forcing.GroundExternalBirthData
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "levels" => completion.externalOwnerLevels P0 r0 μ0 A0

theorem cutoff_iff_birth_le_stamp (n : Nat) {x a : ZFSet.{u}}
    (entry : ZFSet.pair x a ∈ births.birth) :
    x ∈ births.cutoff n ↔ a ∈ compressionStamp oldTimes n ∨ a = compressionStamp oldTimes n := by
  have function : FunctionGraphOn B births.birth := ⟨births.limit, births.function⟩
  constructor
  · intro member
    rcases (mem_ownerLevelPrefix _ _ _ _ _).1 member with old | ⟨hx, fresh, k, hk, level, bound⟩
    · exact Or.inl (births.old_before ((ownerBirthGraph_old_iff old).1 entry) n)
    · obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode k).1 hk
      have atStamp := (births.stamp_fiber k x).2 ⟨(mem_ownerFresh P B x).2 ⟨hx, fresh⟩, level⟩
      rw [function.unique entry atStamp]
      rcases bound with same | before
      · exact Or.inr (congrArg (compressionStamp oldTimes) (natSetCode_injective same))
      · exact Or.inl ((compressionStamp_mem_iff oldTimes k n).2 ((natSetCode_mem_iff k n).1 before))
  · intro bound
    by_cases old : x ∈ P
    · exact births.cutoff_old n old
    · obtain ⟨hx, _, k, level, stamp⟩ := (ownerBirthGraph_fresh_nat_iff births.seed_function old).1 entry
      have actual := (births.times.entries k a).1 stamp
      refine (mem_ownerLevelPrefix _ _ _ _ _).2 (Or.inr ⟨hx, old, natSetCode k,
        natSetCode_mem_omega k, level, ?_⟩)
      rcases bound with before | same
      · exact Or.inr ((natSetCode_mem_iff k n).2 ((compressionStamp_mem_iff oldTimes k n).1 (actual ▸ before)))
      · have atN : ZFSet.pair (natSetCode n) a ∈ births.stamps := (births.times.entries n a).2 same
        exact Or.inl (congrArg natSetCode (births.times.ownerStampCode.injective stamp atN))

theorem point_in_birth_cutoff {n : Nat} {x : ZFSet.{u}}
    (entry : ZFSet.pair x (compressionStamp oldTimes n) ∈ births.birth) : x ∈ births.cutoff n :=
  (births.cutoff_iff_birth_le_stamp n entry).2 (Or.inr rfl)

theorem fresh_birth_cutoff_iff {n : Nat} {x : ZFSet.{u}}
    (entry : ZFSet.pair x (compressionStamp oldTimes n) ∈ births.birth) (k : Nat) :
    x ∈ births.cutoff k ↔ n ≤ k := by
  rw [births.cutoff_iff_birth_le_stamp k entry]
  constructor
  · rintro (before | same)
    · exact Nat.le_of_lt ((compressionStamp_mem_iff oldTimes n k).1 before)
    · have first := (births.times.entries n _).2 rfl
      have second := (births.times.entries k _).2 same
      exact Nat.le_of_eq (births.times.ownerStampCode.injective first second)
  · intro before
    rcases Nat.lt_or_eq_of_le before with before | same
    · exact Or.inl ((compressionStamp_mem_iff oldTimes n k).2 before)
    · exact Or.inr (congrArg (compressionStamp oldTimes) same)

end PartitionPilot.Forcing.GroundExternalBirthData



namespace PartitionPilot.Forcing.GroundExternalBirthData
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (prior : GroundChronologicalHistory M T0 C D rD)

noncomputable def chronologyFields : CompressionChronologyFields.{u} where
  space := compressionPrefixValue oldTimes births.limit prior.space births.cutoff
    (completion.externalPointCarrier P0 r0 μ0 A0)
  order := compressionPrefixValue oldTimes births.limit prior.order births.cutoffOrder
    (completion.externalPointOrder P0 r0 μ0 A0)
  meetGraph := compressionPrefixValue oldTimes births.limit prior.meetGraph births.cutoffMeet
    (completion.externalPointMeet P0 r0 μ0 A0)
  birth := compressionPrefixValue oldTimes births.limit prior.birth births.cutoffBirth births.birth
  height := compressionPrefixValue oldTimes births.limit prior.height (births.cutoffHeight heights.height) heights.height

theorem chronologyFields_old {s : ZFSet.{u}} (before : s ∈ oldTimes ∨ s = oldTimes) :
    (births.chronologyFields heights prior).space s = prior.space s ∧
    (births.chronologyFields heights prior).order s = prior.order s ∧
    (births.chronologyFields heights prior).meetGraph s = prior.meetGraph s ∧
    (births.chronologyFields heights prior).birth s = prior.birth s ∧
    (births.chronologyFields heights prior).height s = prior.height s := by
  dsimp only [chronologyFields]
  exact ⟨compressionPrefixValue_old _ _ _ before, compressionPrefixValue_old _ _ _ before,
    compressionPrefixValue_old _ _ _ before, compressionPrefixValue_old _ _ _ before,
    compressionPrefixValue_old _ _ _ before⟩

theorem chronologyFields_stamp (n : Nat) :
    (births.chronologyFields heights prior).space (compressionStamp oldTimes n) = births.cutoff n ∧
    (births.chronologyFields heights prior).order (compressionStamp oldTimes n) = births.cutoffOrder n ∧
    (births.chronologyFields heights prior).meetGraph (compressionStamp oldTimes n) = births.cutoffMeet n ∧
    (births.chronologyFields heights prior).birth (compressionStamp oldTimes n) = births.cutoffBirth n ∧
    (births.chronologyFields heights prior).height (compressionStamp oldTimes n) = births.cutoffHeight heights.height n := by
  dsimp only [chronologyFields]
  exact ⟨compressionPrefixValue_stamp _ _ _ births.times n, compressionPrefixValue_stamp _ _ _ births.times n,
    compressionPrefixValue_stamp _ _ _ births.times n, compressionPrefixValue_stamp _ _ _ births.times n,
    compressionPrefixValue_stamp _ _ _ births.times n⟩

theorem chronologyFields_limit :
    (births.chronologyFields heights prior).space births.limit = completion.externalPointCarrier P0 r0 μ0 A0 ∧
    (births.chronologyFields heights prior).order births.limit = completion.externalPointOrder P0 r0 μ0 A0 ∧
    (births.chronologyFields heights prior).meetGraph births.limit = completion.externalPointMeet P0 r0 μ0 A0 ∧
    (births.chronologyFields heights prior).birth births.limit = births.birth ∧
    (births.chronologyFields heights prior).height births.limit = heights.height := by
  dsimp only [chronologyFields]
  exact ⟨compressionPrefixValue_limit _ _ _ births.times, compressionPrefixValue_limit _ _ _ births.times,
    compressionPrefixValue_limit _ _ _ births.times, compressionPrefixValue_limit _ _ _ births.times,
    compressionPrefixValue_limit _ _ _ births.times⟩

end PartitionPilot.Forcing.GroundExternalBirthData



namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (prior : GroundChronologicalHistory M T0 C D rD)

theorem chronologyFields_stage_laws
    (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
    (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
    (ordinal : ordinalSetProperty T0) (hOld : oldTimes ∈ T0)
    {s : ZFSet.{u}} (cutoff : s ∈ insert births.limit births.limit) :
    let fields := births.chronologyFields heights prior
    MeetOrderCode (fields.space s) (fields.order s) (fields.meetGraph s) ∧
      ZFSet.IsFunc (fields.space s) (insert births.limit births.limit) (fields.birth s) ∧
      (∀ x ∈ fields.space s, ∀ t, ZFSet.pair x t ∈ fields.birth s → t = s ∨ t ∈ s) ∧
      OldMeetCode (fields.order s) (fields.meetGraph s) (fields.birth s) ∧
      StrictLexHeightCode (fields.space s) C D (fields.order s) (fields.height s) rD := by
  classical
  dsimp only
  by_cases before : s ∈ oldTimes ∨ s = oldTimes
  · have hs := before.elim (fun member => ordinal.1 oldTimes hOld s member)
      (fun equal => equal.symm ▸ hOld)
    obtain ⟨space, order, meet, birth, height⟩ := births.chronologyFields_old heights prior before
    rw [space, order, meet, birth, height]
    exact ⟨prior.meet_order s hs,
      prior.prefix_birth_function_successor births.times ordinal hOld before,
      prior.birth_bound s hs, prior.old_meet s hs, prior.strict_height s hs⟩
  · rcases ZFSet.mem_insert_iff.1 cutoff with rfl | below
    · obtain ⟨space, order, meet, birth, height⟩ := births.chronologyFields_limit heights prior
      rw [space, order, meet, birth, height]
      have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP0
      exact ⟨geometry.meet, isFunc_retarget_of_entries births.function
          (fun _ _ entry => ZFSet.mem_insert_of_mem _ (ZFSet.pair_mem_prod.1 (births.function.1 entry)).2),
        fun _ _ _ entry => Or.inr (ZFSet.pair_mem_prod.1 (births.function.1 entry)).2,
        births.old_meet, heights.code⟩
    · have stamped : ∃ n, s = compressionStamp oldTimes n := by
        rcases (births.times.mem_limit_iff s).1 below with member | equal | stamped
        · exact False.elim (before (Or.inl member))
        · exact False.elim (before (Or.inr equal))
        · exact stamped
      obtain ⟨n, rfl⟩ := stamped
      obtain ⟨space, order, meet, birth, height⟩ := births.chronologyFields_stamp heights prior n
      rw [space, order, meet, birth, height]
      have fields := births.cutoff_fields data group action pairing unions powers separation infinite hG hP0 heights n
      obtain ⟨_, _, _, _, _, meetCode, born, oldMeet, strict, bound⟩ := fields
      exact ⟨meetCode, isFunc_retarget_of_entries born
          (fun _ _ entry => ZFSet.mem_insert_of_mem _ (ZFSet.pair_mem_prod.1 (born.1 entry)).2),
        fun x _ t entry => (bound x t entry).symm, oldMeet, strict⟩

end PartitionPilot.Forcing.GroundExternalBirthData

end OAI
