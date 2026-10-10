import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCompressionOrigins
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundBatchBirths

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
universe u

noncomputable def firstAppearanceBirth (U T Ps stamps oldBirth : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ oldBirth ∨ ∃ n ∈ ZFSet.omega, ∃ D E x t,
    z = ZFSet.pair x t ∧ ZFSet.pair n D ∈ Ps ∧ ZFSet.pair (insert n n) E ∈ Ps ∧
      ZFSet.pair n t ∈ stamps ∧ x ∈ E ∧ x ∉ D) (ZFSet.prod U T)

theorem firstAppearanceBirth_subset (U T Ps stamps oldBirth : ZFSet.{u}) :
    firstAppearanceBirth U T Ps stamps oldBirth ⊆ ZFSet.prod U T :=
  fun _ h => (ZFSet.mem_sep.1 h).1

theorem pair_mem_firstAppearanceBirth (U T Ps stamps oldBirth x t : ZFSet.{u}) :
    ZFSet.pair x t ∈ firstAppearanceBirth U T Ps stamps oldBirth ↔
      x ∈ U ∧ t ∈ T ∧ (ZFSet.pair x t ∈ oldBirth ∨ ∃ n ∈ ZFSet.omega, ∃ D E,
        ZFSet.pair n D ∈ Ps ∧ ZFSet.pair (insert n n) E ∈ Ps ∧
          ZFSet.pair n t ∈ stamps ∧ x ∈ E ∧ x ∉ D) := by
  rw [firstAppearanceBirth, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hx, ht⟩, old | ⟨n, hn, D, E, y, s, equal, before, after, stamp, fresh⟩⟩
    · exact ⟨hx, ht, Or.inl old⟩
    · obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
      exact ⟨hx, ht, Or.inr ⟨n, hn, D, E, before, after, stamp, fresh⟩⟩
  · rintro ⟨hx, ht, old | ⟨n, hn, D, E, before, after, stamp, fresh⟩⟩
    · exact ⟨⟨hx, ht⟩, Or.inl old⟩
    · exact ⟨⟨hx, ht⟩, Or.inr ⟨n, hn, D, E, x, t, rfl, before, after, stamp, fresh⟩⟩

theorem firstAppearanceBirth_nat_iff {U T Ps stamps oldBirth : ZFSet.{u}}
    (P stamp : Nat → ZFSet.{u})
    (domains : ∀ n D, ZFSet.pair (natSetCode n) D ∈ Ps ↔ D = P n)
    (times : ∀ n t, ZFSet.pair (natSetCode n) t ∈ stamps ↔ t = stamp n)
    (x t : ZFSet.{u}) :
    ZFSet.pair x t ∈ firstAppearanceBirth U T Ps stamps oldBirth ↔
      x ∈ U ∧ t ∈ T ∧ (ZFSet.pair x t ∈ oldBirth ∨
        ∃ n, x ∈ P (n + 1) ∧ x ∉ P n ∧ t = stamp n) := by
  rw [pair_mem_firstAppearanceBirth]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨n, hn, D, E, before, after, stampEntry, hx, outside⟩
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    have oldEq := (domains k D).1 before
    have newEq := (domains (k + 1) E).1 after
    exact ⟨k, newEq ▸ hx, oldEq ▸ outside, (times k t).1 stampEntry⟩
  · rintro ⟨n, hx, outside, equal⟩
    exact ⟨natSetCode n, natSetCode_mem_omega n, P n, P (n + 1),
      (domains n _).2 rfl, (domains (n + 1) _).2 rfl, (times n t).2 equal, hx, outside⟩

theorem firstAppearanceBirth_natValue_iff {U T Ps stamps oldBirth : ZFSet.{u}}
    (domains : FunctionGraphOn ZFSet.omega Ps) (times : FunctionGraphOn ZFSet.omega stamps)
    (x t : ZFSet.{u}) :
    ZFSet.pair x t ∈ firstAppearanceBirth U T Ps stamps oldBirth ↔
      x ∈ U ∧ t ∈ T ∧ (ZFSet.pair x t ∈ oldBirth ∨
        ∃ n, x ∈ domains.natValue (n + 1) ∧ x ∉ domains.natValue n ∧ t = times.natValue n) :=
  firstAppearanceBirth_nat_iff domains.natValue times.natValue
    domains.natValue_entry_iff times.natValue_entry_iff x t

theorem firstAppearanceBirth_old_subset {U T Ps stamps oldBirth : ZFSet.{u}}
    (shape : oldBirth ⊆ ZFSet.prod U T) :
    oldBirth ⊆ firstAppearanceBirth U T Ps stamps oldBirth :=
  fun _ entry => ZFSet.mem_sep.2 ⟨shape entry, Or.inl entry⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def firstAppearanceBirthEntryFormula {k} (z omega u t domains stamps old bound : Fin k) :
    BoundedFormula k :=
  disj (.mem z old)
    (exMem omega (exMem omega.succ (exMem bound.succ.succ
      (exMem bound.succ.succ.succ (exMem u.succ.succ.succ.succ
        (exMem t.succ.succ.succ.succ.succ
          (.conj (orderedPairFormula z.succ.succ.succ.succ.succ.succ 1 0)
            (.conj (successorFormula 4 5)
              (.conj (pairMembershipFormula 5 3 domains.succ.succ.succ.succ.succ.succ)
                (.conj (pairMembershipFormula 4 2 domains.succ.succ.succ.succ.succ.succ)
                  (.conj (pairMembershipFormula 5 0 stamps.succ.succ.succ.succ.succ.succ)
                    (.conj (.mem 1 2) (.neg (.mem 1 3))))))))))))))

theorem truth_firstAppearanceBirthEntryFormula {k}
    (z omega u t domains stamps old bound : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (firstAppearanceBirthEntryFormula z omega u t domains stamps old bound) env ↔
      env z ∈ env old ∨ ∃ n ∈ env omega, ∃ m ∈ env omega,
        ∃ D ∈ env bound, ∃ E ∈ env bound, ∃ x ∈ env u, ∃ a ∈ env t,
          env z = ZFSet.pair x a ∧ m = insert n n ∧ ZFSet.pair n D ∈ env domains ∧
            ZFSet.pair m E ∈ env domains ∧ ZFSet.pair n a ∈ env stamps ∧ x ∈ E ∧ x ∉ D := by
  simp only [firstAppearanceBirthEntryFormula, truth_disj, truth_exMem, Truth,
    truth_orderedPairFormula, truth_successorFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem firstAppearanceBirth_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {U T Ps stamps oldBirth : ZFSet.{u}}
    (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets)
    (hU : U ∈ M.sets) (hT : T ∈ M.sets) (hPs : Ps ∈ M.sets)
    (hStamps : stamps ∈ M.sets) (hOld : oldBirth ∈ M.sets) :
    firstAppearanceBirth U T Ps stamps oldBirth ∈ M.sets := by
  have hBound := M.union_mem unions (M.union_mem unions hPs)
  let params := extend ZFSet.omega (extend U (extend T (extend Ps (extend stamps
    (extend oldBirth (extend (⋃₀ ⋃₀ Ps) Fin.elim0))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.firstAppearanceBirthEntryFormula 0 1 2 3 4 5 6 7) params
    (Fin.cases hω (Fin.cases hU (Fin.cases hT (Fin.cases hPs (Fin.cases hStamps
      (Fin.cases hOld (Fin.cases hBound (fun i => Fin.elim0 i))))))))
    (M.prod_mem pairing unions powers separation hU hT)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.firstAppearanceBirthEntryFormula 0 1 2 3 4 5 6 7) (extend z params))
      (ZFSet.prod U T) = firstAppearanceBirth U T Ps stamps oldBirth := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, firstAppearanceBirth, ZFSet.mem_sep,
      BoundedFormula.truth_firstAppearanceBirthEntryFormula]
    change (_ ∧ (z ∈ oldBirth ∨ _)) ↔ _
    apply and_congr_right
    intro bound
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨n, hn, m, _, D, _, E, _, x, _, t, _, pair, successor, before, after, stamp, fresh⟩
      rw [successor] at after
      exact ⟨n, hn, D, E, x, t, pair, before, after, stamp, fresh⟩
    · rintro ⟨n, hn, D, E, x, t, rfl, before, after, stamp, fresh⟩
      have successorMem : insert n n ∈ ZFSet.omega := by
        obtain ⟨j, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
        exact natSetCode_mem_omega (j + 1)
      have points := ZFSet.pair_mem_prod.1 bound
      exact ⟨n, hn, insert n n, successorMem, D, pair_second_mem_doubleUnion before,
        E, pair_second_mem_doubleUnion after, x, points.1, t, points.2,
        rfl, rfl, before, after, stamp, fresh⟩
  exact equal ▸ selected

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

structure NatBirthExtensionCode (P stamp : Nat → ZFSet.{u}) (old birth : ZFSet.{u}) : Prop where
  shape : ∀ z ∈ birth, ∃ x t, z = ZFSet.pair x t
  entries : ∀ x t, ZFSet.pair x t ∈ birth ↔
    ZFSet.pair x t ∈ old ∨ ∃ n, x ∈ P (n + 1) ∧ x ∉ P n ∧ t = stamp n

namespace NatBirthExtensionCode
variable {P stamp : Nat → ZFSet.{u}} {old birth U T : ZFSet.{u}}

theorem first_appearance_unique (mono : ∀ n m, n ≤ m → P n ⊆ P m)
    {n m : Nat} {x : ZFSet.{u}} (hn : x ∈ P (n + 1)) (notN : x ∉ P n)
    (hm : x ∈ P (m + 1)) (notM : x ∉ P m) : n = m := by
  rcases lt_trichotomy n m with before | equal | after
  · exact False.elim (notM (mono (n + 1) m (Nat.succ_le_of_lt before) hn))
  · exact equal
  · exact False.elim (notN (mono (m + 1) n (Nat.succ_le_of_lt after) hm))

theorem first_appearance_exists (carrier : NatUnionCode P U) {x : ZFSet.{u}}
    (hx : x ∈ U) (outside : x ∉ P 0) : ∃ n, x ∈ P (n + 1) ∧ x ∉ P n := by
  obtain ⟨n, hn⟩ := (carrier x).1 hx
  induction n with
  | zero => exact False.elim (outside hn)
  | succ n ih =>
    by_cases before : x ∈ P n
    · exact ih before
    · exact ⟨n, hn, before⟩

variable (code : NatBirthExtensionCode P stamp old birth)
include code

theorem function (carrier : NatUnionCode P U)
    (mono : ∀ n m, n ≤ m → P n ⊆ P m)
    (born : ZFSet.IsFunc (P 0) T old) (stamps : ∀ n, stamp n ∈ T) :
    ZFSet.IsFunc U T birth := by
  constructor
  · intro z hz
    obtain ⟨x, t, rfl⟩ := code.shape z hz
    rcases (code.entries x t).1 hz with oldEntry | ⟨n, hn, _, rfl⟩
    · have bounds := ZFSet.pair_mem_prod.1 (born.1 oldEntry)
      exact ZFSet.pair_mem_prod.2 ⟨carrier.subset 0 bounds.1, bounds.2⟩
    · exact ZFSet.pair_mem_prod.2 ⟨carrier.subset (n + 1) hn, stamps n⟩
  · intro x hx
    by_cases original : x ∈ P 0
    · obtain ⟨t, oldEntry, unique⟩ := born.2 x original
      refine ⟨t, (code.entries x t).2 (Or.inl oldEntry), ?_⟩
      intro s entry
      rcases (code.entries x s).1 entry with before | ⟨n, _, outside, _⟩
      · exact unique s before
      · exact False.elim (outside (mono 0 n (Nat.zero_le n) original))
    · obtain ⟨n, hn, outside⟩ := first_appearance_exists carrier hx original
      refine ⟨stamp n, (code.entries x (stamp n)).2 (Or.inr ⟨n, hn, outside, rfl⟩), ?_⟩
      intro s entry
      rcases (code.entries x s).1 entry with before | ⟨m, hm, notM, equal⟩
      · exact False.elim (original (ZFSet.pair_mem_prod.1 (born.1 before)).1)
      · rw [first_appearance_unique mono hm notM hn outside] at equal
        exact equal

theorem old_entry_iff (mono : ∀ n m, n ≤ m → P n ⊆ P m)
    {x t : ZFSet.{u}} (hx : x ∈ P 0) :
    ZFSet.pair x t ∈ birth ↔ ZFSet.pair x t ∈ old := by
  rw [code.entries]
  constructor
  · rintro (entry | ⟨n, _, outside, _⟩)
    · exact entry
    · exact False.elim (outside (mono 0 n (Nat.zero_le n) hx))
  · exact Or.inl

theorem restriction_zero (mono : ∀ n m, n ≤ m → P n ⊆ P m)
    (born : ZFSet.IsFunc (P 0) T old) : graphRestriction (P 0) birth = old := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, t, rfl, entry⟩ := mem_graphRestriction.1 hz
    exact (code.old_entry_iff mono hx).1 entry
  · intro hz
    obtain ⟨x, hx, t, _, rfl⟩ := ZFSet.mem_prod.1 (born.1 hz)
    exact pair_mem_graphRestriction.2 ⟨(code.old_entry_iff mono hx).2 hz, hx⟩

theorem restriction_function (carrier : NatUnionCode P U)
    (mono : ∀ n m, n ≤ m → P n ⊆ P m)
    (born : ZFSet.IsFunc (P 0) T old) (stamps : ∀ n, stamp n ∈ T) (n : Nat) :
    ZFSet.IsFunc (P n) T (graphRestriction (P n) birth) := by
  have full := code.function carrier mono born stamps
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, t, rfl, entry⟩ := mem_graphRestriction.1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hx, (ZFSet.pair_mem_prod.1 (full.1 entry)).2⟩
  · intro x hx
    obtain ⟨t, entry, unique⟩ := full.2 x (carrier.subset n hx)
    exact ⟨t, pair_mem_graphRestriction.2 ⟨entry, hx⟩,
      fun s hs => unique s (pair_mem_graphRestriction.1 hs).1⟩

theorem restriction_union (carrier : NatUnionCode P U)
    (born : ZFSet.IsFunc (P 0) T old) :
    NatUnionCode (fun n => graphRestriction (P n) birth) birth := by
  intro z
  constructor
  · intro hz
    obtain ⟨x, t, rfl⟩ := code.shape z hz
    have hx : x ∈ U := by
      rcases (code.entries x t).1 hz with original | ⟨n, hn, _, _⟩
      · exact carrier.subset 0 (ZFSet.pair_mem_prod.1 (born.1 original)).1
      · exact carrier.subset (n + 1) hn
    obtain ⟨n, hn⟩ := (carrier x).1 hx
    exact ⟨n, pair_mem_graphRestriction.2 ⟨hz, hn⟩⟩
  · rintro ⟨n, hn⟩
    exact graphRestriction_subset (P n) birth hn

end NatBirthExtensionCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem firstAppearanceBirth_code {U T Ps stamps oldBirth : ZFSet.{u}}
    (P stamp : Nat → ZFSet.{u})
    (domains : ∀ n D, ZFSet.pair (natSetCode n) D ∈ Ps ↔ D = P n)
    (times : ∀ n t, ZFSet.pair (natSetCode n) t ∈ stamps ↔ t = stamp n)
    (carrier : NatUnionCode P U) (born : ZFSet.IsFunc (P 0) T oldBirth)
    (inRange : ∀ n, stamp n ∈ T) :
    NatBirthExtensionCode P stamp oldBirth (firstAppearanceBirth U T Ps stamps oldBirth) := by
  constructor
  · intro z entry
    obtain ⟨x, _, t, _, equal⟩ :=
      ZFSet.mem_prod.1 (firstAppearanceBirth_subset U T Ps stamps oldBirth entry)
    exact ⟨x, t, equal⟩
  · intro x t
    rw [firstAppearanceBirth_nat_iff P stamp domains times]
    constructor
    · exact fun entry => entry.2.2
    · intro entry
      have bounds : x ∈ U ∧ t ∈ T := by
        rcases entry with before | ⟨n, hx, _, rfl⟩
        · have oldBounds := ZFSet.pair_mem_prod.1 (born.1 before)
          exact ⟨carrier.subset 0 oldBounds.1, oldBounds.2⟩
        · exact ⟨carrier.subset (n + 1) hx, inRange n⟩
      exact ⟨bounds.1, bounds.2, entry⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem exists_groundFirstAppearanceBirth
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {U T Ps stamps oldBirth : ZFSet.{u}}
    (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets)
    (hU : U ∈ M.sets) (hT : T ∈ M.sets) (hPs : Ps ∈ M.sets)
    (hStamps : stamps ∈ M.sets) (hOld : oldBirth ∈ M.sets)
    (P stamp : Nat → ZFSet.{u})
    (domains : ∀ n D, ZFSet.pair (natSetCode n) D ∈ Ps ↔ D = P n)
    (times : ∀ n t, ZFSet.pair (natSetCode n) t ∈ stamps ↔ t = stamp n)
    (carrier : NatUnionCode P U) (born : ZFSet.IsFunc (P 0) T oldBirth)
    (inRange : ∀ n, stamp n ∈ T) :
    ∃ birth ∈ M.sets, birth = firstAppearanceBirth U T Ps stamps oldBirth ∧
      NatBirthExtensionCode P stamp oldBirth birth :=
  ⟨firstAppearanceBirth U T Ps stamps oldBirth,
    M.firstAppearanceBirth_mem pairing unions powers separation hω hU hT hPs hStamps hOld,
    rfl, firstAppearanceBirth_code P stamp domains times carrier born inRange⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.NatBirthExtensionCode
universe u
variable {P stamp : Nat → ZFSet.{u}} {old birth T : ZFSet.{u}}
variable (code : NatBirthExtensionCode P stamp old birth)
variable (mono : ∀ n m, n ≤ m → P n ⊆ P m)
variable (born : ZFSet.IsFunc (P 0) T old)
include code

omit code in
include mono in
theorem restriction_mono {n m : Nat} (before : n ≤ m) :
    graphRestriction (P n) birth ⊆ graphRestriction (P m) birth := by
  intro z hz
  obtain ⟨x, hx, t, rfl, entry⟩ := mem_graphRestriction.1 hz
  exact pair_mem_graphRestriction.2 ⟨entry, mono n m before hx⟩

include mono born in
theorem restriction_step (n : Nat) {N : ZFSet.{u}}
    (next : P (n + 1) = taggedExtension (P n) N) :
    graphRestriction (P (n + 1)) birth = taggedBirth (P n) N (graphRestriction (P n) birth) (stamp n) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, t, rfl, entry⟩ := mem_graphRestriction.1 hz
    apply (pair_mem_taggedBirth _ _ _ _ _ _).2
    by_cases oldPoint : x ∈ P n
    · exact Or.inl (pair_mem_graphRestriction.2 ⟨entry, oldPoint⟩)
    · have fresh : x ∈ ZFSet.prod {P n} N := by
        rw [next] at hx
        exact (ZFSet.mem_union.1 hx).resolve_left oldPoint
      rcases (code.entries x t).1 entry with original | ⟨m, hm, notM, equal⟩
      · exact False.elim (oldPoint (mono 0 n (Nat.zero_le n)
          (ZFSet.pair_mem_prod.1 (born.1 original)).1))
      · have same := first_appearance_unique mono hm notM hx oldPoint
        exact Or.inr ⟨fresh, same ▸ equal⟩
  · intro hz
    rcases ZFSet.mem_union.1 hz with original | fresh
    · obtain ⟨x, hx, t, rfl, entry⟩ := mem_graphRestriction.1 original
      exact pair_mem_graphRestriction.2 ⟨entry, mono n (n + 1) (Nat.le_succ n) hx⟩
    · obtain ⟨x, hx, t, ht, rfl⟩ := ZFSet.mem_prod.1 fresh
      obtain rfl := ZFSet.mem_singleton.1 ht
      have current : x ∈ P (n + 1) := by
        rw [next]
        exact ZFSet.mem_union.2 (Or.inr hx)
      have outside : x ∉ P n := fun h => taggedExtension_disjoint (P n) N x h hx
      exact pair_mem_graphRestriction.2
        ⟨(code.entries x (stamp n)).2 (Or.inr ⟨n, current, outside, rfl⟩), current⟩

include mono in
theorem restriction_bound
    (oldBound : ∀ n x t, ZFSet.pair x t ∈ old → t ∈ stamp n)
    (stampBefore : ∀ n m, n < m → stamp n ∈ stamp m)
    (n : Nat) {x t : ZFSet.{u}} (entry : ZFSet.pair x t ∈ graphRestriction (P n) birth) :
    t ∈ stamp n := by
  obtain ⟨entry, hx⟩ := pair_mem_graphRestriction.1 entry
  rcases (code.entries x t).1 entry with original | ⟨m, _, notM, rfl⟩
  · exact oldBound n x t original
  · exact stampBefore m n (lt_of_not_ge (fun h => notM (mono n m h hx)))

include mono born in
theorem earlier_fiber
    (stampMono : ∀ n m, n ≤ m → stamp n ⊆ stamp m)
    (n : Nat) {x t : ZFSet.{u}} (before : t ∈ stamp n)
    (entry : ZFSet.pair x t ∈ birth) :
    x ∈ P n ∧ ZFSet.pair x t ∈ graphRestriction (P n) birth := by
  have hx : x ∈ P n := by
    rcases (code.entries x t).1 entry with original | ⟨m, hm, _, rfl⟩
    · exact mono 0 n (Nat.zero_le n) (ZFSet.pair_mem_prod.1 (born.1 original)).1
    · have smaller : m < n := lt_of_not_ge
        (fun h => ZFSet.mem_irrefl (stamp m) (stampMono n m h before))
      exact mono (m + 1) n (Nat.succ_le_of_lt smaller) hm
  exact ⟨hx, pair_mem_graphRestriction.2 ⟨entry, hx⟩⟩

end PartitionPilot.Forcing.NatBirthExtensionCode



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
variable {base stamps limit old birth : ZFSet.{u}}
variable (code : NatBirthExtensionCode (fun n => (state.data.iterate M I Sources Reps G T n).D)
    (compressionStamp base) old birth)
variable (born : ZFSet.IsFunc state.data.D limit old)
variable (times : CompressionStampCode base stamps limit)
include pairing unions powers separation hI hSources hReps hG hT code

include data born times in
theorem canonical_birth_function (n : Nat) :
    ZFSet.IsFunc (state.data.iterate M I Sources Reps G T n).D limit
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth) :=
  code.restriction_function (data.fieldUnion 0)
    (fun _ _ h => (state.canonical_iterate_graphs_mono pairing unions powers separation
      hI hSources hReps hG hT h).1) born times.stamp_mem_limit n

include born in
theorem canonical_birth_step (n : Nat) :
    graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D birth =
      taggedBirth (state.data.iterate M I Sources Reps G T n).D
        (state.data.iterate M I Sources Reps G T n).fresh
        (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth)
        (compressionStamp base n) :=
  code.restriction_step
    (fun _ _ h => (state.canonical_iterate_graphs_mono pairing unions powers separation
      hI hSources hReps hG hT h).1) born n rfl

theorem canonical_birth_before_stamp
    (oldBound : ∀ x t, ZFSet.pair x t ∈ old → t ∈ base ∨ t = base)
    (n : Nat) {x t : ZFSet.{u}}
    (entry : ZFSet.pair x t ∈ graphRestriction (state.data.iterate M I Sources Reps G T n).D birth) :
    t ∈ compressionStamp base n :=
  code.restriction_bound
    (fun _ _ h => (state.canonical_iterate_graphs_mono pairing unions powers separation
      hI hSources hReps hG hT h).1)
    (fun n x t h => compressionStamp_old_mem (oldBound x t h) n)
    (fun n k h => (compressionStamp_mem_iff base n k).2 h) n entry

include data born times in
theorem canonical_birth_oldMeet
    (oldBound : ∀ x t, ZFSet.pair x t ∈ old → t ∈ base ∨ t = base)
    (oldMeet : OldMeetCode state.data.rD state.data.μD old) (n : Nat) :
    OldMeetCode (state.data.iterate M I Sources Reps G T n).rD
      (state.data.iterate M I Sources Reps G T n).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth) := by
  induction n with
  | zero =>
    rw [code.restriction_zero
      (fun _ _ h => (state.canonical_iterate_graphs_mono pairing unions powers separation
        hI hSources hReps hG hT h).1) born]
    exact oldMeet
  | succ n ih =>
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT n
    have finite : ZFSet.IsFunc current.data.D limit
        (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth) := by
      simpa only [equal] using state.canonical_birth_function data pairing unions powers separation
        hI hSources hReps hG hT code born times n
    have oldLaw : OldMeetCode current.data.rD current.data.μD
        (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth) := by
      simpa only [equal] using ih
    have earlier (x t : ZFSet.{u})
        (h : ZFSet.pair x t ∈ graphRestriction (state.data.iterate M I Sources Reps G T n).D birth) :=
      state.canonical_birth_before_stamp pairing unions powers separation
        hI hSources hReps hG hT code oldBound n h
    have result := current.batch.batchBirth_oldMeet finite earlier oldLaw
    change OldMeetCode current.data.currentOrder current.data.currentMeet
      (taggedBirth current.data.D current.data.fresh
        (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth)
        (compressionStamp base n)) at result
    rw [state.canonical_birth_step pairing unions powers separation hI hSources hReps hG hT code born n]
    simpa only [equal, RecursiveStateData.iterate_succ, RecursiveStateData.successor] using result

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
variable {base stamps limit old birth : ZFSet.{u}}
variable (code : NatBirthExtensionCode (fun n => (state.data.iterate M I Sources Reps G T n).D)
    (compressionStamp base) old birth)
variable (born : ZFSet.IsFunc state.data.D limit old)
variable {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
include pairing unions powers separation hI hSources hReps hG hT code born

noncomputable def canonical_birth_layer_to_union (n : Nat) {t : ZFSet.{u}}
    (before : t ∈ compressionStamp base n)
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet
      (state.data.iterate M I Sources Reps G T n).D
      (state.data.iterate M I Sources Reps G T n).rD
      (state.data.iterate M I Sources Reps G T n).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth) t) :
    CodedGrowthLayer M Space sourceOrder sourceMeet
      (data.fields 0) (data.fields 1) (data.fields 2) birth t := by
  have mono := fun n k h => (state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT (n := n) (k := k) h).1
  have ground : (state.data.iterate M I Sources Reps G T n).D ∈ M.sets := by
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT n
    rw [← equal]
    exact current.ground.carrier
  exact layer.of_literal_extension separation ground
    ((data.fieldUnion 0).subset n) ((data.fieldUnion 1).subset n)
    ((data.fieldUnion 2).subset n)
    (graphRestriction_subset (state.data.iterate M I Sources Reps G T n).D birth)
    (fun _ _ entry => code.earlier_fiber mono born
      (fun _ _ h => compressionStamp_subset base h) n before entry)

noncomputable def prior_birth_layer_to_union {t : ZFSet.{u}} (priorTime : t ∈ base ∨ t = base)
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet
      state.data.D state.data.rD state.data.μD old t) :
    CodedGrowthLayer M Space sourceOrder sourceMeet
      (data.fields 0) (data.fields 1) (data.fields 2) birth t := by
  have mono := fun n k h => (state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT (n := n) (k := k) h).1
  have zero := code.restriction_zero mono born
  apply state.canonical_birth_layer_to_union data pairing unions powers separation
    hI hSources hReps hG hT code born 0 (compressionStamp_old_mem priorTime 0)
  rw [zero]
  simpa only [RecursiveStateData.iterate_zero] using layer

def limit_birth_layer_empty (times : CompressionStampCode base stamps limit) :
    CodedGrowthLayer M Space sourceOrder sourceMeet
      (data.fields 0) (data.fields 1) (data.fields 2) birth limit := by
  have mono := fun n k h => (state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT (n := n) (k := k) h).1
  have function := code.function (data.fieldUnion 0) mono born times.stamp_mem_limit
  exact .empty_at_birth_bound ⟨data.fields 0, data.ground 0⟩
    (fun _ _ entry => (ZFSet.pair_mem_prod.1 (function.1 entry)).2)

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing
universe u

structure GroundCompressionBirthData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T : ZFSet.{u})
    (data : GroundCompressionUnionData M initial I Sources Reps G m one T)
    (base old : ZFSet.{u}) where
  stamps : ZFSet.{u}
  stamps_ground : stamps ∈ M.sets
  limit : ZFSet.{u}
  limit_ground : limit ∈ M.sets
  times : CompressionStampCode base stamps limit
  birth : ZFSet.{u}
  birth_ground : birth ∈ M.sets
  extension : NatBirthExtensionCode (fun n => (initial.iterate M I Sources Reps G T n).D)
    (compressionStamp base) old birth
  family : ZFSet.{u}
  family_ground : family ∈ M.sets
  family_function : FunctionGraphOn ZFSet.omega family
  family_entries : ∀ n b, ZFSet.pair (natSetCode n) b ∈ family ↔
    b = graphRestriction (initial.iterate M I Sources Reps G T n).D birth
  initial_function : ZFSet.IsFunc initial.D limit old
  initial_bound : ∀ x t, ZFSet.pair x t ∈ old → t ∈ base ∨ t = base
  function : ZFSet.IsFunc (data.fields 0) limit birth
  original : graphRestriction initial.D birth = old
  finite_old_meet : ∀ n, OldMeetCode (initial.iterate M I Sources Reps G T n).rD
    (initial.iterate M I Sources Reps G T n).μD
    (graphRestriction (initial.iterate M I Sources Reps G T n).D birth)
  old_meet : OldMeetCode (data.fields 1) (data.fields 2) birth
  no_limit_birth : ∀ x, ZFSet.pair x limit ∉ birth

end PartitionPilot.Forcing

end OAI
