import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCompressionStampBounds
import OAI.SetTheory.PartitionPrinciple.Geometry.GrowthLayerSourceCongruence

namespace OAI

namespace PartitionPilot.Forcing
universe u

noncomputable def ownerFresh (P B : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => x ∉ P) B

theorem mem_ownerFresh (P B x : ZFSet.{u}) :
    x ∈ ownerFresh P B ↔ x ∈ B ∧ x ∉ P := ZFSet.mem_sep

noncomputable def ownerBirthGraph (P B T old levels stamps : ZFSet.{u}) : ZFSet.{u} :=
  old ∪ relationCompose (ownerFresh P B) ZFSet.omega T levels stamps

theorem pair_mem_ownerBirthGraph (P B T old levels stamps x t : ZFSet.{u}) :
    ZFSet.pair x t ∈ ownerBirthGraph P B T old levels stamps ↔
      ZFSet.pair x t ∈ old ∨
        x ∈ B ∧ x ∉ P ∧ t ∈ T ∧ ∃ n ∈ ZFSet.omega,
          ZFSet.pair x n ∈ levels ∧ ZFSet.pair n t ∈ stamps := by
  rw [ownerBirthGraph, ZFSet.mem_union, pair_mem_relationCompose, mem_ownerFresh]
  tauto

theorem ownerBirthGraph_old_subset (P B T old levels stamps : ZFSet.{u}) :
    old ⊆ ownerBirthGraph P B T old levels stamps :=
  fun _ h => ZFSet.mem_union.2 (Or.inl h)

theorem ownerBirthGraph_old_iff {P B T old levels stamps x t : ZFSet.{u}}
    (hx : x ∈ P) :
    ZFSet.pair x t ∈ ownerBirthGraph P B T old levels stamps ↔ ZFSet.pair x t ∈ old := by
  rw [pair_mem_ownerBirthGraph]
  exact ⟨fun h => h.elim id (fun h => (h.2.1 hx).elim), Or.inl⟩

theorem ownerBirthGraph_fresh_iff {P B T T0 old levels stamps x t : ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P T0 old) (hx : x ∉ P) :
    ZFSet.pair x t ∈ ownerBirthGraph P B T old levels stamps ↔
      x ∈ B ∧ t ∈ T ∧ ∃ n ∈ ZFSet.omega,
        ZFSet.pair x n ∈ levels ∧ ZFSet.pair n t ∈ stamps := by
  rw [pair_mem_ownerBirthGraph]
  constructor
  · rintro (oldEntry | fresh)
    · exact (hx (ZFSet.pair_mem_prod.1 (oldFunction.1 oldEntry)).1).elim
    · exact ⟨fresh.1, fresh.2.2⟩
  · rintro ⟨hB, ht, n, hn, level, stamp⟩
    exact Or.inr ⟨hB, hx, ht, n, hn, level, stamp⟩

theorem ownerBirthGraph_function {P B T T0 old levels stamps : ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P T0 old) (oldSubset : P ⊆ B) (times : T0 ⊆ T)
    (levelFunction : ZFSet.IsFunc (ownerFresh P B) ZFSet.omega levels)
    (stampFunction : ZFSet.IsFunc ZFSet.omega T stamps) :
    ZFSet.IsFunc B T (ownerBirthGraph P B T old levels stamps) := by
  have freshFunction := relationCompose_function_of_subset levelFunction stampFunction (fun _ h => h)
  constructor
  · intro z hz
    rcases ZFSet.mem_union.1 hz with oldEntry | freshEntry
    · obtain ⟨x, hx, t, ht, rfl⟩ := ZFSet.mem_prod.1 (oldFunction.1 oldEntry)
      exact ZFSet.pair_mem_prod.2 ⟨oldSubset hx, times ht⟩
    · obtain ⟨x, hx, t, ht, rfl⟩ := ZFSet.mem_prod.1 (freshFunction.1 freshEntry)
      exact ZFSet.pair_mem_prod.2 ⟨(mem_ownerFresh P B x).1 hx |>.1, ht⟩
  · intro x hx
    by_cases oldPoint : x ∈ P
    · obtain ⟨t, entry, unique⟩ := oldFunction.2 x oldPoint
      exact ⟨t, (ownerBirthGraph_old_iff oldPoint).2 entry,
        fun y hy => unique y ((ownerBirthGraph_old_iff oldPoint).1 hy)⟩
    · have freshPoint := (mem_ownerFresh P B x).2 ⟨hx, oldPoint⟩
      obtain ⟨t, entry, unique⟩ := freshFunction.2 x freshPoint
      refine ⟨t, ZFSet.mem_union.2 (Or.inr entry), ?_⟩
      intro y hy
      rcases ZFSet.mem_union.1 hy with oldEntry | freshEntry
      · exact (oldPoint (ZFSet.pair_mem_prod.1 (oldFunction.1 oldEntry)).1).elim
      · exact unique y freshEntry

theorem ownerBirthGraph_restriction {P B T T0 old levels stamps : ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P T0 old) :
    graphRestriction P (ownerBirthGraph P B T old levels stamps) = old := by
  apply ZFSet.ext
  intro z
  constructor
  · intro h
    obtain ⟨x, hx, t, rfl, entry⟩ := mem_graphRestriction.1 h
    exact (ownerBirthGraph_old_iff hx).1 entry
  · intro h
    obtain ⟨x, hx, t, _, rfl⟩ := ZFSet.mem_prod.1 (oldFunction.1 h)
    exact pair_mem_graphRestriction.2 ⟨(ownerBirthGraph_old_iff hx).2 h, hx⟩

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem ownerFresh_mem (separation : SeparationSchema M.sets)
    {P B : ZFSet.{u}} (hP : P ∈ M.sets) (hB : B ∈ M.sets) :
    ownerFresh P B ∈ M.sets := by
  let params := extend P Fin.elim0
  let formula : BoundedFormula 2 := .neg (.mem 0 1)
  exact M.bounded_separation_mem separation formula params
    (Fin.cases hP (fun j => Fin.elim0 j)) hB

theorem ownerBirthGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P B T old levels stamps : ZFSet.{u}}
    (hP : P ∈ M.sets) (hB : B ∈ M.sets) (hT : T ∈ M.sets)
    (hOld : old ∈ M.sets) (hLevels : levels ∈ M.sets) (hStamps : stamps ∈ M.sets)
    (hOmega : ZFSet.omega ∈ M.sets) :
    ownerBirthGraph P B T old levels stamps ∈ M.sets := by
  exact M.binary_union_mem pairing unions hOld
    (M.relationCompose_mem pairing unions powers separation
      (M.ownerFresh_mem separation hP hB) hOmega hT hLevels hStamps)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
universe u

structure OwnerStampCode (T stamps : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc ZFSet.omega T stamps
  strict : ∀ n m a b,
    ZFSet.pair (natSetCode n) a ∈ stamps → ZFSet.pair (natSetCode m) b ∈ stamps →
      (a ∈ b ↔ n < m)

theorem CompressionStampCode.ownerStampCode {base stamps T : ZFSet.{u}}
    (code : CompressionStampCode base stamps T) : OwnerStampCode T stamps := by
  refine ⟨code.function, ?_⟩
  intro n m a b first second
  rw [(code.entries n a).1 first, (code.entries m b).1 second]
  exact compressionStamp_mem_iff base n m

theorem OwnerStampCode.injective {T stamps : ZFSet.{u}}
    (code : OwnerStampCode T stamps) {n m : Nat} {t : ZFSet.{u}}
    (first : ZFSet.pair (natSetCode n) t ∈ stamps)
    (second : ZFSet.pair (natSetCode m) t ∈ stamps) : n = m := by
  have notBefore : ¬ n < m := fun h => ZFSet.mem_irrefl t ((code.strict n m t t first second).2 h)
  have notAfter : ¬ m < n := fun h => ZFSet.mem_irrefl t ((code.strict m n t t second first).2 h)
  omega

theorem ownerBirthGraph_fresh_nat_iff {P B T T0 old levels stamps x t : ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P T0 old) (hx : x ∉ P) :
    ZFSet.pair x t ∈ ownerBirthGraph P B T old levels stamps ↔
      x ∈ B ∧ t ∈ T ∧ ∃ n : Nat,
        ZFSet.pair x (natSetCode n) ∈ levels ∧ ZFSet.pair (natSetCode n) t ∈ stamps := by
  rw [ownerBirthGraph_fresh_iff oldFunction hx]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨i, hi, level, stamp⟩
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode i).1 hi
    exact ⟨n, level, stamp⟩
  · rintro ⟨n, level, stamp⟩
    exact ⟨natSetCode n, (mem_omega_iff_natSetCode _).2 ⟨n, rfl⟩, level, stamp⟩

theorem ownerBirthGraph_oldMeet {P B r μ T T0 old levels stamps : ZFSet.{u}}
    (meet : MeetOrderCode B r μ) (oldFunction : ZFSet.IsFunc P T0 old)
    (oldSubset : P ⊆ B) (times : T0 ⊆ T)
    (levelFunction : ZFSet.IsFunc (ownerFresh P B) ZFSet.omega levels)
    (stampCode : OwnerStampCode T stamps)
    (oldMeet : OldMeetCode r μ old)
    (oldIdeal : ∀ x ∈ B, ∀ y ∈ P, ZFSet.pair x y ∈ r → x ∈ P)
    (oldBefore : ∀ x a n t, ZFSet.pair x a ∈ old →
      ZFSet.pair (natSetCode n) t ∈ stamps → a ∈ t)
    (levelMono : ∀ x ∈ ownerFresh P B, ∀ y ∈ ownerFresh P B, ∀ n m,
      ZFSet.pair x (natSetCode n) ∈ levels → ZFSet.pair y (natSetCode m) ∈ levels →
      ZFSet.pair x y ∈ r → n ≤ m) :
    OldMeetCode r μ (ownerBirthGraph P B T old levels stamps) := by
  have born := ownerBirthGraph_function oldFunction oldSubset times levelFunction stampCode.function
  intro x y z a b c ya xb before notLower xy zc
  have hy := (ZFSet.pair_mem_prod.1 (born.1 ya)).1
  have hz := (ZFSet.pair_mem_prod.1 (born.1 zc)).1
  by_cases xOld : x ∈ P
  · have xbOld := (ownerBirthGraph_old_iff xOld).1 xb
    by_cases yOld : y ∈ P
    · have zOld := oldIdeal z hz x xOld (meet.lower_left x y z xy)
      exact oldMeet x y z a b c ((ownerBirthGraph_old_iff yOld).1 ya) xbOld before notLower xy
        ((ownerBirthGraph_old_iff zOld).1 zc)
    · obtain ⟨_, _, m, _, stampY⟩ := (ownerBirthGraph_fresh_nat_iff oldFunction yOld).1 ya
      exact (ZFSet.mem_asymm before (oldBefore x b m a xbOld stampY)).elim
  · obtain ⟨_, _, n, _, stampX⟩ := (ownerBirthGraph_fresh_nat_iff oldFunction xOld).1 xb
    by_cases zOld : z ∈ P
    · exact oldBefore z c n b ((ownerBirthGraph_old_iff zOld).1 zc) stampX
    · have yOld : y ∉ P := fun member => zOld (oldIdeal z hz y member (meet.lower_right x y z xy))
      obtain ⟨_, _, m, levelY, stampY⟩ := (ownerBirthGraph_fresh_nat_iff oldFunction yOld).1 ya
      obtain ⟨_, _, k, levelZ, stampZ⟩ := (ownerBirthGraph_fresh_nat_iff oldFunction zOld).1 zc
      have lowerLevels := levelMono z ((mem_ownerFresh P B z).2 ⟨hz, zOld⟩)
        y ((mem_ownerFresh P B y).2 ⟨hy, yOld⟩) k m levelZ levelY (meet.lower_right x y z xy)
      exact (stampCode.strict k n c b stampZ stampX).2
        (Nat.lt_of_le_of_lt lowerLevels ((stampCode.strict m n a b stampY stampX).1 before))

theorem ownerBirthGraph_stamp_fiber {P B T T0 old levels stamps : ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P T0 old)
    (stampCode : OwnerStampCode T stamps)
    (oldBefore : ∀ x a n t, ZFSet.pair x a ∈ old →
      ZFSet.pair (natSetCode n) t ∈ stamps → a ∈ t)
    {n : Nat} {t x : ZFSet.{u}} (stamp : ZFSet.pair (natSetCode n) t ∈ stamps) :
    ZFSet.pair x t ∈ ownerBirthGraph P B T old levels stamps ↔
      x ∈ ownerFresh P B ∧ ZFSet.pair x (natSetCode n) ∈ levels := by
  constructor
  · intro entry
    have fresh : x ∉ P := by
      intro oldPoint
      exact ZFSet.mem_irrefl t (oldBefore x t n t ((ownerBirthGraph_old_iff oldPoint).1 entry) stamp)
    obtain ⟨hx, _, k, level, value⟩ := (ownerBirthGraph_fresh_nat_iff oldFunction fresh).1 entry
    have equal := stampCode.injective value stamp
    exact ⟨(mem_ownerFresh P B x).2 ⟨hx, fresh⟩, equal ▸ level⟩
  · rintro ⟨fresh, level⟩
    have hx := (mem_ownerFresh P B x).1 fresh
    exact (ownerBirthGraph_fresh_nat_iff oldFunction hx.2).2
      ⟨hx.1, (ZFSet.pair_mem_prod.1 (stampCode.function.1 stamp)).2, n, level, stamp⟩

theorem ownerBirthGraph_earlier_of_level {P B T T0 old levels stamps : ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P T0 old)
    (levelFunction : ZFSet.IsFunc (ownerFresh P B) ZFSet.omega levels)
    (stampCode : OwnerStampCode T stamps)
    (oldBefore : ∀ x a n t, ZFSet.pair x a ∈ old →
      ZFSet.pair (natSetCode n) t ∈ stamps → a ∈ t)
    {n : Nat} {t x a : ZFSet.{u}} (stamp : ZFSet.pair (natSetCode n) t ∈ stamps)
    (entry : ZFSet.pair x a ∈ ownerBirthGraph P B T old levels stamps)
    (earlier : x ∈ P ∨ ∃ k < n, ZFSet.pair x (natSetCode k) ∈ levels) : a ∈ t := by
  rcases earlier with oldPoint | ⟨k, before, level⟩
  · exact oldBefore x a n t ((ownerBirthGraph_old_iff oldPoint).1 entry) stamp
  · have fresh := (ZFSet.pair_mem_prod.1 (levelFunction.1 level)).1
    have hx := (mem_ownerFresh P B x).1 fresh
    obtain ⟨_, _, j, actualLevel, actualStamp⟩ := (ownerBirthGraph_fresh_nat_iff oldFunction hx.2).1 entry
    obtain ⟨_, _, unique⟩ := levelFunction.2 x fresh
    have equal : j = k := natSetCode_injective
      ((unique _ actualLevel).trans (unique _ level).symm)
    exact (stampCode.strict j n a t actualStamp stamp).2 (equal.symm ▸ before)

noncomputable def ownerBirthGraph_separated
    {M : TransitiveGround.{u}} {P B L r μ T T0 old levels stamps : ZFSet.{u}}
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P T0 old) (oldSubset : P ⊆ B) (times : T0 ⊆ T)
    (levelFunction : ZFSet.IsFunc (ownerFresh P B) ZFSet.omega levels)
    (stampCode : OwnerStampCode T stamps)
    (oldBefore : ∀ x a n t, ZFSet.pair x a ∈ old →
      ZFSet.pair (natSetCode n) t ∈ stamps → a ∈ t)
    {n : Nat} {t : ZFSet.{u}} (stamp : ZFSet.pair (natSetCode n) t ∈ stamps)
    (I : Type u) (index e : I → ZFSet.{u})
    (copyEarlier : ∀ i, index i ∈ t) (groundCopy : ∀ i, e i ∈ M.sets)
    (embedding : ∀ i, MeetEmbeddingCode (Space (index i)) L
      (sourceOrder (index i)) r (sourceMeet (index i)) μ (e i))
    (component : {x : ZFSet.{u} // x ∈ ownerFresh P B ∧
      ZFSet.pair x (natSetCode n) ∈ levels} → I)
    (cover : ∀ x : {x : ZFSet.{u} // x ∈ ownerFresh P B ∧
      ZFSet.pair x (natSetCode n) ∈ levels}, x.val ∈ L →
        x.val ∈ relationImage (Space (index (component x))) L (e (component x)))
    (separated : ∀ x y : {x : ZFSet.{u} // x ∈ ownerFresh P B ∧
      ZFSet.pair x (natSetCode n) ∈ levels}, x.val ∈ L → y.val ∈ L →
      component x ≠ component y → ∃ z ∈ B, ZFSet.pair (ZFSet.pair x.val y.val) z ∈ μ ∧
        (z ∈ P ∨ ∃ k < n, ZFSet.pair z (natSetCode k) ∈ levels)) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L r μ
      (ownerBirthGraph P B T old levels stamps) t := by
  let born := ownerBirthGraph_function oldFunction oldSubset times levelFunction stampCode.function
  let fresh (x : {x : ZFSet.{u} // x ∈ L ∧
      ZFSet.pair x t ∈ ownerBirthGraph P B T old levels stamps}) :
      {x : ZFSet.{u} // x ∈ ownerFresh P B ∧ ZFSet.pair x (natSetCode n) ∈ levels} :=
    ⟨x.val, (ownerBirthGraph_stamp_fiber oldFunction stampCode oldBefore stamp).1 x.property.2⟩
  refine .separated I index e copyEarlier groundCopy embedding (fun x => component (fresh x)) ?_ ?_
  · intro x
    exact cover (fresh x) x.property.1
  · intro x y different
    obtain ⟨z, hz, meet, earlier⟩ := separated (fresh x) (fresh y) x.property.1 y.property.1 different
    obtain ⟨a, entry, _⟩ := born.2 z hz
    exact Or.inl ⟨z, a, meet, entry,
      ownerBirthGraph_earlier_of_level oldFunction levelFunction stampCode oldBefore stamp entry earlier⟩

end PartitionPilot.Forcing

end OAI
