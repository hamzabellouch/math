import OAI.SetTheory.PartitionPrinciple.Geometry.GroundVisibilitySupportIncidence

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

def SynchronizedEnumerationCode (omega N B f e names : ZFSet.{u}) : Prop :=
  ZFSet.IsFunc B N f ∧ ZFSet.IsFunc omega B e ∧ ZFSet.IsFunc omega N names ∧
    (∀ v ∈ B, ∃ n ∈ omega, ZFSet.pair n v ∈ e) ∧
    (∀ n ∈ omega, ∀ v tau, ZFSet.pair n v ∈ e →
      ZFSet.pair n tau ∈ names → ZFSet.pair v tau ∈ f) ∧
    (∀ n ∈ omega, ∀ v tau, ZFSet.pair n v ∈ e →
      ZFSet.pair v tau ∈ f → ZFSet.pair n tau ∈ names)

namespace BoundedFormula
open SetFormula

def synchronizedEnumerationFormula {n} (omega N B f e names : Fin n) : BoundedFormula n :=
  .conj (functionFormula B N f)
    (.conj (functionFormula omega B e)
      (.conj (functionFormula omega N names)
        (.conj (.allMem B (exMem omega.succ (pairMembershipFormula 0 1 e.succ.succ)))
          (.conj
            (.allMem omega (.allMem B.succ (.allMem N.succ.succ
              (imp (pairMembershipFormula 2 1 e.succ.succ.succ)
                (imp (pairMembershipFormula 2 0 names.succ.succ.succ)
                  (pairMembershipFormula 1 0 f.succ.succ.succ))))))
            (.allMem omega (.allMem B.succ (.allMem N.succ.succ
              (imp (pairMembershipFormula 2 1 e.succ.succ.succ)
                (imp (pairMembershipFormula 1 0 f.succ.succ.succ)
                  (pairMembershipFormula 2 0 names.succ.succ.succ))))))))))

theorem truth_synchronizedEnumerationFormula {n} (omega N B f e names : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (synchronizedEnumerationFormula omega N B f e names) env ↔
      SynchronizedEnumerationCode (env omega) (env N) (env B) (env f) (env e) (env names) := by
  simp only [synchronizedEnumerationFormula, Truth, truth_functionFormula,
    truth_exMem, truth_pairMembershipFormula, truth_imp]
  change (ZFSet.IsFunc (env B) (env N) (env f) ∧
    ZFSet.IsFunc (env omega) (env B) (env e) ∧
    ZFSet.IsFunc (env omega) (env N) (env names) ∧
    (∀ v ∈ env B, ∃ n ∈ env omega, ZFSet.pair n v ∈ env e) ∧
    (∀ n ∈ env omega, ∀ v ∈ env B, ∀ tau ∈ env N, ZFSet.pair n v ∈ env e →
      ZFSet.pair n tau ∈ env names → ZFSet.pair v tau ∈ env f) ∧
    (∀ n ∈ env omega, ∀ v ∈ env B, ∀ tau ∈ env N, ZFSet.pair n v ∈ env e →
      ZFSet.pair v tau ∈ env f → ZFSet.pair n tau ∈ env names)) ↔ _
  constructor
  · rintro ⟨ff, ef, nf, onto, forward, backward⟩
    refine ⟨ff, ef, nf, onto, ?_, ?_⟩
    · intro n hn v tau nv nt
      exact forward n hn v (ZFSet.pair_mem_prod.1 (ef.1 nv)).2
        tau (ZFSet.pair_mem_prod.1 (nf.1 nt)).2 nv nt
    · intro n hn v tau nv vt
      exact backward n hn v (ZFSet.pair_mem_prod.1 (ef.1 nv)).2
        tau (ZFSet.pair_mem_prod.1 (ff.1 vt)).2 nv vt
  · rintro ⟨ff, ef, nf, onto, forward, backward⟩
    exact ⟨ff, ef, nf, onto, fun n hn v _ tau _ => forward n hn v tau,
      fun n hn v _ tau _ => backward n hn v tau⟩

def certificateEnumerationEntryFormula {n} (entry J E Names omega N k : Fin n) :
    BoundedFormula n :=
  exPairFields entry (exPairFields 0
    (exGraphFields k.succ.succ.succ.succ (exPairFields 0 (exPairFields 0
      (.conj (.equal 5 9)
        (.conj (.mem 9 J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
          (.conj (.mem 7 E.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
            (.conj (.mem 6 Names.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
              (synchronizedEnumerationFormula
                omega.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
                N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 1 0 7 6)))))))))

theorem truth_certificateEnumerationEntryFormula {n} (entry J E Names omega N k : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (certificateEnumerationEntryFormula entry J E Names omega N k) env ↔
      ∃ j ∈ env J, ∃ e ∈ env E, ∃ names ∈ env Names,
        env entry = ZFSet.pair j (ZFSet.pair e names) ∧
        ∃ F B f, ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ env k ∧
          SynchronizedEnumerationCode (env omega) (env N) B f e names := by
  simp only [certificateEnumerationEntryFormula, truth_exPairFields, truth_exGraphFields,
    Truth, truth_synchronizedEnumerationFormula]
  change (∃ j pair, env entry = ZFSet.pair j pair ∧
    ∃ e names, pair = ZFSet.pair e names ∧
    ∃ j' certificate, ZFSet.pair j' certificate ∈ env k ∧
    ∃ F tail, certificate = ZFSet.pair F tail ∧
    ∃ B f, tail = ZFSet.pair B f ∧ j' = j ∧
      j ∈ env J ∧ e ∈ env E ∧ names ∈ env Names ∧
      SynchronizedEnumerationCode (env omega) (env N) B f e names) ↔ _
  constructor
  · rintro ⟨j, pair, eq, e, names, rfl, j', certificate, stored,
      F, tail, rfl, B, f, rfl, rfl, hj, he, hn, code⟩
    exact ⟨j', hj, e, he, names, hn, eq, F, B, f, stored, code⟩
  · rintro ⟨j, hj, e, he, names, hn, eq, F, B, f, stored, code⟩
    exact ⟨j, _, eq, e, names, rfl, j, _, stored, F, _, rfl,
      B, f, rfl, rfl, hj, he, hn, code⟩

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

def PreparedCertificateCode (M : TransitiveGround.{u})
    (P order q nodes nodeOrder meet N visibility top omega z F B f e names : ZFSet.{u}) : Prop :=
  MeetFilterCode nodes nodeOrder meet F ∧
  CoinitialBelowCode nodeOrder F F B ∧ B.Nonempty ∧
  SynchronizedEnumerationCode omega N B f e names ∧
  (∀ v tau, ZFSet.pair v tau ∈ f →
    ZFSet.pair v tau ∈ visibilitySupportIncidence nodes N visibility top) ∧
  PreparationForcingCode M P order q nodes visibility z F f

namespace SetFormula

def preparedCertificateFormula {n}
    (P order q nodes nodeOrder meet N visibility top omega z F B f e names : Fin n) : SetFormula n :=
  .conj (BoundedFormula.meetFilterFormula nodes nodeOrder meet F).toFormula
    (.conj (BoundedFormula.coinitialBelowFormula nodeOrder F F B).toFormula
      (.conj (BoundedFormula.exMem B (.equal 0 0)).toFormula
        (.conj (BoundedFormula.synchronizedEnumerationFormula omega N B f e names).toFormula
          (.conj (allGraphFields f
            (BoundedFormula.visibilitySupportAt 1 0 nodes.succ.succ N.succ.succ
              visibility.succ.succ top.succ.succ).toFormula)
            (preparationForcingFormula P order q nodes visibility z F f)))))

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_preparedCertificateFormula {n}
    (P order q nodes nodeOrder meet N visibility top omega z F B f e names : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meetCode : MeetOrderCode (env nodes) (env nodeOrder) (env meet)) :
    Realize M.sets
      (preparedCertificateFormula P order q nodes nodeOrder meet N visibility top omega z F B f e names) env ↔
      PreparedCertificateCode M (env P) (env order) (env q) (env nodes) (env nodeOrder)
        (env meet) (env N) (env visibility) (env top) (env omega) (env z)
        (env F) (env B) (env f) (env e) (env names) := by
  have nonempty : Realize M.sets (BoundedFormula.exMem B (.equal 0 0)).toFormula env ↔
      (env B).Nonempty := by
    rw [BoundedFormula.realize_toFormula M _ env members, BoundedFormula.truth_exMem]
    simp only [BoundedFormula.Truth, and_true]
    rfl
  have supported : Realize M.sets (allGraphFields f
      (BoundedFormula.visibilitySupportAt 1 0 nodes.succ.succ N.succ.succ
        visibility.succ.succ top.succ.succ).toFormula) env ↔
      ∀ v tau, ZFSet.pair v tau ∈ env f →
        ZFSet.pair v tau ∈ visibilitySupportIncidence (env nodes) (env N) (env visibility) (env top) := by
    rw [M.realize_allGraphFields _ _ env members]
    constructor
    · intro holds v tau entry
      have pairGround := M.transitive (members f) entry
      exact (BoundedFormula.truth_visibilitySupportAt _ _ _ _ _ _ _).1
        ((BoundedFormula.realize_toFormula M _ _
          (Fin.cases (M.pair_right pairGround) (Fin.cases (M.pair_left pairGround) members))).1
            (holds v tau entry))
    · intro holds v tau entry
      have pairGround := M.transitive (members f) entry
      exact (BoundedFormula.realize_toFormula M _ _
        (Fin.cases (M.pair_right pairGround) (Fin.cases (M.pair_left pairGround) members))).2
          ((BoundedFormula.truth_visibilitySupportAt _ _ _ _ _ _ _).2 (holds v tau entry))
  simp only [preparedCertificateFormula, Realize]
  rw [BoundedFormula.realize_meetFilterFormula M _ _ _ _ env members meetCode,
    BoundedFormula.realize_coinitialBelowFormula M _ _ _ _ env members,
    nonempty, BoundedFormula.realize_toFormula M _ env members,
    BoundedFormula.truth_synchronizedEnumerationFormula, supported,
    M.realize_preparationForcingFormula _ _ _ _ _ _ _ _ env members]
  rfl

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
