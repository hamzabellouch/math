import OAI.SetTheory.PartitionPrinciple.Geometry.GroundFinalInsertionExceptions

namespace OAI

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def codedInsertionProfileFormula {n} (L r μ c E K F : Fin n) : BoundedFormula n :=
  .allMem L (imp (pairMembershipFormula E.succ 0 r.succ)
    (.conj
      (imp (.exMem F.succ (pairMembershipFormula 0 1 r.succ.succ))
        (pairMembershipFormula K.succ 0 r.succ))
      (imp (.neg (.exMem F.succ (pairMembershipFormula 0 1 r.succ.succ)))
        (tripleMembershipFormula K.succ 0 c.succ μ.succ))))

theorem truth_codedInsertionProfileFormula {n} (L r μ c E K F : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (codedInsertionProfileFormula L r μ c E K F) env ↔
      CodedInsertionProfile (env L) (env r) (env μ) (env c) (env E) (env K) (env F) := by
  simp only [codedInsertionProfileFormula, Truth, truth_imp, truth_exMem,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

def codedCapProfileFormula {n} (L r μ c E K F : Fin n) : BoundedFormula n :=
  .conj (.mem c L) (.conj (.mem E L) (.conj (.mem K L)
    (.conj (subsetFormula F L) (.conj (.exMem F (.equal 0 0))
      (.conj (codedInsertionProfileFormula L r μ c E K F)
        (.conj (pairMembershipFormula c K r)
          (.conj (.neg (pairMembershipFormula K c r)) (.neg (pairMembershipFormula E K r)))))))))

theorem truth_codedCapProfileFormula {n} (L r μ c E K F : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (codedCapProfileFormula L r μ c E K F) env ↔
      CodedCapProfile (env L) (env r) (env μ) (env c) (env E) (env K) (env F) := by
  simp only [codedCapProfileFormula, Truth, truth_subsetFormula, truth_exMem,
    truth_codedInsertionProfileFormula, truth_pairMembershipFormula, and_true]
  constructor
  · rintro ⟨hc, hE, hK, subset, nonempty, profile, lower, strict, separated⟩
    exact ⟨hc, hE, hK, subset, nonempty, profile, lower, strict, separated⟩
  · intro code
    exact ⟨code.target_mem, code.separator_mem, code.cap_mem, code.filter_subset,
      code.nonempty, code.profile, code.target_below_cap, code.cap_not_below_target,
      code.separator_not_below_cap⟩

def imageProfilePositiveFormula {n} (F Q e R x : Fin n) : BoundedFormula n :=
  .exMem Q (.conj (.exMem F.succ (pairMembershipFormula 0 1 e.succ.succ))
    (pairMembershipFormula 0 x.succ R.succ))

theorem truth_imageProfilePositiveFormula {n} (F Q e R x : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (imageProfilePositiveFormula F Q e R x) env ↔
      ∃ f ∈ relationImage (env F) (env Q) (env e), ZFSet.pair f (env x) ∈ env R := by
  simp only [imageProfilePositiveFormula, truth_exMem, Truth, truth_pairMembershipFormula]
  constructor
  · rintro ⟨y, hy, ⟨f, hf, entry⟩, lower⟩
    exact ⟨y, (mem_relationImage _ _ _ _).2 ⟨hy, f, hf, entry⟩, lower⟩
  · rintro ⟨y, hy, lower⟩
    obtain ⟨hy, f, hf, entry⟩ := (mem_relationImage _ _ _ _).1 hy
    exact ⟨y, hy, ⟨f, hf, entry⟩, lower⟩

def imageInsertionProfileFormula {n} (Q R ν c E K F e : Fin n) : BoundedFormula n :=
  .allMem Q (imp (pairMembershipFormula E.succ 0 R.succ)
    (.conj
      (imp (imageProfilePositiveFormula F.succ Q.succ e.succ R.succ 0)
        (pairMembershipFormula K.succ 0 R.succ))
      (imp (.neg (imageProfilePositiveFormula F.succ Q.succ e.succ R.succ 0))
        (tripleMembershipFormula K.succ 0 c.succ ν.succ))))

theorem truth_imageInsertionProfileFormula {n} (Q R ν c E K F e : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (imageInsertionProfileFormula Q R ν c E K F e) env ↔
      CodedInsertionProfile (env Q) (env R) (env ν) (env c) (env E) (env K)
        (relationImage (env F) (env Q) (env e)) := by
  simp only [imageInsertionProfileFormula, Truth, truth_imp, truth_imageProfilePositiveFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

def imageCapProfileFormula {n} (Q R ν c E K F e : Fin n) : BoundedFormula n :=
  .conj (.mem c Q) (.conj (.mem E Q) (.conj (.mem K Q)
    (.conj (.exMem Q (.exMem F.succ (pairMembershipFormula 0 1 e.succ.succ)))
      (.conj (imageInsertionProfileFormula Q R ν c E K F e)
        (.conj (pairMembershipFormula c K R)
          (.conj (.neg (pairMembershipFormula K c R)) (.neg (pairMembershipFormula E K R))))))))

theorem truth_imageCapProfileFormula {n} (Q R ν c E K F e : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (imageCapProfileFormula Q R ν c E K F e) env ↔
      CodedCapProfile (env Q) (env R) (env ν) (env c) (env E) (env K)
        (relationImage (env F) (env Q) (env e)) := by
  simp only [imageCapProfileFormula, Truth, truth_exMem, truth_pairMembershipFormula,
    truth_imageInsertionProfileFormula]
  constructor
  · rintro ⟨hc, hE, hK, ⟨y, hy, f, hf, entry⟩, profile, lower, strict, separated⟩
    exact ⟨hc, hE, hK, fun _ h => ((mem_relationImage _ _ _ _).1 h).1,
      ⟨y, (mem_relationImage _ _ _ _).2 ⟨hy, f, hf, entry⟩⟩,
      profile, lower, strict, separated⟩
  · intro code
    obtain ⟨y, hy⟩ := code.nonempty
    obtain ⟨hy, f, hf, entry⟩ := (mem_relationImage _ _ _ _).1 hy
    exact ⟨code.target_mem, code.separator_mem, code.cap_mem, ⟨y, hy, f, hf, entry⟩,
      code.profile, code.target_below_cap, code.cap_not_below_target,
      code.separator_not_below_cap⟩

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing
universe u

def OldProfilePreservationCode (P r μ Q R ν e Filters : ZFSet.{u}) : Prop :=
  ∀ F ∈ Filters, ∀ c ∈ P, ∀ E ∈ P, ∀ K ∈ P,
    CodedCapProfile P r μ c E K F →
    ∀ c' ∈ Q, ∀ E' ∈ Q, ∀ K' ∈ Q,
      ZFSet.pair c c' ∈ e → ZFSet.pair E E' ∈ e → ZFSet.pair K K' ∈ e →
      CodedCapProfile Q R ν c' E' K' (relationImage F Q e)

namespace BoundedFormula
open SetFormula

def oldProfilePreservationFormula {n} (P r μ Q R ν e Filters : Fin n) : BoundedFormula n :=
  let lift (j : Fin n) := j.succ.succ.succ.succ.succ.succ.succ
  .allMem Filters (.allMem P.succ (.allMem P.succ.succ (.allMem P.succ.succ.succ
    (imp (codedCapProfileFormula P.succ.succ.succ.succ r.succ.succ.succ.succ
      μ.succ.succ.succ.succ 2 1 0 3)
      (.allMem Q.succ.succ.succ.succ (.allMem Q.succ.succ.succ.succ.succ
        (.allMem Q.succ.succ.succ.succ.succ.succ
          (imp (pairMembershipFormula 5 2 (lift e))
            (imp (pairMembershipFormula 4 1 (lift e))
              (imp (pairMembershipFormula 3 0 (lift e))
                (imageCapProfileFormula (lift Q) (lift R) (lift ν) 2 1 0 6 (lift e))))))))))))

theorem truth_oldProfilePreservationFormula {n} (P r μ Q R ν e Filters : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (oldProfilePreservationFormula P r μ Q R ν e Filters) env ↔
      OldProfilePreservationCode (env P) (env r) (env μ) (env Q) (env R) (env ν)
        (env e) (env Filters) := by
  simp only [oldProfilePreservationFormula, Truth, truth_imp, truth_codedCapProfileFormula,
    truth_imageCapProfileFormula, truth_pairMembershipFormula]
  rfl

theorem realize_oldProfilePreservationFormula (M : TransitiveGround.{u}) {n}
    (P r μ Q R ν e Filters : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (oldProfilePreservationFormula P r μ Q R ν e Filters).toFormula env ↔
      OldProfilePreservationCode (env P) (env r) (env μ) (env Q) (env R) (env ν)
        (env e) (env Filters) :=
  (realize_toFormula M _ env members).trans
    (truth_oldProfilePreservationFormula P r μ Q R ν e Filters env)

end BoundedFormula

theorem oldProfilePreservation_groundPower_iff (M : TransitiveGround.{u})
    (P r μ Q R ν e : ZFSet.{u}) :
    OldProfilePreservationCode P r μ Q R ν e (M.groundPower P) ↔
      ∀ F ∈ M.sets, ∀ c E K,
        CodedCapProfile P r μ c E K F →
        ∀ c' E' K', ZFSet.pair c c' ∈ e → ZFSet.pair E E' ∈ e → ZFSet.pair K K' ∈ e →
          c' ∈ Q → E' ∈ Q → K' ∈ Q →
          CodedCapProfile Q R ν c' E' K' (relationImage F Q e) := by
  constructor
  · intro code F hF c E K profile c' E' K' first second third hc' hE' hK'
    exact code F ((M.mem_groundPower P F).2 ⟨hF, profile.filter_subset⟩)
      c profile.target_mem E profile.separator_mem K profile.cap_mem profile
      c' hc' E' hE' K' hK' first second third
  · intro code F hF c _ E _ K _ profile c' hc' E' hE' K' hK' first second third
    exact code F ((M.mem_groundPower P F).1 hF).1 c E K profile
      c' E' K' first second third hc' hE' hK'

def TaskCapProfilesCode (I P Q R ν e Targets Separators Filters Families Caps : ZFSet.{u}) : Prop :=
  ∀ i ∈ I, ∀ c ∈ P, ∀ v ∈ P, ∀ F ∈ Families,
    ∀ K ∈ Q, ∀ c' ∈ Q, ∀ v' ∈ Q,
      ZFSet.pair i c ∈ Targets → ZFSet.pair i v ∈ Separators → ZFSet.pair i F ∈ Filters →
      ZFSet.pair i K ∈ Caps → ZFSet.pair c c' ∈ e → ZFSet.pair v v' ∈ e →
      CodedCapProfile Q R ν c' v' K (relationImage F Q e)

def CommonTargetCapMeetCode (I P Q ν e Targets Caps : ZFSet.{u}) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, ∀ c ∈ P, ∀ K ∈ Q, ∀ L ∈ Q, ∀ c' ∈ Q,
    i ≠ j → ZFSet.pair i c ∈ Targets → ZFSet.pair j c ∈ Targets →
    ZFSet.pair i K ∈ Caps → ZFSet.pair j L ∈ Caps → ZFSet.pair c c' ∈ e →
      ZFSet.pair (ZFSet.pair K L) c' ∈ ν

structure TaskCapFamilyCode (I P Q R ν e Targets Separators Filters Families Caps : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc I Q Caps
  profiles : TaskCapProfilesCode I P Q R ν e Targets Separators Filters Families Caps
  common_target : CommonTargetCapMeetCode I P Q ν e Targets Caps

namespace BoundedFormula

def taskCapProfilesFormula {n}
    (I P Q R ν e Targets Separators Filters Families Caps : Fin n) : BoundedFormula n :=
  let lift (j : Fin n) := j.succ.succ.succ.succ.succ.succ.succ
  .allMem I (.allMem P.succ (.allMem P.succ.succ (.allMem Families.succ.succ.succ
    (.allMem Q.succ.succ.succ.succ (.allMem Q.succ.succ.succ.succ.succ
      (.allMem Q.succ.succ.succ.succ.succ.succ
        (imp (pairMembershipFormula 6 5 (lift Targets))
          (imp (pairMembershipFormula 6 4 (lift Separators))
            (imp (pairMembershipFormula 6 3 (lift Filters))
              (imp (pairMembershipFormula 6 2 (lift Caps))
                (imp (pairMembershipFormula 5 1 (lift e))
                  (imp (pairMembershipFormula 4 0 (lift e))
                    (imageCapProfileFormula (lift Q) (lift R) (lift ν) 1 0 2 3 (lift e))))))))))))))

theorem truth_taskCapProfilesFormula {n}
    (I P Q R ν e Targets Separators Filters Families Caps : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (taskCapProfilesFormula I P Q R ν e Targets Separators Filters Families Caps) env ↔
      TaskCapProfilesCode (env I) (env P) (env Q) (env R) (env ν) (env e) (env Targets)
        (env Separators) (env Filters) (env Families) (env Caps) := by
  simp only [taskCapProfilesFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_imageCapProfileFormula]
  rfl

def commonTargetCapMeetFormula {n} (I P Q ν e Targets Caps : Fin n) : BoundedFormula n :=
  let lift (j : Fin n) := j.succ.succ.succ.succ.succ.succ
  .allMem I (.allMem I.succ (.allMem P.succ.succ (.allMem Q.succ.succ.succ
    (.allMem Q.succ.succ.succ.succ (.allMem Q.succ.succ.succ.succ.succ
      (imp (.neg (.equal 5 4))
        (imp (pairMembershipFormula 5 3 (lift Targets))
          (imp (pairMembershipFormula 4 3 (lift Targets))
            (imp (pairMembershipFormula 5 2 (lift Caps))
              (imp (pairMembershipFormula 4 1 (lift Caps))
                (imp (pairMembershipFormula 3 0 (lift e))
                  (tripleMembershipFormula 2 1 0 (lift ν)))))))))))))

theorem truth_commonTargetCapMeetFormula {n} (I P Q ν e Targets Caps : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (commonTargetCapMeetFormula I P Q ν e Targets Caps) env ↔
      CommonTargetCapMeetCode (env I) (env P) (env Q) (env ν) (env e) (env Targets) (env Caps) := by
  simp only [commonTargetCapMeetFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula]
  rfl

def taskCapFamilyFormula {n}
    (I P Q R ν e Targets Separators Filters Families Caps : Fin n) : BoundedFormula n :=
  .conj (functionFormula I Q Caps)
    (.conj (taskCapProfilesFormula I P Q R ν e Targets Separators Filters Families Caps)
      (commonTargetCapMeetFormula I P Q ν e Targets Caps))

theorem truth_taskCapFamilyFormula {n}
    (I P Q R ν e Targets Separators Filters Families Caps : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (taskCapFamilyFormula I P Q R ν e Targets Separators Filters Families Caps) env ↔
      TaskCapFamilyCode (env I) (env P) (env Q) (env R) (env ν) (env e) (env Targets)
        (env Separators) (env Filters) (env Families) (env Caps) := by
  simp only [taskCapFamilyFormula, Truth, truth_functionFormula, truth_taskCapProfilesFormula,
    truth_commonTargetCapMeetFormula]
  exact ⟨fun ⟨f, p, c⟩ => ⟨f, p, c⟩, fun code => ⟨code.function, code.profiles, code.common_target⟩⟩

theorem realize_taskCapFamilyFormula (M : TransitiveGround.{u}) {n}
    (I P Q R ν e Targets Separators Filters Families Caps : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    SetFormula.Realize M.sets
      (taskCapFamilyFormula I P Q R ν e Targets Separators Filters Families Caps).toFormula env ↔
      TaskCapFamilyCode (env I) (env P) (env Q) (env R) (env ν) (env e) (env Targets)
        (env Separators) (env Filters) (env Families) (env Caps) :=
  (realize_toFormula M _ env members).trans
    (truth_taskCapFamilyFormula I P Q R ν e Targets Separators Filters Families Caps env)

end BoundedFormula

end PartitionPilot.Forcing

end OAI
