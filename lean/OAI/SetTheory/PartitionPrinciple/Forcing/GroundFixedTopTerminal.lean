import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundChronologyFieldAppend

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundChronologicalHistory
variable {M : TransitiveGround.{u}} {s C D rD : ZFSet.{u}}
variable (history : GroundChronologicalHistory M (insert s s) C D rD)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (ordinal : ordinalSetProperty s) (hs : s ∈ M.sets)
variable (earlier : ∀ x t, ZFSet.pair x t ∈ history.birth s → t ∈ s)
variable (newHeight : ZFSet.{u}) (hHeight : newHeight ∈ M.sets)
variable (heightCode : StrictLexHeightCode (fixedTopCarrier (history.space s)) C D
  (fixedTopOrder (history.space s) (history.order s)) newHeight rD)

local notation "time" => s
local notation "times" => (insert s s)
local notation "P" => history.space s
local notation "r" => history.order s
local notation "μ" => history.meetGraph s
local notation "born" => history.birth s
local notation "space'" => appendHistoryValue time history.space (fixedTopCarrier P)
local notation "order'" => appendHistoryValue time history.order (fixedTopOrder P r)
local notation "meet'" => appendHistoryValue time history.meetGraph (fixedTopMeet P r)
local notation "birth'" => appendHistoryValue time history.birth (fixedTopBirth P born s)
local notation "height'" => appendHistoryValue time history.height newHeight

noncomputable def replaceTerminalFixedTop : GroundChronologicalHistory M times C D rD := by
  classical
  have terminal : s ∈ times := ZFSet.mem_insert_iff.2 (Or.inl rfl)
  have hP := history.space_mem s terminal
  have hr := history.order_mem s terminal
  have meet := history.meet_order s terminal
  have function := history.birth_function s terminal
  have inside : ∀ t ∈ times, ∀ z ∈ t, z ∈ s := by
    intro t ht z hz
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · exact hz
    · exact ordinal.1 t ht z hz
  have sourceSpace : ∀ t ∈ times, ∀ z ∈ t, history.space z = space' z :=
    fun t ht z hz => (appendHistoryValue_old (inside t ht z hz) _ _).symm
  have sourceOrder : ∀ t ∈ times, ∀ z ∈ t, history.order z = order' z :=
    fun t ht z hz => (appendHistoryValue_old (inside t ht z hz) _ _).symm
  have sourceMeet : ∀ t ∈ times, ∀ z ∈ t, history.meetGraph z = meet' z :=
    fun t ht z hz => (appendHistoryValue_old (inside t ht z hz) _ _).symm
  refine {
    space := space', order := order', meetGraph := meet', birth := birth', height := height'
    space_mem := ?_, order_mem := ?_, meet_mem := ?_, birth_mem := ?_, height_mem := ?_
    meet_order := ?_, birth_function := ?_, birth_bound := ?_, old_meet := ?_
    strict_height := ?_, layer := ?_ }
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using M.fixedTopCarrier_mem pairing unions hP
    · simpa only [appendHistoryValue_old ht] using history.space_mem t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using M.fixedTopOrder_mem pairing unions powers separation hP hr
    · simpa only [appendHistoryValue_old ht] using history.order_mem t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using M.fixedTopMeet_mem pairing unions powers separation hP hr
    · simpa only [appendHistoryValue_old ht] using history.meet_mem t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using
        M.fixedTopBirth_mem pairing unions hP (history.birth_mem _ terminal) hs
    · simpa only [appendHistoryValue_old ht] using history.birth_mem t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using hHeight
    · simpa only [appendHistoryValue_old ht] using history.height_mem t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using fixedTopMeet_code meet
    · simpa only [appendHistoryValue_old ht] using history.meet_order t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using fixedTopBirth_function function terminal
    · simpa only [appendHistoryValue_old ht] using
        history.birth_function t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simp only [appendHistoryValue_at]
      exact fun x _ a entry => fixedTopBirth_bound earlier x a entry
    · simpa only [appendHistoryValue_old ht] using
        history.birth_bound t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using
        fixedTopBirth_oldMeet meet function earlier (history.old_meet _ terminal)
    · simpa only [appendHistoryValue_old ht] using history.old_meet t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using heightCode
    · simpa only [appendHistoryValue_old ht] using history.strict_height t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro cutoff hc t ht bound
    by_cases equal : cutoff = s
    · subst cutoff
      simp only [appendHistoryValue_at]
      have layer := M.fixedTopBirth_layers pairing separation hP meet function earlier
        (fun a ha => history.layer s terminal a (ZFSet.mem_insert_iff.2 (Or.inr ha)) (Or.inr ha))
        t bound
      exact layer.congr_sources_below (sourceSpace t ht) (sourceOrder t ht) (sourceMeet t ht)
    · have hc := (ZFSet.mem_insert_iff.1 hc).resolve_left equal
      simpa only [appendHistoryValue_old hc] using
        (history.layer cutoff (ZFSet.mem_insert_iff.2 (Or.inr hc)) t ht bound).congr_sources_below
          (sourceSpace t ht) (sourceOrder t ht) (sourceMeet t ht)

local notation "extended" => history.replaceTerminalFixedTop pairing unions powers separation ordinal hs earlier newHeight hHeight heightCode

theorem replaceTerminalFixedTop_old {t : ZFSet.{u}} (ht : t ∈ time) :
    (extended).space t = history.space t ∧ (extended).order t = history.order t ∧
      (extended).meetGraph t = history.meetGraph t ∧ (extended).birth t = history.birth t ∧
      (extended).height t = history.height t := by
  exact ⟨appendHistoryValue_old ht _ _, appendHistoryValue_old ht _ _, appendHistoryValue_old ht _ _,
    appendHistoryValue_old ht _ _, appendHistoryValue_old ht _ _⟩

theorem replaceTerminalFixedTop_terminal :
    (extended).space time = fixedTopCarrier P ∧ (extended).order time = fixedTopOrder P r ∧
      (extended).meetGraph time = fixedTopMeet P r ∧ (extended).birth time = fixedTopBirth P born s ∧
      (extended).height time = newHeight := by
  exact ⟨appendHistoryValue_at _ _ _, appendHistoryValue_at _ _ _, appendHistoryValue_at _ _ _,
    appendHistoryValue_at _ _ _, appendHistoryValue_at _ _ _⟩

end GroundChronologicalHistory
end PartitionPilot.Forcing

end

end OAI
