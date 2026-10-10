import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PositiveTwistOtherTest2
import OAI.Topology.ArtinGroups.Complexes.ScalarSupportedTokenShift
import OAI.Topology.ArtinGroups.Complexes.PositiveTwistOtherTest3
import OAI.Topology.ArtinGroups.Complexes.GeneratorTokenTest
import OAI.Topology.ArtinGroups.Complexes.Test

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def TestUpperBound (E:BasedComplex Q (K:=K) I) (U:Set V) (t:ℤ) : Prop :=
  ∀ α∈U,∀ l:ℤ,t<l→∀ c:ℤ,ScalarExactAt Q (E.testComplex Q α) α l c

omit [DecidableEq I] in
lemma testUpperBound_mono (E:BasedComplex Q (K:=K) I) (U:Set V) {s t:ℤ}
    (hst:s≤t) (h:TestUpperBound Q E U s) : TestUpperBound Q E U t :=
  fun α hα l hl c=>h α hα l (lt_of_le_of_lt hst hl) c

lemma testUpperBound_transport (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (e:HomotopyEquivalence Q E F) (U:Set V) {t:ℤ} (h:TestUpperBound Q F U t) :
    TestUpperBound Q E U t := by
  intro α hα l hl c
  exact scalarExact_transport Q _ _ (e.test Q α) α (fun _=>rfl) (h α hα l hl c)

theorem positiveTwist_testUpperBound (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) (U:Set V) (α:V) (hα:α∈U) {t:ℤ}
    (h:TestUpperBound Q E U t) : TestUpperBound Q (E.positiveTwist Q α) U (t+1) := by
  intro β hβ l hl c
  by_cases he:β=α
  · subst β
    apply (positiveTwist_test_exact_iff Q hn E α l c).mpr
    exact h α hα (l-1) (by omega) (c+1)
  · exact positiveTwist_other_test_exact Q E α β he l c
      (h α hα l (by omega) (c+1)) (h β hβ l (by omega) c)

theorem positiveTwist_testUpperBound_reflect (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) (U:Set V) (α:V) (hα:α∈U) {t:ℤ}
    (h:TestUpperBound Q (E.positiveTwist Q α) U t) : TestUpperBound Q E U t := by
  have ha:∀ l:ℤ,t<l+1→∀ c:ℤ,ScalarExactAt Q (E.testComplex Q α) α l c := by
    intro l hl c
    have hh:=(positiveTwist_test_exact_iff Q hn E α (l+1) (c-1)).mp
      (h α hα (l+1) hl (c-1))
    simpa only [add_sub_cancel_right,sub_add_cancel] using hh
  intro β hβ l hl c
  by_cases he:β=α
  · subst β
    exact ha l (by omega) c
  · exact positiveTwist_other_test_exact_reflect Q E α β he l c
      (ha (l-1) (by omega) c) (h β hβ l hl c)

theorem positiveTwist_testUpperBound_iff (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) (U:Set V) (α:V) (hα:α∈U) {t:ℤ}
    (h:TestUpperBound Q E U t) :
    TestUpperBound Q (E.positiveTwist Q α) U t ↔
      ∀ c,ScalarExactAt Q (E.testComplex Q α) α t c := by
  constructor
  · intro hh c
    have hz:=(positiveTwist_test_exact_iff Q hn E α (t+1) (c-1)).mp
      (hh α hα (t+1) (by omega) (c-1))
    simpa only [add_sub_cancel_right,sub_add_cancel] using hz
  · intro hh β hβ l hl c
    by_cases he:β=α
    · subst β
      apply (positiveTwist_test_exact_iff Q hn E α l c).mpr
      by_cases he:l-1=t
      · rw [he]; exact hh (c+1)
      · exact h α hα (l-1) (by omega) (c+1)
    · exact positiveTwist_other_test_exact Q E α β he l c
        (h α hα l hl (c+1)) (h β hβ l hl c)

omit [DecidableEq I] in
theorem positiveTwist_other_testUpperBound
    (E:BasedComplex Q (K:=K) I) (U:Set V) (α:V) (hα:α∈U) {t:ℤ}
    (h:TestUpperBound Q E U t) (β:V) (hne:β≠α) (hβ:β∈U)
    (l:ℤ) (hl:t<l) (c:ℤ) :
    ScalarExactAt Q ((E.positiveTwist Q α).testComplex Q β) β l c :=
  positiveTwist_other_test_exact Q E α β hne l c
    (h α hα l hl (c+1)) (h β hβ l hl c)

omit [DecidableEq I] in
theorem generatorBound_of_test_and_outside
    (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (U:Set V) (d:ℤ)
    (h:TestUpperBound Q E U (d+2))
    (hout:∀ i,(E.placement i).color∉U→(E.placement i).level≤d) :
    ∀ i,(E.placement i).level≤d := by
  classical
  intro i
  by_contra hi
  obtain ⟨j,hj,hmax⟩:=Finset.exists_max_image (Finset.univ:Finset I)
    (fun j:I=>(E.placement j).level) ⟨i,Finset.mem_univ i⟩
  have hm:∀ k,(E.placement k).level≤(E.placement j).level:=
    fun k=>hmax k (Finset.mem_univ k)
  let F:=Finset.univ.filter (fun k:I=>(E.placement k).level=(E.placement j).level)
  have hjF:j∈F:=by simp [F]
  obtain ⟨k,hk,hmin⟩:=Finset.exists_min_image F (fun k:I=>(E.placement k).cochain) ⟨j,hjF⟩
  have hlev:(E.placement k).level=(E.placement j).level:= (Finset.mem_filter.mp hk).2
  have hkd:d<(E.placement k).level := by have hh:=hm i; omega
  have hku:(E.placement k).color∈U := by
    by_contra hn
    have hh:=hout k hn
    omega
  apply highest_generator_test_not_exact Q E hE k
    (fun z=>by rw [hlev]; exact hm z)
    (fun z hz=>hmin z (by simp [F,hz,hlev]))
  exact h (E.placement k).color hku ((E.placement k).level+2) (by omega)
    (E.placement k).cochain

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
