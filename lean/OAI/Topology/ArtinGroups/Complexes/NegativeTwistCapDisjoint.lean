import Mathlib
import OAI.Topology.ArtinGroups.Complexes.HighestLocalGeneratorTest

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u v
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma classNegativeTwist_capOn_disjoint (x : FiniteHomotopyClass Q (K:=K))
    (U:Set V) (q:ℤ) (hcap:ClassCapOn Q x U q) (α:V) (hα:α∉U) :
    ClassCapOn Q (classNegativeTwist Q α x) U q := by
  let E:=minimalClassModel Q x
  let F:=E.complex.negativeTwist Q α
  have hx:classOfComplex Q F=classNegativeTwist Q α x := by
    change classNegativeTwist Q α (classOfComplex Q E.complex)=_
    exact congrArg (classNegativeTwist Q α) (minimalClassModel_class Q x)
  rw [← hx]
  apply minimal_bound_transport Q F _ (minimalClassModel_minimal Q _)
    ((minimalClassModelEquivalence Q F).symm Q) (fun p=>p.color∈U→p.level≤q)
  intro i hi
  rcases i with j|j
  · exact hcap j hi
  · exact (hα hi).elim

lemma inverseWord_capOn_disjoint (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (q:ℤ) (hcap:ClassCapOn Q x U q) (hw:∀ α∈w,α∉U) :
    ClassCapOn Q (inverseWordAction Q w x) U q := by
  induction w generalizing x with
  | nil => exact hcap
  | cons α w ih =>
    exact ih _ (classNegativeTwist_capOn_disjoint Q x U q hcap α (hw α (by simp)))
      (fun β hβ=>hw β (by simp [hβ]))

omit [Fintype V] [DecidableEq A] in
lemma finiteFamily_upperBound {F:Type*} [Finite F]
    (x:F→FiniteHomotopyClass Q (K:=K)) : ∃ d:ℤ,∀ f,ClassUpperBound Q d (x f) := by
  obtain ⟨d,hd⟩:=Finite.exists_le
    (fun z : Σ f:F,(minimalClassModel Q (x f)).Index =>
      ((minimalClassModel Q (x z.1)).complex.placement z.2).level)
  exact ⟨d,fun f i=>hd ⟨f,i⟩⟩

lemma ClassTestUpper.mono {x:FiniteHomotopyClass Q (K:=K)} {U:Set V} {s t:ℤ}
    (h:ClassTestUpper Q x U s) (hst:s≤t) : ClassTestUpper Q x U t :=
  fun α hα l hl c=>h α hα l (lt_of_le_of_lt hst hl) c

variable (hn:∀ a,Q.source a≠Q.target a)

lemma inverseWord_iterate_testUpper (w:List V) (U:Set V)
    (hw:∀ (x:FiniteHomotopyClass Q (K:=K)) (t:ℤ),ClassTestUpper Q x U t →
      ClassTestUpper Q (inverseWordAction Q w x) U (t-1))
    (x:FiniteHomotopyClass Q (K:=K)) (t:ℤ) (hx:ClassTestUpper Q x U t) (n:ℕ) :
    ClassTestUpper Q ((inverseWordAction Q w)^[n] x) U (t-(n:ℤ)) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    convert hw _ _ ih using 1
    push_cast
    ring

lemma inverseWord_iterate_boundary (w:List V) (U:Set V) (hw:∀ α∈w,α∈U)
    (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hb:ClassCapOn Q x (Q.closedNeighborhood U \ U) q) (n:ℕ) :
    ClassCapOn Q ((inverseWordAction Q w)^[n] x) (Q.closedNeighborhood U \ U) q := by
  induction n with
  | zero => exact hb
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact inverseWord_capOn_disjoint Q w _ _ q ih (fun α hα h=>h.2 (hw α hα))

theorem finiteFamily_cap_accessible_of_test_decrement {F:Type*} [Finite F]
    (w:List V) (U:Set V) (hw:∀ α∈w,α∈U)
    (hdec:∀ (x:FiniteHomotopyClass Q (K:=K)) (t:ℤ),ClassTestUpper Q x U t →
      ClassTestUpper Q (inverseWordAction Q w x) U (t-1))
    (x:F→FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hb:∀ f,ClassCapOn Q (x f) (Q.closedNeighborhood U \ U) q) :
    ∃ n:ℕ,∀ f,ClassCapOn Q ((inverseWordAction Q w)^[n] (x f)) (Q.closedNeighborhood U) q := by
  obtain ⟨d,hd⟩:=finiteFamily_upperBound Q x
  let n:ℕ:=(d-q).toNat
  have hn:(d:ℤ)-q≤(n:ℤ) := by dsimp [n]; omega
  refine ⟨n,fun f=>?_⟩
  have hbd:=inverseWord_iterate_boundary Q w U hw (x f) q (hb f) n
  have ht:=inverseWord_iterate_testUpper Q w U hdec (x f) (d+2)
    (classTestUpper_of_generator_cap Q (x f) d (hd f) U) n
  have hcu:=classCapOn_of_test_and_boundary Q _ U q (ht.mono Q (by omega)) hbd
  intro i hi
  by_cases hui:((minimalClassModel Q ((inverseWordAction Q w)^[n] (x f))).complex.placement i).color∈U
  · exact hcu i hui
  · exact hbd i ⟨hi,hui⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
