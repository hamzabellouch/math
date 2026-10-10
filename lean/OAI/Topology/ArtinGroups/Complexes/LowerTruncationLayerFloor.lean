import Mathlib
import OAI.Topology.ArtinGroups.Complexes.LevelArrayComplexMinimal
import OAI.Topology.ArtinGroups.Complexes.TotalVectorLayer

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma classLowerTruncation_eq_layer_of_floor (x:FiniteHomotopyClass Q (K:=K))
    (q:ℤ) (hx:ClassLowerBound Q q x) :
    classLowerTruncation Q q x=classLayer Q q x := by
  have hp:=classLayer_eq_self_of_bounds Q (classLowerTruncation Q q x) q
    (classLowerTruncation_floor Q q q x hx) (classLowerTruncation_cap Q q x)
  have hl:=classLayer_lowerTruncation Q (minimalClassModel Q x).complex
    (minimalClassModel_minimal Q x) q
  have hxx:classOfComplex Q (minimalClassModel Q x).complex=x:=minimalClassModel_class Q x
  rw [hxx] at hl
  exact hp.symm.trans hl

omit [Fintype V] [DecidableEq A] in
theorem classSignedVector_two_levels (x:FiniteHomotopyClass Q (K:=K))
    (q:ℤ) (hl:ClassLowerBound Q q x) (hh:ClassUpperBound Q (q+1) x) :
    classSignedVector Q x=cochainSign (K:=ℝ) q •
      (classTotalVector Q (classLayer Q q x)-classTotalVector Q (classLayer Q (q+1) x)) := by
  rw [classSignedVector_upper_partition Q x (q+1) hh]
  rw [show q+1-1=q by omega,classLowerTruncation_eq_layer_of_floor Q x q hl]
  rw [classSignedVector_pure Q _ q (classLayer_lowerBound Q x q) (classLayer_upperBound Q x q),
    classSignedVector_pure Q _ (q+1) (classLayer_lowerBound Q x (q+1)) (classLayer_upperBound Q x (q+1)),
    cochainSign_add_one,neg_smul,smul_sub,sub_eq_add_neg]

lemma classPacketPerm_upper_add_one {P:Type u} [Fintype P] [DecidableEq P]
    (hn:∀ a,Q.source a≠Q.target a) (v:P→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K:=K)) {q:ℤ} (hx:ClassUpperBound Q q x) :
    ClassUpperBound Q (q+1) (classPacketPerm Q hn v hv x) := by
  rw [← minimalClassModel_class Q x,classPacketPerm_apply]
  apply classUpperBound_of_representative Q
  intro i
  rcases i with ⟨b,i⟩|i
  · change ((minimalClassModel Q x).complex.placement i.1).cochain-1+
      (((minimalClassModel Q x).complex.placement i.1).internal+Path.length i.2.val)≤q+1
    have hi:=hx i.1
    have hl:Path.length i.2.val≤2:=by rcases Path.length_cases i.2.val with h|h|h <;> omega
    dsimp only [GeneratorPlacement.level] at hi
    omega
  · change ((minimalClassModel Q x).complex.placement i).level≤q+1
    have hi:=hx i
    omega

omit [Fintype V] [DecidableEq A] in
lemma classTotalVector_layer_nonneg (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) (α:V) :
    0≤classTotalVector Q (classLayer Q q x) α := by
  rw [classTotalVector_layer_apply]
  exact Nat.cast_nonneg _

omit [Fintype V] [DecidableEq A] in
lemma classUpperBound_of_upper_layer_zero (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hh:ClassUpperBound Q (q+1) x)
    (hz:classTotalVector Q (classLayer Q (q+1) x)=0) : ClassUpperBound Q q x := by
  intro i
  have hi:=hh i
  by_contra hn
  have he:((minimalClassModel Q x).complex.placement i).level=q+1 := by omega
  have hc:=congrFun hz ((minimalClassModel Q x).complex.placement i).color
  rw [classTotalVector_layer_apply] at hc
  have hc0:classLevelArray Q x (((minimalClassModel Q x).complex.placement i).color,q+1)=0 :=
    by simpa only [Nat.cast_eq_zero,Pi.zero_apply] using hc
  have harr:classLevelArray Q x=(minimalClassModel Q x).complex.levelArray Q := by
    have hmodel : classOfComplex Q (minimalClassModel Q x).complex=x := minimalClassModel_class Q x
    exact (congrArg (classLevelArray Q) hmodel).symm.trans
      (classLevelArray_complex_minimal Q (minimalClassModel Q x).complex (minimalClassModel_minimal Q x))
  rw [harr] at hc0
  rw [levelArray_apply,Nat.card_eq_fintype_card] at hc0
  have hp:0<Fintype.card {j : (minimalClassModel Q x).Index //
      ((minimalClassModel Q x).complex.placement j).color=((minimalClassModel Q x).complex.placement i).color ∧
      ((minimalClassModel Q x).complex.placement j).level=q+1} :=
    Fintype.card_pos_iff.mpr ⟨⟨i,rfl,he⟩⟩
  rw [hc0] at hp
  exact Nat.lt_irrefl _ hp

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
