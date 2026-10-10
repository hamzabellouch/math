import Mathlib
import OAI.Topology.ArtinGroups.Complexes.GeneratorVector
import OAI.Topology.ArtinGroups.Coxeter.PositiveBraidRel
import OAI.Topology.ArtinGroups.Harmonic.RowReflect
import OAI.Topology.ArtinGroups.Complexes.PlacementSignedWeight

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma cochainSign_sub_one (n : ℤ) : cochainSign (K:=ℝ) (n-1)= -cochainSign n := by
  have h:=cochainSign_add_one (K:=ℝ) (n-1)
  rw [sub_add_cancel] at h
  linarith

lemma cochainSign_sub_two (n : ℤ) : cochainSign (K:=ℝ) (n-2)=cochainSign n := by
  rw [show n-2=(n-1)-1 by omega,cochainSign_sub_one,cochainSign_sub_one,neg_neg]

omit [DecidableEq A] in
lemma signedCorner_sum (α β : V) :
    (∑ p : Zigzag.CornerPath Q α β, cochainSign (K:=ℝ) (Path.length p.val))=
      unfoldedCartan Q α β := by
  have hs := Finset.sum_subtype (p:=fun p : Path V A => Path.source Q p=α ∧ Path.target Q p=β) (F:=inferInstance)
    ((Finset.univ : Finset (Path V A)).filter (fun p => Path.source Q p=α ∧ Path.target Q p=β))
    (by intro p; simp) (fun p => cochainSign (K:=ℝ) (Path.length p))
  rw [← hs,Finset.sum_filter]
  simp only [Fintype.sum_sum_type,Path.source,Path.target,Path.length]
  simp [cochainSign,unfoldedCartan,Nat.card_eq_fintype_card,Fintype.card_subtype,
    ← Finset.sum_boole,eq_comm]
  have hv : (∑ x : V, if α=x ∧ β=x then (1:ℝ) else 0)=if α=β then 1 else 0 := by
    simp [ite_and, eq_comm]
  have ha : (∑ x : A, if α=Q.source x ∧ β=Q.target x then (-1:ℝ) else 0)=
      -(∑ x : A, if α=Q.source x ∧ β=Q.target x then (1:ℝ) else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> ring
  rw [hv,ha]
  split_ifs <;> ring

omit [DecidableEq A] in
lemma signedGeneratorVector_mulVec {I : Type u} [Fintype I]
    (E : BasedComplex Q (K:=K) I) (α : V) :
    (unfoldedCartan Q *ᵥ signedGeneratorVector Q E) α=
      ∑ i, cochainSign (K:=ℝ) (E.placement i).level * unfoldedCartan Q α (E.placement i).color := by
  simp only [Matrix.mulVec,dotProduct,signedGeneratorVector,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [placementSignedWeight,mul_comm]

lemma signedGeneratorVector_test {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K:=K) I) (α β : V) :
    signedGeneratorVector Q (E.testComplex Q α) β=
      if α=β then (unfoldedCartan Q *ᵥ signedGeneratorVector Q E) α else 0 := by
  by_cases h : α=β
  · subst β
    rw [ite_eq_left rfl,signedGeneratorVector_mulVec]
    change (∑ t : TestIndex Q E.placement α,
      if α=α then cochainSign (K:=ℝ) ((E.placement t.1).cochain+
        ((E.placement t.1).internal+Path.length t.2.val)) else 0)=_
    simp only [ite_true,Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    have hlev (p : Zigzag.CornerPath Q α (E.placement i).color) :
        (E.placement i).cochain+((E.placement i).internal+Path.length p.val)=
          (E.placement i).level+Path.length p.val := by
      simp only [GeneratorPlacement.level]; ring
    simp_rw [hlev,cochainSign_add]
    rw [← Finset.mul_sum,signedCorner_sum]

  · simp [signedGeneratorVector,placementSignedWeight,testComplex,testPlacement,h]

omit [Fintype V] in
lemma placementSignedWeight_lower (a : GeneratorPlacement V) (v : V) :
    placementSignedWeight ⟨a.color,a.cochain-1,a.internal⟩ v= -placementSignedWeight a v := by
  have hh : a.cochain-1+a.internal=a.level-1 := by dsimp [GeneratorPlacement.level]; omega
  simp only [placementSignedWeight,GeneratorPlacement.level,hh,cochainSign_sub_one]
  split_ifs <;> simp

omit [DecidableEq A] [Fintype V] in
lemma Map.signedGeneratorVector_cone {I J : Type u} [Fintype I] [Fintype J]
    {E : BasedComplex Q (K:=K) I} {F : BasedComplex Q (K:=K) J} (f : Map Q E F) :
    signedGeneratorVector Q (f.cone Q)=signedGeneratorVector Q F-signedGeneratorVector Q E := by
  funext v
  simp only [signedGeneratorVector,Map.cone,Map.conePlacement,Fintype.sum_sum_type,
    placementSignedWeight_lower,Finset.sum_neg_distrib,Pi.sub_apply]
  ring

theorem signedGeneratorVector_positiveTwist {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K:=K) I) (α : V) :
    signedGeneratorVector Q (E.positiveTwist Q α)=rowReflect (unfoldedCartan Q) α
      (signedGeneratorVector Q E) := by
  unfold positiveTwist
  rw [Map.signedGeneratorVector_cone]
  funext β
  simp only [Pi.sub_apply,signedGeneratorVector_test,rowReflect,Pi.smul_apply,smul_eq_mul,
    Pi.single_apply]
  by_cases h : α=β
  · subst β; simp
  · simp [h,Ne.symm h]

lemma classSignedVector_positiveTwist (x : FiniteHomotopyClass Q (K:=K)) (α : V) :
    classSignedVector Q (classPositiveTwist Q α x)=
      rowReflect (unfoldedCartan Q) α (classSignedVector Q x) := by
  induction x using Quotient.inductionOn with | _ E =>
    exact signedGeneratorVector_positiveTwist Q E.complex α

omit [Fintype V] in
lemma placementSignedWeight_raise (a : GeneratorPlacement V) (v : V) :
    placementSignedWeight ⟨a.color,a.cochain+1,a.internal⟩ v= -placementSignedWeight a v := by
  have hh : a.cochain+1+a.internal=a.level+1 := by dsimp [GeneratorPlacement.level]; omega
  simp only [placementSignedWeight,GeneratorPlacement.level,hh,cochainSign_add_one]
  split_ifs <;> simp

omit [DecidableEq A] [Fintype V] in
lemma Map.signedGeneratorVector_cocone {I J : Type u} [Fintype I] [Fintype J]
    {E : BasedComplex Q (K:=K) I} {F : BasedComplex Q (K:=K) J} (f : Map Q E F) :
    signedGeneratorVector Q (f.cocone Q)=signedGeneratorVector Q E-signedGeneratorVector Q F := by
  funext v
  simp only [signedGeneratorVector,Map.cocone,Map.coconePlacement,Fintype.sum_sum_type,
    placementSignedWeight_raise,Finset.sum_neg_distrib,Pi.sub_apply]
  ring

lemma signedGeneratorVector_cotest {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K:=K) I) (α : V) :
    signedGeneratorVector Q (E.cotestComplex Q α)=signedGeneratorVector Q (E.testComplex Q α) := by
  funext β
  apply Finset.sum_congr rfl
  intro t _
  change (if α=β then cochainSign (K:=ℝ) ((E.placement t.1).cochain+
    ((E.placement t.1).internal+Path.length t.2.val-2)) else 0)=
    (if α=β then cochainSign (K:=ℝ) ((E.placement t.1).cochain+
    ((E.placement t.1).internal+Path.length t.2.val)) else 0)
  rw [← add_sub_assoc,cochainSign_sub_two]

theorem signedGeneratorVector_negativeTwist {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K:=K) I) (α : V) :
    signedGeneratorVector Q (E.negativeTwist Q α)=rowReflect (unfoldedCartan Q) α
      (signedGeneratorVector Q E) := by
  unfold negativeTwist
  rw [Map.signedGeneratorVector_cocone,signedGeneratorVector_cotest]
  funext β
  simp only [Pi.sub_apply,signedGeneratorVector_test,rowReflect,Pi.smul_apply,smul_eq_mul,
    Pi.single_apply]
  by_cases h : α=β
  · subst β; simp
  · simp [h,Ne.symm h]

lemma classSignedVector_negativeTwist (x : FiniteHomotopyClass Q (K:=K)) (α : V) :
    classSignedVector Q (classNegativeTwist Q α x)=
      rowReflect (unfoldedCartan Q) α (classSignedVector Q x) := by
  induction x using Quotient.inductionOn with | _ E =>
    exact signedGeneratorVector_negativeTwist Q E.complex α

lemma classSignedVector_positiveWord (w : List V) (x : FiniteHomotopyClass Q (K:=K)) :
    classSignedVector Q (positiveWordAction Q w x)=
      rowReflectWord (unfoldedCartan Q) w (classSignedVector Q x) := by
  induction w with
  | nil => rfl
  | cons α w ih =>
    change classSignedVector Q (classPositiveTwist Q α (positiveWordAction Q w x))=_
    rw [classSignedVector_positiveTwist,ih]
    rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
