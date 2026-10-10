import Mathlib
import OAI.Topology.ArtinGroups.Quivers.Reduction
import OAI.Topology.ArtinGroups.Cancellation.ScalarPivot
import OAI.Topology.ArtinGroups.Cancellation.Retained

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

universe u
variable {V A K I J L : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]
  {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
  {G : BasedComplex Q (K := K) L}

namespace Map

noncomputable def identity (E : BasedComplex Q (K := K) I) : Map Q E E where
  matrix := projectiveIdentity Q E.placement
  entries := projectiveEntries_identity Q
  degree := mapDegree_identity Q
  commute := (mul_projectiveIdentity Q E.entries).trans (projectiveIdentity_mul Q E.entries).symm

omit [DecidableEq I] [DecidableEq J] [DecidableEq L] in
noncomputable def comp (f : Map Q E F) (g : Map Q F G) : Map Q E G where
  matrix := f.matrix * g.matrix
  entries := projectiveEntries_mul Q f.entries g.entries
  degree := mapDegree_mul Q f.degree g.degree
  commute := by
    rw [← Matrix.mul_assoc, f.commute, Matrix.mul_assoc, g.commute, Matrix.mul_assoc]

omit [DecidableEq I] [DecidableEq J] in
lemma conjugateBoundary (f : Map Q E F) (g : Map Q F E)
    (h : Matrix J J (Q.Zigzag K)) :
    f.matrix * (F.differential * h + h * F.differential) * g.matrix =
      E.differential * (f.matrix * h * g.matrix) +
        (f.matrix * h * g.matrix) * E.differential := by
  rw [Matrix.mul_add, Matrix.add_mul]
  congr 1
  · rw [← Matrix.mul_assoc f.matrix F.differential, ← f.commute]
    simp only [Matrix.mul_assoc]
  · simp only [Matrix.mul_assoc]
    rw [g.commute]

end Map

namespace HomotopyEquivalence

noncomputable def refl (E : BasedComplex Q (K := K) I) : HomotopyEquivalence Q E E where
  forward := Map.identity Q E
  backward := Map.identity Q E
  sourceHomotopy := 0
  targetHomotopy := 0
  sourceEntries := projectiveEntries_zero Q
  targetEntries := projectiveEntries_zero Q
  sourceDegree := mapDegree_zero Q (-1) 0
  targetDegree := mapDegree_zero Q (-1) 0
  sourceEquation := by
    change projectiveIdentity Q E.placement * projectiveIdentity Q E.placement = _
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
    exact projectiveIdentity_mul Q (projectiveEntries_identity Q)
  targetEquation := by
    change projectiveIdentity Q E.placement * projectiveIdentity Q E.placement = _
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
    exact projectiveIdentity_mul Q (projectiveEntries_identity Q)

noncomputable def trans (f : HomotopyEquivalence Q E F) (g : HomotopyEquivalence Q F G) :
    HomotopyEquivalence Q E G where
  forward := f.forward.comp Q g.forward
  backward := g.backward.comp Q f.backward
  sourceHomotopy := f.sourceHomotopy + f.forward.matrix * g.sourceHomotopy * f.backward.matrix
  targetHomotopy := g.targetHomotopy + g.backward.matrix * f.targetHomotopy * g.forward.matrix
  sourceEntries := projectiveEntries_add Q f.sourceEntries
    (projectiveEntries_mul Q (projectiveEntries_mul Q f.forward.entries g.sourceEntries)
      f.backward.entries)
  targetEntries := projectiveEntries_add Q g.targetEntries
    (projectiveEntries_mul Q (projectiveEntries_mul Q g.backward.entries f.targetEntries)
      g.forward.entries)
  sourceDegree := by
    have h := mapDegree_mul Q (mapDegree_mul Q f.forward.degree g.sourceDegree) f.backward.degree
    norm_num at h
    exact mapDegree_add Q f.sourceDegree h
  targetDegree := by
    have h := mapDegree_mul Q (mapDegree_mul Q g.backward.degree f.targetDegree) g.forward.degree
    norm_num at h
    exact mapDegree_add Q g.targetDegree h
  sourceEquation := by
    change (f.forward.matrix * g.forward.matrix) * (g.backward.matrix * f.backward.matrix) = _
    calc
      _ = f.forward.matrix * (g.forward.matrix * g.backward.matrix) * f.backward.matrix := by
        simp only [Matrix.mul_assoc]
      _ = f.forward.matrix * (projectiveIdentity Q F.placement +
          (F.differential * g.sourceHomotopy + g.sourceHomotopy * F.differential)) *
          f.backward.matrix := by rw [g.sourceEquation]
      _ = f.forward.matrix * f.backward.matrix + f.forward.matrix *
          (F.differential * g.sourceHomotopy + g.sourceHomotopy * F.differential) *
          f.backward.matrix := by
        rw [Matrix.mul_add, Matrix.add_mul]
        exact congrArg (fun M => M * f.backward.matrix +
          f.forward.matrix * (F.differential * g.sourceHomotopy +
            g.sourceHomotopy * F.differential) * f.backward.matrix)
          (mul_projectiveIdentity Q f.forward.entries)
      _ = _ := by
        rw [f.sourceEquation, Map.conjugateBoundary Q f.forward f.backward]
        simp only [Matrix.mul_add, Matrix.add_mul]
        abel
  targetEquation := by
    change (g.backward.matrix * f.backward.matrix) * (f.forward.matrix * g.forward.matrix) = _
    calc
      _ = g.backward.matrix * (f.backward.matrix * f.forward.matrix) * g.forward.matrix := by
        simp only [Matrix.mul_assoc]
      _ = g.backward.matrix * (projectiveIdentity Q F.placement +
          (F.differential * f.targetHomotopy + f.targetHomotopy * F.differential)) *
          g.forward.matrix := by rw [f.targetEquation]
      _ = g.backward.matrix * g.forward.matrix + g.backward.matrix *
          (F.differential * f.targetHomotopy + f.targetHomotopy * F.differential) *
          g.forward.matrix := by
        rw [Matrix.mul_add, Matrix.add_mul]
        exact congrArg (fun M => M * g.forward.matrix +
          g.backward.matrix * (F.differential * f.targetHomotopy +
            f.targetHomotopy * F.differential) * g.forward.matrix)
          (mul_projectiveIdentity Q g.backward.entries)
      _ = _ := by
        rw [g.targetEquation, Map.conjugateBoundary Q g.backward g.forward]
        simp only [Matrix.mul_add, Matrix.add_mul]
        abel

end HomotopyEquivalence

structure FiniteModel where
  Index : Type u
  fintype : Fintype Index
  decidableEq : DecidableEq Index
  complex : @BasedComplex V A K Q _ _ _ Index fintype

attribute [instance] FiniteModel.fintype FiniteModel.decidableEq

namespace FiniteModel

noncomputable def ofComplex {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K := K) I) : FiniteModel.{u} Q (K := K) where
  Index := I
  fintype := inferInstance
  decidableEq := inferInstance
  complex := E

theorem exists_minimal (E : FiniteModel.{u} Q (K := K)) :
    ∃ F : FiniteModel.{u} Q (K := K), F.complex.IsMinimal Q ∧
      Nonempty (HomotopyEquivalence Q E.complex F.complex) := by
  have h : ∀ n (B : FiniteModel.{u} Q (K := K)), Fintype.card B.Index = n →
      ∃ F : FiniteModel.{u} Q (K := K), F.complex.IsMinimal Q ∧
        Nonempty (HomotopyEquivalence Q B.complex F.complex) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro B hn
      by_cases hm : B.complex.IsMinimal Q
      · exact ⟨B, hm, ⟨HomotopyEquivalence.refl Q B.complex⟩⟩
      · obtain ⟨p⟩ := scalarPivot_of_not_minimal Q B.complex hm
        let C := ofComplex Q (p.reduced Q)
        have hc : Fintype.card C.Index < n := by
          dsimp only [C, ofComplex]
          rw [← hn]
          exact p.retained_card_lt Q
        obtain ⟨F, hF, ⟨e⟩⟩ := ih (Fintype.card C.Index) hc C rfl
        exact ⟨F, hF, ⟨(p.reductionEquivalence Q).trans Q e⟩⟩
  exact h (Fintype.card E.Index) E rfl

end FiniteModel
end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
