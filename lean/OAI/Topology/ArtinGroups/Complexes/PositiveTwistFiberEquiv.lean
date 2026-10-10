import Mathlib
import OAI.Topology.ArtinGroups.Quivers.VertexMinimal

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def positiveTwistFiberEquiv (E : BasedComplex Q (K := K) I)
    (α : V) (a : GeneratorPlacement V) (hα : α ≠ a.color) :
    {i // E.placement i = a} ≃ {i // (E.positiveTwist Q α).placement i = a} :=
  Equiv.ofBijective (fun i => ⟨Sum.inr i.val, i.property⟩) (by
    constructor
    · intro i j h
      exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))
    · intro i
      rcases i with ⟨i | i, hi⟩
      · exact (hα (congrArg GeneratorPlacement.color hi)).elim
      · exact ⟨⟨i, hi⟩, rfl⟩)

noncomputable def negativeTwistFiberEquiv (E : BasedComplex Q (K := K) I)
    (α : V) (a : GeneratorPlacement V) (hα : α ≠ a.color) :
    {i // E.placement i = a} ≃ {i // (E.negativeTwist Q α).placement i = a} :=
  Equiv.ofBijective (fun i => ⟨Sum.inl i.val, i.property⟩) (by
    constructor
    · intro i j h
      exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
    · intro i
      rcases i with ⟨i | i, hi⟩
      · exact ⟨⟨i, hi⟩, rfl⟩
      · exact (hα (congrArg GeneratorPlacement.color hi)).elim)

theorem positiveTwist_exterior_multiplicity (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (α : V) (e : HomotopyEquivalence Q (E.positiveTwist Q α) F)
    (a : GeneratorPlacement V) (hα : α ≠ a.color) :
    F.multiplicity Q a = E.multiplicity Q a := by
  calc
    F.multiplicity Q a = (E.positiveTwist Q α).multiplicity Q a :=
      (multiplicity_eq_of_vertex_homotopyEquivalence Q _ _ e a
        (positiveTwist_vertexMinimal Q E hE α a.color hα)
        (fun i j => congrFun (hF i j) a.color)).symm
    _ = E.multiplicity Q a := Nat.card_congr (positiveTwistFiberEquiv Q E α a hα).symm

theorem negativeTwist_exterior_multiplicity (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (α : V) (e : HomotopyEquivalence Q (E.negativeTwist Q α) F)
    (a : GeneratorPlacement V) (hα : α ≠ a.color) :
    F.multiplicity Q a = E.multiplicity Q a := by
  calc
    F.multiplicity Q a = (E.negativeTwist Q α).multiplicity Q a :=
      (multiplicity_eq_of_vertex_homotopyEquivalence Q _ _ e a
        (negativeTwist_vertexMinimal Q E hE α a.color hα)
        (fun i j => congrFun (hF i j) a.color)).symm
    _ = E.multiplicity Q a := Nat.card_congr (negativeTwistFiberEquiv Q E α a hα).symm

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
