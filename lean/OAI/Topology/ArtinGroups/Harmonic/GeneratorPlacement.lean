import Mathlib
import OAI.Topology.ArtinGroups.Quivers.VertexHom

namespace OAI

namespace HarmonicArtin

structure GeneratorPlacement (V : Type*) where
  color : V
  cochain : ℤ
  internal : ℤ
  deriving DecidableEq

namespace ReversibleQuiver.Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

def Homogeneous (a : ℤ) (x : Q.Zigzag K) : Prop :=
  (a ≠ 0 → x.vertex = 0) ∧ (a ≠ 1 → x.arrow = 0) ∧ (a ≠ 2 → x.token = 0)

variable {I J L : Type*}

def ProjectiveEntries (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (M : Matrix I J (Q.Zigzag K)) : Prop :=
  (∀ i j, vertexId Q (p i).color * M i j = M i j) ∧
  (∀ i j, M i j * vertexId Q (q j).color = M i j)

def MapDegree (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (n v : ℤ) (M : Matrix I J (Q.Zigzag K)) : Prop :=
  ∀ i j, ((q j).cochain ≠ (p i).cochain + n → M i j = 0) ∧
    Homogeneous Q (v + (p i).internal - (q j).internal) (M i j)

def projectiveIdentity [DecidableEq I] (p : I → GeneratorPlacement V) :
    Matrix I I (Q.Zigzag K) := Matrix.diagonal fun i => vertexId Q (p i).color

omit [Fintype A] in
lemma vertexId_eval (v w : V) :
    (vertexId Q (K := K) v).vertex w = if w = v then 1 else 0 := by
  simp only [vertex_vertexId, Pi.single_apply]

lemma reduction_support {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {M : Matrix I J (Q.Zigzag K)} (hc : ProjectiveEntries Q p q M)
    (hd : MapDegree Q p q 0 0 M) (i : I) (j : J) (v : V)
    (hne : (M i j).vertex v ≠ 0) : p i = q j ∧ (p i).color = v := by
  have hleft := congrArg (fun x : Q.Zigzag K => x.vertex v) (hc.1 i j)
  have hright := congrArg (fun x : Q.Zigzag K => x.vertex v) (hc.2 i j)
  have hpv : (p i).color = v := by
    by_contra h
    have hh : v ≠ (p i).color := Ne.symm h
    change (vertexId Q (p i).color).vertex v * (M i j).vertex v = (M i j).vertex v at hleft
    rw [vertexId_eval, ite_eq_right hh] at hleft
    exact hne (hleft.symm.trans (MulZeroClass.zero_mul _))
  have hqv : (q j).color = v := by
    by_contra h
    have hh : v ≠ (q j).color := Ne.symm h
    change (M i j).vertex v * (vertexId Q (q j).color).vertex v = (M i j).vertex v at hright
    rw [vertexId_eval, ite_eq_right hh] at hright
    exact hne (hright.symm.trans (MulZeroClass.mul_zero _))
  have hcq : (q j).cochain = (p i).cochain := by
    by_contra h
    have hz := (hd i j).1 (by simpa only [add_zero] using h)
    exact hne (by simp [hz])
  have hiq : (p i).internal = (q j).internal := by
    by_contra h
    have hz := (hd i j).2.1 (by simpa only [zero_add, sub_ne_zero] using h)
    exact hne (by rw [hz]; rfl)
  exact ⟨by cases hp : p i; cases hq : q j; simp_all, hpv⟩

structure BasedComplex (I : Type*) [Fintype I] where
  placement : I → GeneratorPlacement V
  differential : Matrix I I (Q.Zigzag K)
  entries : ProjectiveEntries Q placement placement differential
  degree : MapDegree Q placement placement 1 0 differential
  square_zero : differential * differential = 0

namespace BasedComplex

variable [Fintype I] [Fintype J] [Fintype L]

def IsMinimal (E : BasedComplex Q (K := K) I) : Prop :=
  PositiveMatrix Q E.differential

structure Map (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) where
  matrix : Matrix I J (Q.Zigzag K)
  entries : ProjectiveEntries Q E.placement F.placement matrix
  degree : MapDegree Q E.placement F.placement 0 0 matrix
  commute : E.differential * matrix = matrix * F.differential

noncomputable def multiplicity (E : BasedComplex Q (K := K) I) (a : GeneratorPlacement V) : ℕ :=
  Nat.card {i : I // E.placement i = a}

end BasedComplex
end ReversibleQuiver.Zigzag
end HarmonicArtin

end OAI
