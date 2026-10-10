import Mathlib
import OAI.Topology.ArtinGroups.Quivers.TestPlacement
import OAI.Topology.ArtinGroups.Complexes.ConePlacement

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq J]

abbrev PacketIndex (p : I → GeneratorPlacement V) (v : J → V) :=
  (a : J) × TestIndex Q p (v a)

def packetPlacement (p : I → GeneratorPlacement V) (v : J → V) :
    PacketIndex Q p v → GeneratorPlacement V :=
  fun x => testPlacement Q p (v x.1) x.2

noncomputable def packetDifferential (p : I → GeneratorPlacement V) (v : J → V)
    (M : Matrix I I (Zigzag Q K)) :
    Matrix (PacketIndex Q p v) (PacketIndex Q p v) (Zigzag Q K) :=
  Matrix.blockDiagonal' (fun a => scalarCornerMatrix Q (v a) (testMatrix Q p p (v a) M))

omit [DecidableEq A] [Fintype I] [Fintype J] in
lemma packet_entries (p : I → GeneratorPlacement V) (v : J → V)
    (M : Matrix I I (Zigzag Q K)) :
    ProjectiveEntries Q (packetPlacement Q p v) (packetPlacement Q p v)
      (packetDifferential Q p v M) := by
  constructor
  · rintro ⟨a,x⟩ ⟨b,y⟩
    by_cases h : a=b
    · subst b
      rw [packetDifferential,Matrix.blockDiagonal'_apply_eq]
      exact (scalarCornerMatrix_entries Q (v a) (testPlacement Q p (v a)) (testPlacement Q p (v a)) (fun _ => rfl) (fun _ => rfl) _).1 x y
    · rw [packetDifferential,Matrix.blockDiagonal'_apply_ne _ _ _ h,mul_zero]
  · rintro ⟨a,x⟩ ⟨b,y⟩
    by_cases h : a=b
    · subst b
      rw [packetDifferential,Matrix.blockDiagonal'_apply_eq]
      exact (scalarCornerMatrix_entries Q (v a) (testPlacement Q p (v a)) (testPlacement Q p (v a)) (fun _ => rfl) (fun _ => rfl) _).2 x y
    · rw [packetDifferential,Matrix.blockDiagonal'_apply_ne _ _ _ h,zero_mul]

omit [Fintype I] [Fintype J] in
lemma packet_degree (p : I → GeneratorPlacement V) (v : J → V)
    (M : Matrix I I (Zigzag Q K)) (hM : MapDegree Q p p 1 0 M) :
    MapDegree Q (packetPlacement Q p v) (packetPlacement Q p v) 1 0
      (packetDifferential Q p v M) := by
  rintro ⟨a,x⟩ ⟨b,y⟩
  by_cases h : a=b
  · subst b
    rw [packetDifferential,Matrix.blockDiagonal'_apply_eq]
    exact testMatrix_degree Q (v a) hM x y
  · rw [packetDifferential,Matrix.blockDiagonal'_apply_ne _ _ _ h]
    exact ⟨fun _ => rfl,homogeneous_zero Q _⟩

namespace BasedComplex

noncomputable def packetTest (E : BasedComplex Q (K := K) I) (v : J → V) :
    BasedComplex Q (K := K) (PacketIndex Q E.placement v) where
  placement := packetPlacement Q E.placement v
  differential := packetDifferential Q E.placement v E.differential
  entries := packet_entries Q E.placement v E.differential
  degree := packet_degree Q E.placement v E.differential E.degree
  square_zero := by
    simp only [packetDifferential,← Matrix.blockDiagonal'_mul]
    have h : (fun a => scalarCornerMatrix Q (v a) (testMatrix Q E.placement E.placement (v a) E.differential) *
        scalarCornerMatrix Q (v a) (testMatrix Q E.placement E.placement (v a) E.differential)) = 0 := by
      funext a
      exact (E.testComplex Q (v a)).square_zero
    rw [h,Matrix.blockDiagonal'_zero]

noncomputable def packetEvaluationMatrix (E : BasedComplex Q (K := K) I) (v : J → V) :
    Matrix (PacketIndex Q E.placement v) I (Zigzag Q K) :=
  fun x i => evaluationMatrix Q E.placement (v x.1) x.2 i

lemma packetEvaluation_commute (E : BasedComplex Q (K := K) I) (v : J → V) :
    (E.packetTest Q v).differential * E.packetEvaluationMatrix Q v =
      E.packetEvaluationMatrix Q v * E.differential := by
  apply Matrix.ext
  rintro ⟨a,x⟩ i
  change (∑ y, packetDifferential Q E.placement v E.differential ⟨a,x⟩ y *
      packetEvaluationMatrix Q E v y i) = _
  rw [Fintype.sum_sigma,Finset.sum_eq_single a]
  · simp only [packetDifferential,Matrix.blockDiagonal'_apply_eq,packetEvaluationMatrix]
    exact congrFun (congrFun (E.evaluation Q (v a)).commute x) i
  · intro b hb hba
    apply Finset.sum_eq_zero
    intro y hy
    rw [packetDifferential,Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hba),zero_mul]
  · simp

noncomputable def packetEvaluation (E : BasedComplex Q (K := K) I) (v : J → V) :
    Map Q (E.packetTest Q v) E where
  matrix := E.packetEvaluationMatrix Q v
  entries := ⟨fun x i => (evaluation_entries Q E.placement (v x.1)).1 x.2 i,
    fun x i => (evaluation_entries Q E.placement (v x.1)).2 x.2 i⟩
  degree := fun x i => evaluation_degree Q E.placement (v x.1) x.2 i
  commute := E.packetEvaluation_commute Q v

noncomputable def packetTwist (E : BasedComplex Q (K := K) I) (v : J → V) :
    BasedComplex Q (K := K) (PacketIndex Q E.placement v ⊕ I) :=
  (E.packetEvaluation Q v).cone Q

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
