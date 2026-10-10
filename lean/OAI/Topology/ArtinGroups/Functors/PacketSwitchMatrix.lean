import Mathlib
import OAI.Topology.ArtinGroups.Functors.HomSwitchMap
import OAI.Topology.ArtinGroups.Functors.LeftPacketIndex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
attribute [local instance] Classical.propDecidable
variable {V B J K T : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)
local notation "U" => Q.stringQuiver step hstep N hN
local notation "F" => linearMap Q step hstep N hN orient μ A

noncomputable def packetSwitchMatrix [DecidableEq T]
    (p : T → GeneratorPlacement (V × J)) (u:V) :
    Matrix (LeftPacketIndex Q step hstep N hN p u)
      (RightPacketIndex Q step hstep N hN p u) (Zigzag U K) :=
  Matrix.blockDiagonal' (fun c => Zigzag.scalarCornerMatrix U (u,c)
    (homSwitch Q step hstep N hN orient μ A p u c))

lemma switch_evaluation (u t : V) (b c : J)
    (x : LeftPaths Q step hstep N hN u t b c) (d : {d:J // N b d}) :
    (∑ y : RightPaths Q step hstep N hN u t b c,
      (evaluationMatrix Q step hstep N hN orient μ A u t b c x y • Zigzag.vertexId U (u,c)) *
        (if y.1=d then Zigzag.pathBasis U y.2.val else 0)) =
      F (Zigzag.pathBasis U x.2.val) (evaluationSource N u c x.1) (evaluationTarget N t b d) := by
  rw [Fintype.sum_sigma,Finset.sum_eq_single d]
  · simp only [ite_true,smul_mul_assoc,Zigzag.cornerPath_left]
    exact Zigzag.sum_cornerPath U
      (F (Zigzag.pathBasis U x.2.val) (evaluationSource N u c x.1) (evaluationTarget N t b d))
      (linearMap_left Q step hstep N hN orient μ A (Zigzag.pathBasis U x.2.val)
        (evaluationSource N u c x.1) (evaluationTarget N t b d))
      (linearMap_right Q step hstep N hN orient μ A (Zigzag.pathBasis U x.2.val)
        (evaluationSource N u c x.1) (evaluationTarget N t b d))
  · intro e he hed
    apply Finset.sum_eq_zero
    intro z hz
    simp only [ite_eq_right hed,mul_zero]
  · simp

section Comparison
variable [Fintype T] [DecidableEq T]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "L" => leftHomComplex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "R" => rightHomComplex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

noncomputable def packetComparison (E : Zigzag.BasedComplex U (K := K) T) (u:V) :
    Zigzag.BasedComplex.ChainIsomorphism U
      ((C (E.packetTest U (fun a:J => (u,a)))).reindex U
        (leftPacketEquiv Q step hstep N hN E.placement u))
      (((C E).packetTest U (fun a:J => (u,a))).reindex U
        (rightPacketEquiv Q step hstep N hN E.placement u)) := by
  let s := Zigzag.BasedComplex.ChainIsomorphism.finiteSum U
    (fun c => homComparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u c)
  have hL := congrArg Zigzag.BasedComplex.differential
    (leftPacketComplex_eq Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u)
  have hR := congrArg Zigzag.BasedComplex.differential
    (rightPacketComplex_eq Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u)
  exact {
    forward := {
      matrix := s.forward.matrix
      entries := s.forward.entries
      degree := s.forward.degree
      commute := by rw [hL,hR]; exact s.forward.commute }
    backward := {
      matrix := s.backward.matrix
      entries := s.backward.entries
      degree := s.backward.degree
      commute := by rw [hL,hR]; exact s.backward.commute }
    sourceEquation := s.sourceEquation
    targetEquation := s.targetEquation }

lemma packetEvaluation_right_entry (E : Zigzag.BasedComplex U (K := K) T) (u:V)
    (c:J) (i:T) (y : RightPaths Q step hstep N hN u (E.placement i).color.1 (E.placement i).color.2 c)
    (j:T) (d : {d:J // N (E.placement j).color.2 d}) :
    ((C E).packetEvaluationMatrix U (fun a:J => (u,a))).submatrix
      (rightPacketEquiv Q step hstep N hN E.placement u) id ⟨c,⟨i,y⟩⟩ ⟨j,d⟩ =
      if (⟨i,y.1⟩ : Index N E.placement) = ⟨j,d⟩ then Zigzag.pathBasis U y.2.val else 0 := by
  dsimp only [Matrix.submatrix,rightPacketEquiv,rightHomEquiv,Equiv.coe_fn_mk,
    Zigzag.BasedComplex.packetEvaluationMatrix,Zigzag.evaluationMatrix]
  simp only [Matrix.of_apply]
  split_ifs <;> first | rfl | contradiction

lemma packetEvaluation_left_entry (E : Zigzag.BasedComplex U (K := K) T) (u:V)
    (c:J) (i:T) (x : LeftPaths Q step hstep N hN u (E.placement i).color.1 (E.placement i).color.2 c)
    (j:T) (d : {d:J // N (E.placement j).color.2 d}) :
    (matrix Q step hstep N hN orient μ A
      (E.packetTest U (fun a:J => (u,a))).placement E.placement
      (E.packetEvaluationMatrix U (fun a:J => (u,a)))).submatrix
      (leftPacketEquiv Q step hstep N hN E.placement u) id ⟨c,⟨i,x⟩⟩ ⟨j,d⟩ =
      F (if i=j then Zigzag.pathBasis U x.2.val else 0)
        (evaluationSource N u c x.1) (evaluationTarget N (E.placement j).color.1 (E.placement j).color.2 d) := by
  dsimp only [Matrix.submatrix,leftPacketEquiv,Equiv.coe_fn_mk,matrix,indexEmbed,
    Zigzag.BasedComplex.packetEvaluationMatrix, Zigzag.evaluationMatrix,
    Zigzag.BasedComplex.packetTest,Zigzag.packetPlacement,Zigzag.testPlacement,
    evaluationSource,evaluationTarget]
  simp only [Matrix.of_apply]
  split_ifs <;> first | rfl | contradiction

lemma packetEvaluation_comparison (E : Zigzag.BasedComplex U (K := K) T) (u:V) :
    packetSwitchMatrix Q step hstep N hN orient μ A E.placement u *
      ((C E).packetEvaluationMatrix U (fun a:J => (u,a))).submatrix
        (rightPacketEquiv Q step hstep N hN E.placement u) id =
    (matrix Q step hstep N hN orient μ A
      (E.packetTest U (fun a:J => (u,a))).placement E.placement
      (E.packetEvaluationMatrix U (fun a:J => (u,a)))).submatrix
        (leftPacketEquiv Q step hstep N hN E.placement u) id := by
  apply Matrix.ext
  rintro ⟨c,i,a,x⟩ ⟨j,d⟩
  rw [packetSwitchMatrix,Matrix.blockDiagonal'_mul_entry,Fintype.sum_sigma,Finset.sum_eq_single i]
  · simp only [Zigzag.scalarCornerMatrix,homSwitch,Matrix.blockDiagonal'_apply_eq]
    simp only [packetEvaluation_right_entry,packetEvaluation_left_entry]
    by_cases hij : i=j
    · subst j
      simp only [Sigma.mk.inj_iff,heq_eq_eq,true_and,ite_true]
      exact switch_evaluation Q step hstep N hN orient μ A _ _ _ _ _ _
    · simp only [ite_eq_right hij,map_zero,Matrix.zero_apply]
      apply Finset.sum_eq_zero
      intro y hy
      have he : (⟨i,y.1⟩ : Index N E.placement) ≠ ⟨j,d⟩ := fun h => hij (congrArg Sigma.fst h)
      rw [ite_eq_right he,mul_zero]
  · intro k hk hki
    apply Finset.sum_eq_zero
    intro y hy
    simp only [Zigzag.scalarCornerMatrix,homSwitch,Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hki),
      zero_smul,zero_mul]
  · simp

end Comparison
end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
