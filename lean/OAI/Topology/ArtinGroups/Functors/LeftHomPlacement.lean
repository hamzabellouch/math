import Mathlib
import OAI.Topology.ArtinGroups.Functors.LeftHomIndex
import OAI.Topology.ArtinGroups.Quivers.ScalarCornerMatrixDegree

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
variable {V B J K T : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

local notation "U" => Q.stringQuiver step hstep N hN

def leftHomPlacement (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    LeftHomIndex Q step hstep N hN p u c → GeneratorPlacement (V × J) :=
  fun x => ⟨(u,c),(p x.1).cochain,(p x.1).internal + Path.length x.2.2.val⟩

def rightHomEquiv (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    RightHomIndex Q step hstep N hN p u c ≃ Zigzag.TestIndex U (placement N p) (u,c) where
  toFun x := ⟨⟨x.1,x.2.1⟩,x.2.2⟩
  invFun x := ⟨x.1.1,⟨x.1.2,x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def rightHomPlacement (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    RightHomIndex Q step hstep N hN p u c → GeneratorPlacement (V × J) :=
  Zigzag.testPlacement U (placement N p) (u,c) ∘ rightHomEquiv Q step hstep N hN p u c

lemma rightHomMatrix_eq (p : T → GeneratorPlacement (V × J)) (u:V) (c:J)
    (M : Matrix T T (Zigzag U K)) :
    rightHomMatrix Q step hstep N hN orient μ A p p u c M =
      (Zigzag.testMatrix U (placement N p) (placement N p) (u,c)
        (matrix Q step hstep N hN orient μ A p p M)).submatrix
          (rightHomEquiv Q step hstep N hN p u c) (rightHomEquiv Q step hstep N hN p u c) := rfl

lemma leftHom_degree (p : T → GeneratorPlacement (V × J)) (u:V) (c:J)
    (M : Matrix T T (Zigzag U K)) (hM : Zigzag.MapDegree U p p 1 0 M) :
    Zigzag.MapDegree U (leftHomPlacement Q step hstep N hN p u c)
      (leftHomPlacement Q step hstep N hN p u c) 1 0
      (Zigzag.scalarCornerMatrix U (u,c) (leftHomMatrix Q step hstep N hN p p u c M)) := by
  apply Zigzag.scalarCornerMatrix_degree
  · rintro ⟨i,a,x⟩ ⟨j,b,y⟩ h
    change (p j).cochain = (p i).cochain+1
    by_contra hn
    apply h
    simp only [leftHomMatrix,(hM i j).1 hn,mul_zero,Zigzag.coordinates_zero,ite_self]
  · rintro ⟨i,a,x⟩ ⟨j,b,y⟩ h
    have hz : Zigzag.pathCoordinates U (Zigzag.pathBasis U x.val * M i j) y.val ≠ 0 := by
      intro hz
      apply h
      simp only [leftHomMatrix,hz,ite_self]
    have he := Zigzag.coordinates_mul_degree U (Zigzag.pathBasis_homogeneous U x.val)
      (hM i j).2 hz
    change (p j).internal+Path.length y.val=(p i).internal+Path.length x.val+0
    omega

section Complex
variable [Fintype T] [DecidableEq T]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)

local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

noncomputable def rightHomComplex (E : Zigzag.BasedComplex U (K := K) T) (u:V) (c:J) :
    Zigzag.BasedComplex U (K := K) (RightHomIndex Q step hstep N hN E.placement u c) :=
  ((C E).testComplex U (u,c)).reindex U (rightHomEquiv Q step hstep N hN E.placement u c)

include ho hμ hA hroot hPF in
omit [DecidableEq T] in
lemma rightHomMatrix_square (E : Zigzag.BasedComplex U (K := K) T) (u:V) (c:J) :
    rightHomMatrix Q step hstep N hN orient μ A E.placement E.placement u c E.differential *
      rightHomMatrix Q step hstep N hN orient μ A E.placement E.placement u c E.differential = 0 := by
  simp only [rightHomMatrix_eq]
  rw [Matrix.submatrix_mul_equiv]
  change (Zigzag.testMatrix U (C E).placement (C E).placement (u,c) (C E).differential *
    Zigzag.testMatrix U (C E).placement (C E).placement (u,c) (C E).differential).submatrix _ _ = 0
  rw [Zigzag.testMatrix_mul U (u,c) _ (C E).entries]
  change (Zigzag.testMatrix U _ _ (u,c) ((C E).differential * (C E).differential)).submatrix _ _ = 0
  rw [(C E).square_zero,Zigzag.testMatrix_zero]
  rfl

include ho hμ hA hroot hPF in
lemma leftHomMatrix_square (E : Zigzag.BasedComplex U (K := K) T) (u:V) (c:J) :
    leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential *
      leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential = 0 := by
  classical
  let L := leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential
  let R := rightHomMatrix Q step hstep N hN orient μ A E.placement E.placement u c E.differential
  let S := homSwitch Q step hstep N hN orient μ A E.placement u c
  let D := homUnswitch Q step hstep N hN orient μ A E.placement u c
  have hSD : S*D=1 := homSwitch_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF _ _ _
  have hLS : L*S=S*R := homSwitch_naturality Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ E.entries
  have hRR : R*R=0 := rightHomMatrix_square Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u c
  change L*L=0
  calc
    L*L = L*L*(S*D) := by rw [hSD,Matrix.mul_one]
    _ = L*((L*S)*D) := by simp only [Matrix.mul_assoc]
    _ = L*((S*R)*D) := by rw [hLS]
    _ = (L*S)*(R*D) := by simp only [Matrix.mul_assoc]
    _ = S*(R*R)*D := by rw [hLS]; simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hRR,Matrix.mul_zero,Matrix.zero_mul]

noncomputable def leftHomComplex (E : Zigzag.BasedComplex U (K := K) T) (u:V) (c:J) :
    Zigzag.BasedComplex U (K := K) (LeftHomIndex Q step hstep N hN E.placement u c) where
  placement := leftHomPlacement Q step hstep N hN E.placement u c
  differential := Zigzag.scalarCornerMatrix U (u,c) (leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential)
  entries := Zigzag.scalarCornerMatrix_entries U (u,c) _ _ (fun _ => rfl) (fun _ => rfl) _
  degree := leftHom_degree Q step hstep N hN _ _ _ _ E.degree
  square_zero := by
    rw [Zigzag.scalarCornerMatrix_mul,leftHomMatrix_square Q step hstep N hN orient μ A ho hμ δ hA hroot hPF,
      Zigzag.scalarCornerMatrix_zero]

end Complex
end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
