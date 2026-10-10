import Mathlib
import OAI.Topology.ArtinGroups.Functors.SectorInverse
import OAI.Topology.ArtinGroups.Functors.CoordinateExpansion
import OAI.Topology.ArtinGroups.Realizations.MulBlockDiagonal'Entry

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
variable {V B J K T R : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

local notation "U" => Q.stringQuiver step hstep N hN
local notation "F" => linearMap Q step hstep N hN orient μ A

abbrev LeftHomIndex (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :=
  (i:T) × LeftPaths Q step hstep N hN u (p i).color.1 (p i).color.2 c
abbrev RightHomIndex (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :=
  (i:T) × RightPaths Q step hstep N hN u (p i).color.1 (p i).color.2 c

noncomputable def leftHomMatrix (p : T → GeneratorPlacement (V × J))
    (q : R → GeneratorPlacement (V × J)) (u:V) (c:J)
    (M : Matrix T R (Zigzag U K)) :
    Matrix (LeftHomIndex Q step hstep N hN p u c) (LeftHomIndex Q step hstep N hN q u c) K :=
  fun x y => if x.2.1=y.2.1 then
    Zigzag.pathCoordinates U (Zigzag.pathBasis U x.2.2.val * M x.1 y.1) y.2.2.val else 0

noncomputable def rightHomMatrix (p : T → GeneratorPlacement (V × J))
    (q : R → GeneratorPlacement (V × J)) (u:V) (c:J)
    (M : Matrix T R (Zigzag U K)) :
    Matrix (RightHomIndex Q step hstep N hN p u c) (RightHomIndex Q step hstep N hN q u c) K :=
  fun x y => Zigzag.pathCoordinates U
    (Zigzag.pathBasis U x.2.2.val * F (M x.1 y.1)
      (evaluationTarget N (p x.1).color.1 (p x.1).color.2 x.2.1)
      (evaluationTarget N (q y.1).color.1 (q y.1).color.2 y.2.1)) y.2.2.val

noncomputable def homSwitch [DecidableEq T] (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    Matrix (LeftHomIndex Q step hstep N hN p u c) (RightHomIndex Q step hstep N hN p u c) K :=
  Matrix.blockDiagonal' (fun i => evaluationMatrix Q step hstep N hN orient μ A
    u (p i).color.1 (p i).color.2 c)

noncomputable def homUnswitch [DecidableEq T] (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    Matrix (RightHomIndex Q step hstep N hN p u c) (LeftHomIndex Q step hstep N hN p u c) K :=
  Matrix.blockDiagonal' (fun i => inverseEvaluationMatrix Q step hstep N hN orient μ A
    u (p i).color.1 (p i).color.2 c)

lemma homSwitch_inverse [Fintype T] [DecidableEq T]
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    homSwitch Q step hstep N hN orient μ A p u c *
      homUnswitch Q step hstep N hN orient μ A p u c = (by classical exact 1) := by
  classical
  unfold homSwitch homUnswitch
  rw [← Matrix.blockDiagonal'_mul]
  simp only [evaluationMatrix_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF]
  exact Matrix.blockDiagonal'_one

lemma homUnswitch_inverse [Fintype T] [DecidableEq T]
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    homUnswitch Q step hstep N hN orient μ A p u c *
      homSwitch Q step hstep N hN orient μ A p u c = (by classical exact 1) := by
  classical
  unfold homSwitch homUnswitch
  rw [← Matrix.blockDiagonal'_mul]
  simp only [inverseEvaluationMatrix_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF]
  exact Matrix.blockDiagonal'_one

lemma homSwitch_naturality [Fintype T] [Fintype R] [DecidableEq T] [DecidableEq R]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p : T → GeneratorPlacement (V × J)) (q : R → GeneratorPlacement (V × J))
    (u:V) (c:J) (M : Matrix T R (Zigzag U K)) (hM : Zigzag.ProjectiveEntries U p q M) :
    leftHomMatrix Q step hstep N hN p q u c M *
      homSwitch Q step hstep N hN orient μ A q u c =
    homSwitch Q step hstep N hN orient μ A p u c *
      rightHomMatrix Q step hstep N hN orient μ A p q u c M := by
  classical
  apply Matrix.ext
  rintro ⟨i,a,x⟩ ⟨j,d,w⟩
  simp only [homSwitch]
  rw [Matrix.mul_blockDiagonal'_entry,Matrix.blockDiagonal'_mul_entry]
  rw [Fintype.sum_sigma,Finset.sum_eq_single a]
  · simp only [leftHomMatrix,ite_true]
    rw [Fintype.sum_sigma]
    exact hom_naturality Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
      u (p i).color.1 (q j).color.1 a (p i).color.2 c (q j).color.2 a.property
      x (M i j) (hM.2 i j) (evaluationTarget N (q j).color.1 (q j).color.2 d) w.val
  · intro b hb hba
    apply Finset.sum_eq_zero
    intro z hz
    rw [leftHomMatrix,ite_eq_right (Ne.symm hba),zero_mul]
  · simp

lemma homUnswitch_naturality [Fintype T] [Fintype R] [DecidableEq T] [DecidableEq R]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p : T → GeneratorPlacement (V × J)) (q : R → GeneratorPlacement (V × J))
    (u:V) (c:J) (M : Matrix T R (Zigzag U K)) (hM : Zigzag.ProjectiveEntries U p q M) :
    rightHomMatrix Q step hstep N hN orient μ A p q u c M *
      homUnswitch Q step hstep N hN orient μ A q u c =
    homUnswitch Q step hstep N hN orient μ A p u c *
      leftHomMatrix Q step hstep N hN p q u c M := by
  classical
  let L := leftHomMatrix Q step hstep N hN p q u c M
  let R := rightHomMatrix Q step hstep N hN orient μ A p q u c M
  let Sp := homSwitch Q step hstep N hN orient μ A p u c
  let Sq := homSwitch Q step hstep N hN orient μ A q u c
  let Dp := homUnswitch Q step hstep N hN orient μ A p u c
  let Dq := homUnswitch Q step hstep N hN orient μ A q u c
  have hn : L*Sq=Sp*R := homSwitch_naturality Q step hstep N hN orient μ A ho hμ δ hA hroot hPF p q u c M hM
  have hDS : Dp*Sp=1 := homUnswitch_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF p u c
  have hSD : Sq*Dq=1 := homSwitch_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF q u c
  change R*Dq=Dp*L
  calc
    R*Dq = (Dp*Sp)*(R*Dq) := by rw [hDS,Matrix.one_mul]
    _ = Dp*(Sp*R)*Dq := by simp only [Matrix.mul_assoc]
    _ = Dp*(L*Sq)*Dq := by rw [← hn]
    _ = Dp*L*(Sq*Dq) := by simp only [Matrix.mul_assoc]
    _ = Dp*L := by rw [hSD,Matrix.mul_one]

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
